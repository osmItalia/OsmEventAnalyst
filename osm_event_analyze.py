#!/usr/bin/env python3
# -*- coding: utf-8 -*-
# (c) Copyright Luca Delucchi 2017
##################################################################
#
#  This code is licensed under the terms of GNU GPL 2.
#  This program is free software; you can redistribute it and/or
#  modify it under the terms of the GNU General Public License as
#  published by the Free Software Foundation; either version 2 of
#  the License, or (at your option) any later version.
#  This program is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
#  See the GNU General Public License for more details.
#
##################################################################
"""
Created on Thu Apr 20 08:21:23 2017

@author: lucadelu
"""

import tempfile
import os
import time
import lzma
import glob
import json
import multiprocessing as mltp
from datetime import datetime
from datetime import date
from collections import OrderedDict
from datetime import timedelta
import matplotlib.pyplot as plt
try:
    import psycopg2
except ImportError:
    raise ImportError("Please install psycopg2")
try:
    import numpy as np
except ImportError:
    raise ImportError("Please install numpy")
try:
    import requests
except ImportError:
    raise ImportError("Please install requests")
try:
    import geojson
except ImportError:
    raise ImportError("Please install geojson")
try:
    import mercantile
except ImportError:
    raise ImportError("Please install mercantile")


TABLES = ['planet_osm_line', 'planet_osm_point', 'planet_osm_polygon']
TIME_FORMAT = "%Y-%m-%dT%H:%M:%SZ"
TIME_FORMAT_NOZ = "%Y-%m-%dT%H:%M:%S"
LOGS_FORMAT = "%Y-%m-%d"
LOGS_FILE = "tiles-{day}.txt.xz"
NEISURL = "http://www.hdyc.neis-one.org/search/{user}"
NEIS_TIMEFORMAT = "%B %d{ext}, %Y"
NEIS_TIMEFORMAT2 = "%b %d{ext}, %Y"
LOCK = mltp.Lock()

def get_neiss_info(user):
    """Return a dictionary with the info from Neiss service"""
    http = requests.get(NEISURL.format(user=user))
    return http.json()


def convert_neissday(data):
    """Return a datetime object"""

    def date_extention(number):
        """return the right text for the date extention"""
        # exception for the first values
        if number in [11, 12, 13]:
            return 'th'
        last = number % 10
        if last == 1:
            return 'st'
        if last == 2:
            return 'nd'
        if last == 3:
            return 'rd'
        return 'th'

    day = int(data.split()[1][:2])
    suf = date_extention(day)
    try:
        return datetime.strptime(data, NEIS_TIMEFORMAT.format(ext=suf))
    except ValueError:
        try:
            return datetime.strptime(data, NEIS_TIMEFORMAT2.format(ext=suf))
        except ValueError:
            raise ValueError("Error in input format")


def set_area(area):
    """Return area variable using geojson input

    :param str area: the full path to a geojson file
    """
    if os.path.exists(area):
        try:
            f = open(area)
            myjson = geojson.load(f)
        except:
            print("The input file does not seem a geojson")
    else:
        print("The path {pa} does not exist".format(pa=area))
    try:
        return myjson['geometry']
    except:
        try:
            feats = myjson['features']
            if len(feats) == 1:
                return myjson['features'][0]['geometry']
            else:
                print("The geoJSON file is not valid, only geoJSON with one"
                      "feature are accepted")
        except:
            print("The input file does not seem a geojson")
            return None


def get_extent(area):
    """Return the bounding box of a geometry

    :param str area: the full path to a geojson file
    """
    # set opposite max/min values to get first value assigned
    minx = 180
    maxx = -180
    miny = 90
    maxy = -90
    geom = set_area(area)
    # for each polygon
    for poly in geom['coordinates']:
        # for each node of polygon
        for coord in poly:
            # check min longitude
            if coord[0] < minx:
                minx = coord[0]
            # check max longitude
            if coord[0] > maxx:
                maxx = coord[0]
            # check min latitude
            if coord[1] < miny:
                miny = coord[1]
            # check max latitude
            if coord[1] > maxy:
                maxy = coord[1]
    return minx, miny, maxx, maxy


def urljoin(*args):
    """Joins given arguments into a url. Trailing but not leading slashes are
    stripped for each argument.
    http://stackoverflow.com/a/11326230

    :return: a string
    """
    return "/".join([str(x).rstrip('/') for x in args])


def write_output(path, data):
    """Write dictionary to a json file"""
    if len(data) == 0:
        print("It seems that analysis for user was not run")
    else:
        with open(path, 'w') as f:
            f.write(json.dumps(data, sort_keys=True,
                               indent=4, cls=JsonOsmEncoder))
        f.close()

def reduce_labels(labels, step):
    """Function to manage correctly the labels"""
    out = []
    x = 0
    for lab in labels:
        if x == 0 or x % step == 0:
            out.append(lab)
        x += 1
    return out


class JsonOsmEncoder(json.JSONEncoder):
    """Class to convert correctly datetime object to json"""
    def default(self, obj):
        if isinstance(obj, (date, datetime)):
            return obj.isoformat()
        elif isinstance(obj, (np.int64, np.int32)):
            return int(obj)
        elif isinstance(obj, (np.float64, np.float32)):
            return float(obj)
        else:
            return json.JSONEncoder.default(self, obj)


class OsmDataEventAnalyze():
    """Class to analyze OpenStreetMap history data"""

    def __init__(self, dbconn, eventdate, area=None):
        # start connection with postgresql database
        self.conn = psycopg2.connect(dbconn)
        # parse datetime string
        self.eventdate = datetime.strptime(eventdate, TIME_FORMAT)
        self.users = {}
        # initialize the area variable
        self.area = None
        if area:
            self.area = set_area(area)
        self.finalusers = {}
        self.finaldata = {}
        self.finalchanges = {'hourlyeditscount': {}, 'dailyusercount': {},
                             'dailyeditsclasses': {}}

    def _execute(self, query):
        """Execute a query and return the result

        :param str query: a string containing the query to execute
        """
        cursor = self.conn.cursor()
        # execute query
        cursor.execute(query)
        # return results
        return cursor.fetchall()

    def _point_in_area(self, point):
        """Return is a point is contained in the area

        :param str point: string containing a point in wkt format 'POINT(30 10)'
        """
        # check if a point is inside the area
        q = "SELECT ST_Contains(ST_GeomFromGeoJSON('{poly}')," \
            "ST_GeometryFromText('{point}'))".format(poly=self.area,
                                                     point=point)
        return self._execute(q)[0][0]

    def get_users(self):
        """Return the users for that area"""
        # for each table
        for tab in TABLES:
            # select distinct user
            users_query = "select distinct tags -> 'osm_user' from " \
                          "{ta}".format(ta=tab)
            tab_users = self._execute(users_query)
            for user in tab_users:
                # if user was not already added because existing in different
                # table add it has dictionary
                if user[0] not in self.users.keys():
                    self.users[user[0]] = {}
        return True

    def get_info(self):
        """Return a dictionary with users and starting/ending timestamp"""
        # for each user
        for user in self.users.keys():
            mind = None
            maxd = None
            count = 0
            for tab in TABLES:
                # select min and max time of mapping in the area
                dates_query = "select min(tags -> 'osm_timestamp') as " \
                              "min_date, max(tags -> 'osm_timestamp') as " \
                              "max_date from {ta} where tags -> 'osm_user' " \
                              "= '{us}'".format(ta=tab, us=user)
                tab_dates = self._execute(dates_query)
                # if user doesn't exist in this table skip to next user
                if tab_dates[0][0] is None:
                    continue
                if not mind:
                    mind = datetime.strptime(tab_dates[0][0], TIME_FORMAT)
                    maxd = datetime.strptime(tab_dates[0][1], TIME_FORMAT)
                else:
                    # check min and max value
                    curmin = datetime.strptime(tab_dates[0][0], TIME_FORMAT)
                    curmax = datetime.strptime(tab_dates[0][1], TIME_FORMAT)
                    if curmin < mind:
                        mind = curmin
                    if curmax > maxd:
                        maxd = curmax
                # select count of edits for each user and sum to edits in
                # other table
                count_query = "select count(tags) from {ta} where tags -> " \
                              "'osm_user' = '{us}'".format(ta=tab, us=user)
                count += int(self._execute(count_query)[0][0])
            # add value to dictionary
            self.users[user]['min_time'] = mind
            self.users[user]['max_time'] = maxd
            self.users[user]['count'] = count
        return True

    def get_new_old_user(self):
        """Return three dictionary related to users:
           - existing users non mapping after event
           - existing users mapping after event
           - mapper new to that area
        """
        new = {}
        old = {}
        old_old = {}
        for k, v in self.users.items():
            if v['min_time'] < self.eventdate:
                if v['max_time'] < self.eventdate:
                    old_old[k] = v
                else:
                    old[k] = v
            else:
                new[k] = v
        # user already mapping the area but they stop to editing before event
        self.finalusers['old_user_mapping_only_before_event'] = old_old
        # user already mapping the area continuing after event
        self.finalusers['old_user_mapping_before_after_event'] = old
        return old_old, old, new

    def real_new_user(self, users):
        """Return if a user is a new user after event or if the user already
        mapped in different area
        """
        newout = {}
        newin = {}
        old = {}
        for k, v in users.items():
            info = get_neiss_info(k)
            since = convert_neissday(info['contributor']['since'])
            if since < self.eventdate:
                old[k] = v
            else:
                poi = "POINT({x} {y})".format(x=info['node']['f_lon'],
                                              y=info['node']['f_lat'])
                if self._point_in_area(poi):
                    newin[k] = v
                    newin[k]['neiss'] = info
                else:
                    newout[k] = v
                    newout[k]['neiss'] = info
        # existing user before event but starting to modify event area after
        self.finalusers['old_user_mapping_only_after_event'] = old
        # new user but first point is in a different area
        self.finalusers['new_user_first_point_other_area'] = newout
        # new user first point is in the case study area
        self.finalusers['new_user_first_point_this_area'] = newin
        return old, newout, newin

    def get_info_newuser(self, users):
        """Return info about new users"""
        info = {}
        for user, vals in users.items():
            info[user] = {}
            # get number mapping days
            mdays = 0
            mdayssplit = vals['neiss']['changesets']['mapping_days'].split(';')
            for d in mdayssplit:
                mdays += int(d.split('=')[1])
            info[user]['mdays'] = mdays
            info[user]['changes'] = int(vals['neiss']['changesets']['changes'])
            info[user]['tags'] = vals['neiss']['tags']
            tag = {}
            for k, v in info[user]['tags'].items():
                v = int(v)
                if len(tag.keys()) == 0:
                    tag[k] = v
                else:
                    if v > list(tag.values())[0]:
                        tag = {}
                        tag[k] = v
            info[user]['max_tag'] = tag
            # added new info
            self.finalusers['new_user_first_point_this_area'][user].update(info[user])
        return True

    def get_data(self, table):
        """Get data from a table"""
        self.finaldata[table] = {'new': {}, 'old': {}}
        old_query = "select distinct on (osm_id) osm_id, tags, way from " \
                    "(select osm_id, hstore_to_json(tags) as tags, st_astext" \
                    "(way) as way, tags -> 'osm_version' as version from " \
                    "{ta} where tags -> 'osm_timestamp' < '{da}') as data " \
                    "ORDER BY osm_id, version DESC;".format(da=self.eventdate,
                                                            ta=table)
        new_query = "select osm_id, hstore_to_json(tags) as tags, st_astext" \
                    "(way) as way from {ta} where tags -> 'osm_timestamp' >=" \
                    " '{da}' and tags -> 'osm_version' = '1';".format(da=self.eventdate,
                                                                      ta=table)
        mod_query = "select osm_id, hstore_to_json(tags) as tags, st_astext" \
                    "(way) as way from {ta} where tags -> 'osm_timestamp' >=" \
                    " '{da}' and tags -> 'osm_version' != '1';".format(da=self.eventdate,
                                                                       ta=table)
        count_query = "select count(osm_id) from {ta}".format(ta=table)
        countdata = self._execute(count_query)
        self.finaldata[table]['count'] = countdata[0][0]
        olddata = self._execute(old_query)
        newdata = self._execute(new_query)
        moddata = self._execute(mod_query)
        return olddata, newdata, moddata

    def compare_data(self, first, mod):
        """Compare first version of data and the modified one, it return a
        dictionary with several version of the same object
        """
        modids = [m[0] for m in mod]
        modids = list(set(modids))
        oldmod = {}
        for f in first:
            if f[0] in modids:
                oldmod[f[0]] = [f]
        for m in mod:
            if m[0] in oldmod.keys():
                oldmod[m[0]].append(m)
        return oldmod

    def _check_tags_values(self, tags0, tags1):
        """Check is tags value changed"""
        excluded_tags = ['osm_user', 'osm_timestamp', 'osm_uid',
                         'osm_changeset', 'osm_version']
        tags = list(set(tags0) - set(excluded_tags))
        out = []
        for tag in tags:
            try:
                if tags0[tag] != tags1[tag]:
                    out.append("{}->{}".format(tags0[tag], tags1[tag]))
            except KeyError:
                pass
        if len(out) == 0:
            return False
        else:
            return out

    def analyze_data(self, data, table=None, status=None):
        """Analyze data"""
        if table and not status:
            raise IOError("'table' option requires also 'status' option")
        elif table and status not in ['new', 'old']:
            raise IOError("'status' option should be 'new' or 'old'")
        out = {}
        for key, values in data.items():
            out[key] = {}
            diffgeom = False
            diffgeomcount = 0
            difftagskey = False
            difftagskeycount = 0
            diffvalues = {}
            for n in range(0, len(values) - 1):
                for m in range(1, len(values)):
                    if values[n][2] != values[m][2]:
                        diffgeom = True
                        diffgeomcount += 1
                    if values[n][1].keys() != values[m][1].keys():
                        difftagskey = True
                        difftagskeycount += 1
                    dvals = self._check_tags_values(values[n][1], values[m][1])
                    if dvals:
                        for dval in dvals:
                            if dval in diffvalues.keys():
                                if diffvalues[dval] > values[n][1]['osm_version']:
                                    diffvalues[dval] = values[n][1]['osm_version']
                            else:
                                diffvalues[dval] = values[n][1]['osm_version']
            out[key]['versions'] = len(values)
            out[key]['diffgeom'] = diffgeom
            out[key]['diffgeomcount'] = diffgeomcount
            out[key]['difftags'] = difftagskey
            out[key]['difftagscount'] = difftagskeycount
            out[key]['diffvalues'] = diffvalues
            if table and status:
                self.finaldata[table][status] = out
        return out

    def get_count_user_per_day(self, fday=None, lday=None):
        """Return the number of user modifing the area for each table"""
        fday = fday if fday is not None else self.eventdate.date()
        self.finalchanges['dailyusercount'][fday.strftime("%Y-%m-%d")] = {}
        query = "select mydate, count(myuser) from ("
        tqueries = []
        for tab in TABLES:
            tquery = "SELECT DISTINCT DATE(tags -> 'osm_timestamp') AS " \
                     "mydate, tags -> 'osm_user' AS myuser FROM {ta} " \
                     "where tags -> 'osm_timestamp' >= '{da}'".format(ta=tab,
                                                                      da=fday)
            if lday:
                tquery += " AND tags -> 'osm_timestamp' < " \
                          "'{da}'".format(da=lday)
            tqueries.append(tquery)
        query += ' UNION '.join(tqueries)
        query += ") as query group by mydate order by mydate;"
        data = self._execute(query)
        delta = timedelta(1)
        day = fday
        for d in data:
            while day <= d[0]:
                if day < d[0]:
                    self.finalchanges['dailyusercount'][fday.strftime("%Y-%m-%d")][day.strftime("%Y-%m-%d")] = 0
                else:
                    self.finalchanges['dailyusercount'][fday.strftime("%Y-%m-%d")][d[0].strftime("%Y-%m-%d")] = d[1]
                day = day + delta
        return True

    def get_count_edits_classes_per_day(self, fday=None, lday=None):
        """Return the number of edits for user class modifing the area
        for each table"""
        fday = fday if fday is not None else self.eventdate.date()
        daystr = fday.strftime("%Y-%m-%d")
        self.finalchanges['dailyeditsclasses'][daystr] = {}
        for k, v in self.finalusers.items():
            if k == 'old_user_mapping_only_before_event':
                continue
            query = "select mydate, count(osm_id) from ("
            tqueries = []
            self.finalchanges['dailyeditsclasses'][daystr][k] = {}
            users = "'{us}'".format(us="', '".join(list(v.keys())))
            for tab in TABLES:
                tqueries.append("select DATE(tags -> 'osm_timestamp') as " \
                                "mydate, osm_id from {ta} where tags -> " \
                                "'osm_user' in ({uss})".format(ta=tab,
                                                               uss=users))
            query += ' UNION '.join(tqueries)
            query += ") as query group by mydate order by mydate;"
            data = self._execute(query)
            delta = timedelta(1)
            day = fday
            for d in data:
                while day <= d[0]:
                    if day < d[0]:
                        self.finalchanges['dailyeditsclasses'][daystr][k][day.strftime("%Y-%m-%d")] = 0
                    else:
                        self.finalchanges['dailyeditsclasses'][daystr][k][d[0].strftime("%Y-%m-%d")] = d[1]
                    day = day + delta
        return True

    def get_count_edits_per_hour(self, day=None):
        """Return the number of changes in the area per hours"""
        day = day if day is not None else self.eventdate.strftime("%Y-%m-%d")
        self.finalchanges['hourlyeditscount'][day] = {}
        query = "select hour, sum(osmid) from ("
        tqueries = []
        for tab in TABLES:
            tqueries.append("select DISTINCT EXTRACT(hour from (tags -> " \
                            "'osm_timestamp')::timestamp) as hour, count(" \
                            "osm_id) as osmid from {ta} where (tags -> " \
                            "'osm_timestamp')::timestamp >= '{da}' and (tags" \
                            " -> 'osm_timestamp')::timestamp < ('{da}'::" \
                            "timestamp + '1 day'::interval) group by EXTRACT" \
                            "(hour from (tags -> 'osm_timestamp')::timestamp" \
                            ")".format(ta=tab, da=day))
        query += ' UNION '.join(tqueries)
        query += ") as query group by hour order by hour;"
        data = self._execute(query)
        hour = 0
        for d in data:
            while hour <= int(d[0]):
                if hour < int(d[0]):
                    self.finalchanges['hourlyeditscount'][day][hour] = 0
                else:
                    self.finalchanges['hourlyeditscount'][day][int(d[0])] = int(d[1])
                hour += 1
        while hour <= 23:
            self.finalchanges['hourlyeditscount'][day][hour] = 0
            hour += 1
        return True

    def output(self, userpath=None, datapath=None, changespath=None):
        """Write final result to json file"""
        if userpath:
            write_output(userpath, self.finalusers)
        if datapath:
            write_output(datapath, self.finaldata)
        if changespath:
            write_output(changespath, self.finalchanges)
        return True


class OsmDataEventPlot():
    """Class to get plots from OsmDataEventAnalize outputs"""
    def __init__(self, userdata=None, datadata=None, tilesdates=None,
                 tilestiles=None, changes=None):
        self.data_aggr = {}
        if isinstance(userdata, dict):
            self.userdata = userdata
        if isinstance(datadata, dict):
            self.datadata = datadata
            if self.datadata:
                self._aggregate_data()
        if isinstance(tilesdates, dict):
            self.tilesdates = tilesdate
        if isinstance(tilestiles, dict):
            self.tilestiles = tilestiles
        if isinstance(changes, dict):
            self.changes = changes

    def _aggregate_data(self):
        """Function to aggregate data"""
        for key, val in self.datadata.items():
            self.data_aggr[key] = {'new': {'diffgeom': list(),
                                   'diffgeomcount': list(),
                                   'difftags': list(),
                                   'difftagscount': list(),
                                   'versions': list(),
                                   },
                           'old': {'diffgeom': list(),
                                   'diffgeomcount': list(),
                                   'difftags': list(),
                                   'difftagscount': list(),
                                   'versions': list(),
                                   },
                           'count': self.datadata[key]['count']
                          }
            for v in val['new'].values():
                if 'diffgeom' in v.keys():
                    self.data_aggr[key]['new']['diffgeom'].append(1)
                    self.data_aggr[key]['new']['diffgeomcount'].append(v['diffgeomcount'])
                if 'difftags' in v.keys():
                    self.data_aggr[key]['new']['difftags'].append(1)
                    self.data_aggr[key]['new']['difftagscount'].append(v['difftagscount'])
                self.data_aggr[key]['new']['versions'].append(v['versions'])
            for v in val['old'].values():
                if 'diffgeom' in v.keys():
                    self.data_aggr[key]['old']['diffgeom'].append(1)
                    self.data_aggr[key]['old']['diffgeomcount'].append(v['diffgeomcount'])
                if 'difftags' in v.keys():
                    self.data_aggr[key]['old']['difftags'].append(1)
                    self.data_aggr[key]['old']['difftagscount'].append(v['difftagscount'])
                self.data_aggr[key]['old']['versions'].append(v['versions'])

    def set_userdata(self, path):
        """Load users' data from a json file"""
        f = open(path)
        self.userdata = json.loads(f.read())
        f.close()
        return True

    def set_datadata(self, path):
        """Load data data from a json file"""
        f = open(path)
        self.datadata = json.loads(f.read(), object_pairs_hook=OrderedDict)
        f.close()
        self._aggregate_data()
        return True

    def set_tilesdates(self, path):
        """Load tiles dates data from a json file"""
        f = open(path)
        self.tilesdates = json.loads(f.read(), object_pairs_hook=OrderedDict)
        f.close()
        return True

    def set_tilestiles(self, path):
        """Load tiles dates data from a json file"""
        f = open(path)
        self.tilestiles = json.loads(f.read())
        f.close()
        return True

    def set_changes(self, path):
        """Load changes data from a json file"""
        f = open(path)
        self.changes = json.loads(f.read(), object_pairs_hook=OrderedDict)
        f.close()
        return True

    def plot_oldnew_user(self, output=None):
        """Plot user distribution as a pie"""
        labels = []
        values = []
        for k, v in self.userdata.items():
            labels.append(k)
            values.append(len(v))
        fig1, ax1 = plt.subplots()
        ax1.pie(values, labels=labels, autopct='%1.1f%%', shadow=True)
        ax1.axis('equal')
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_oldnew_user_count_boxplot(self, output=None, outliers=None):
        """Plot number of edits for the user distribution in a boxplot"""
        labels = []
        values = []
        i = 0
        for k, v in self.userdata.items():
            labels.append(k)
            values.append(list())
            for z in v.values():
                values[i].append(z['count'])
            i += 1
        plt.figure()
        plt.boxplot(values, 0, outliers, labels=labels)
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_oldnew_user_count_lines(self, output=None):
        """Plot mean, max and sum number of edits for the user distribution"""
        labels = []
        values = []
        minn = []
        maxx = []
        mean = []
        summ = []
        x = []
        i = 0
        for k, v in self.userdata.items():
            x.append(i + 1)
            labels.append(k)
            values.append(list())
            for z in v.values():
                values[i].append(z['count'])
            minn.append(min(values[i]))
            maxx.append(max(values[i]))
            mean.append(sum(values[i]) / len(values[i]))
            summ.append(sum(values[i]))
            i += 1
        fig, ax = plt.subplots()
        linemin, = ax.plot(x, minn, '--', linewidth=2,
                           label='Min values')
        linemax, = ax.plot(x, maxx, '--', linewidth=2,
                           label='Max values')
        linemean, = ax.plot(x, mean, '--', linewidth=2,
                            label='mean values')
        linesum, = ax.plot(x, summ, '--', linewidth=2,
                           label='Sum values')
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_user_mapping_days(self, output=None, outliers=None):
        """Plot in a boxplot the number of day from the first edit in the event
        area to the last one"""
        labels = []
        values = []
        x = []
        i = 0
        for k, v in self.userdata.items():
            x.append(i + 1)
            labels.append(k)
            values.append(list())
            for z in v.values():
                fe = datetime.strptime(z['min_time'], TIME_FORMAT_NOZ)
                le = datetime.strptime(z['max_time'], TIME_FORMAT_NOZ)
                diff = le - fe
                values[i].append(diff.days + 1)
            i += 1
        plt.figure()
        plt.boxplot(values, 0, outliers, labels=labels)
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_data_changes_pie(self, output=None):
        """Plot the percentual of modified data in a pie"""
        labels = ['Old data modified', 'New data modified',
                  'Data not modified']
        fig, axis = plt.subplots(figsize=(8, 3), nrows=3)
        x = 0
        for key, val in self.data_aggr.items():
            values = []
            values.append(len(val['old']['versions']))
            values.append(len(val['new']['versions']))
            values.append(int(val['count']))
            axis[x].pie(values, labels=labels, autopct='%1.1f%%', shadow=True)
            axis[x].set_title(key.replace('_', ' '))
            axis[x].axis('equal')
            x += 1
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_geomtag_diff_histo(self, output=None):
        """Plot different between geometry and tags changes"""
        width = 0.5
        xs = range(len(self.datadata.keys()))
        x_label = []
        y_geomnew = []
        y_geomold = []
        y_tagsnew = []
        y_tagsold = []
        for key, val in self.datadata.items():
            x_label.append(key)
            y_geomnew.append(len(val['new']['diffgeom']))
            y_geomold.append(len(val['old']['diffgeom']))
            y_tagsnew.append(len(val['new']['difftags']))
            y_tagsold.append(len(val['old']['difftags']))
        fig, ax = plt.subplots()
        plot_geomold = ax.bar(xs, y_geomold, width, color='red')
        plot_geomnew = ax.bar(xs, y_geomnew, width, color='green')
        plot_tagsold = ax.bar(xs + width, y_tagsold, width, color='yellow')
        plot_tagsnew = ax.bar(xs + width, y_tagsnew, width, color='gray')
        ax.xticks(xs, x_label)
        if output:
            plt.savefig(output)
        else:
            plt.show()
            
    def plot_mean_diff_lines(self, output=None):
        """Plot mean value of number of changes for each element"""
        xs = range(len(self.datadata.keys()))
        x_label = []
        y_geomnew = []
        y_geomold = []
        y_tagsnew = []
        y_tagsold = []
        for key, val in self.datadata.items():
            x_label.append(key)
            values = np.array(list(v['new']['diffgeomcount']))
            y_geomnew.append(values.mean())
            values = np.array(list(v['new']['difftagscount']))
            y_tagsnew.append(values.mean())
            values = np.array(list(v['old']['diffgeomcount']))
            y_geomold.append(values.mean())
            values = np.array(list(v['old']['difftagscount']))
            y_tagsold.append(values.mean())
        fig, ax = plt.subplots()
        linemin, = ax.plot(x, minn, '--', linewidth=2,
                           label='Min values')
        linemax, = ax.plot(x, maxx, '--', linewidth=2,
                           label='Max values')
        linemean, = ax.plot(x, mean, '--', linewidth=2,
                            label='mean values')
        linesum, = ax.plot(x, summ, '--', linewidth=2,
                           label='Sum values')
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_tiles_avg_sum_dates(self, output=None):
        """Plot lines related to sum and mean of visited tiles"""
        x_values = range(len(self.tilesdates['sum']))
        xs = range(0, len(self.tilesdates['sum']), 3)
        x_labels = reduce_labels(list(self.tilesdates['sum'].keys()), 3)
        y_sum = list(self.tilesdates['sum'].values())
        y_avg = list(self.tilesdates['avg'].values())
        fig, axis = plt.subplots(figsize=(8, 3), ncols=2)
        line_sum = axis[0].plot(x_values, y_sum, linewidth=2)
        axis[0].set_title("The sum of visited tile for day")
        axis[0].set_xticks(xs)
        axis[0].set_xticklabels(x_labels, rotation='vertical')
        line_avg = axis[1].plot(x_values, y_avg, linewidth=2)
        axis[1].set_title("The mean of visited tile for day")
        axis[1].set_xticklabels(x_labels, rotation='vertical')
        axis[1].set_xticks(xs)
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_hourly_edit_count(self, output=None):
        """Plot daily data about number of edit per hour"""
        xs = range(24)
        fig, axis = plt.subplots(figsize=(8, 3),
                                 ncols=len(self.changes['hourlyeditscount']))
        plot = 0
        maxy = 0
        for v in self.changes['hourlyeditscount'].values():
            mxy = max(list(v.values()))
            if mxy > maxy:
                maxy = mxy
        for k, v in self.changes['hourlyeditscount'].items():
            axis[plot].plot(xs, list(v.values()), linewidth=2)
            axis[plot].set_title(k)
            axis[plot].set_xticks(xs)
            axis[plot].set_yticks(range(0, maxy, int(maxy / 10)))
            axis[plot].set_xticklabels(list(v.keys()))
            plot += 1
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_daily_user_count(self, output=None):
        """Plot data about number of user per day"""
        maxy = None
        if len(self.changes['dailyusercount']) == 0:
            print("No data loaded")
            return False
        elif len(self.changes['dailyusercount']) == 1:
            fig, axis = plt.subplots()
            for k, v in self.changes['dailyusercount'].items():
                xs = range(len(v.keys()))
                axis.plot(xs, list(v.values()), linewidth=2)
                axis.set_title(k)
                axis.set_xticks(range(0, len(v.keys()), 4))
                axis.set_xticklabels(reduce_labels(list(v.keys()), 4),
                                     rotation='vertical')
        elif len(self.changes['dailyusercount']) > 1:
            fig, axis = plt.subplots(figsize=(8, 3),
                                     ncols=len(self.changes['dailyusercount']))
            maxy = 0
            for k, v in self.changes['dailyusercount'].item():
                mxy = max(list(v.values()))
                if mxy > maxy:
                    maxy = mxy
            plot = 0
            for k, v in self.changes['dailyusercount'].items():
                xs = range(len(v.keys()))
                axis[plot].plot(xs, list(v.values()), linewidth=2)
                axis[plot].set_title(k)
                axis[plot].set_xticks(range(0, len(v.keys()), 4))
                axis[plot].set_yticks(range(0, maxy, int(maxy / 10)))
                axis[plot].set_xticklabels(reduce_labels(list(v.keys()), 4),
                                           rotation='vertical')
                plot += 1
        if output:
            plt.savefig(output)
        else:
            plt.show()

    def plot_daily_edits_classes(self, output=None):
        """Plot data about number of edits per user class"""
        if len(self.changes['dailyeditsclasses']) == 0:
            print("No data loaded")
            return False
        elif len(self.changes['dailyeditsclasses']) == 1:
            fig, axis = plt.subplots()
            for day, classes in self.changes['dailyeditsclasses'].items():
                for clas, values in classes.items():
                    x_values = range(len(values.keys()))
                    axis.plot(x_values, list(values.values()), '--',
                              linewidth=2, label=clas)
                axis.set_xticks(range(0, len(values.keys()), 4))
                axis.set_xticklabels(reduce_labels(list(values.keys()), 4),
                                     rotation='vertical')
                axis.legend(loc='right')
        if output:
            plt.savefig(output)
        else:
            plt.show()

class OsmTileLogEventAnalyze():
    """Class to analyze OpenStreetMap tiles log files"""

    def __init__(self, eventdate, area, workdir=None, timeout=30):
        self.url = 'http://planet.openstreetmap.org/tile_logs/'
        self.eventdate = datetime.strptime(eventdate, TIME_FORMAT)
        self.users = {}
        self.extent = get_extent(area)
        self.workdir = workdir if workdir is not None else tempfile.gettempdir()
        # timeout for HTTP connection before failing (seconds)
        self.timeout = timeout
        self.tiles = []
        self.files = []
        self.out = {'tiles': {}, 'dates': {}}
        self.out['dates'][self.eventdate.strftime(LOGS_FORMAT)] = {}
        self.multi = False
        self.final_dates = {'sum': {}, 'avg': {}, 'min': {}, 'max': {}}
        self.final_tiles = {'sum': {}, 'avg': {}, 'min': {}, 'max': {}}

    def _download_file(self, file):
        """Download a singolar XZ file"""
        orig_size = None
        fileurl = urljoin(self.url, file)
        filDir = os.path.join(self.workdir, file)
        filNoXZDir = filDir.replace('.xz', '')
        if os.path.exists(filDir):
            print("{} already exists".format(filDir))
            return True
        elif os.path.exists(filNoXZDir):
            print("{} already exists".format(filNoXZDir))
            return True
        filSave = open(filDir, "wb")
        http = requests.get(fileurl, timeout=self.timeout)
        orig_size = int(http.headers['Content-Length'])
        filSave.write(http.content)
        filSave.close()

        transf_size = int(os.path.getsize(filSave.name))
        if orig_size is not None:
            if transf_size == orig_size:
                print("File {name} downloaded correctly".format(name=file))
                return True
            else:
                print("File {name} downloaded but sizes are "
                      "different".format(name=file))
                time.sleep(5)
                self._download_file(file)
        else:
            print("File {name} downloaded, but not checked".format(name=file))
            return True

    def _extract_file(self, file, remove=True):
        """Extract a singolar XZ file"""
        outfile = file.replace('.xz', '')
        outpath = os.path.join(self.workdir, outfile)
        if os.path.exists(outpath):
            print("{} already exists".format(outpath))
            return True
        output = open(outpath, 'wb')
        inpath = os.path.join(self.workdir, file)
        with lzma.open(inpath) as f:
            output.write(f.read())
        output.close()
        f.close()
        self.files.append(outfile)
        if remove:
            os.remove(inpath)
        return True

    def get_min_tile(self):
        """Return the first"""
        tile = mercantile.bounding_tile(*self.extent)
        return tile.z

    def get_tiles(self, minz=None, maxz=18):
        """Get the tile for each zoom levels"""
        if not minz:
            minz = self.get_min_tile()
        for tile in mercantile.tiles(*self.extent, range(minz, maxz + 1)):
            tilestr = "{z}/{x}/{y}".format(z=tile.z, x=tile.x, y=tile.y)
            self.tiles.append(tilestr)
            self.out['tiles'][tilestr] = {}

    def check_existing_files(self, year=None, month=None):
        """Check files already downloaded"""
        if year and month:
            patt = 'tiles-{ye}-{mo}*.txt'.format(ye=year, mo=month)
        else:
            patt = 'tiles-*.txt'
        for f in glob.glob1(self.workdir, patt):
            if f not in self.files:
                self.files.append(f)
                data = f.replace('tiles-', '').replace('.txt', '')
                if data not in self.out['dates'].keys():
                    self.out['dates'][data] = {}
        return True

    def _analyze_file(self, filename, output=None):
        """Analize a singolar file, saving useful information into output
        dictionaries"""
        start = time.time()
        infile = os.path.join(self.workdir, filename)
        f = open(infile)
        lines = f.readlines()
        date = filename.replace('tiles-', '').replace('.txt', '')
        for line in lines:
            linesplit = line.split(' ')
            tile = linesplit[0]
            val = linesplit[1]
            if tile in self.tiles:
                if not output:
                    self.out['tiles'][tile][date] = int(val)
                    self.out['dates'][date][tile] = int(val)
                elif isinstance(output, dict):
                    output['tiles'][tile][date] = int(val)
                    output['dates'][date][tile] = int(val)
        end = time.time()
        print(filename, end-start, output)

    def _download_tileslog_day(self, file, remove=True):
        """Download and extract a singolar tiles log file"""
        self.out['dates'][file] = {}
        myfile = LOGS_FILE.format(day=file)
        self._download_file(myfile)
        self._extract_file(myfile, remove)
        return True


    def download_tileslog_days(self, days=15, remove=True):
        """Download the tiles log files for the number of days before and after
        the event date"""

        dayfile = LOGS_FILE.format(day=self.eventdate.strftime(LOGS_FORMAT))
        self._download_file(dayfile)
        self._extract_file(dayfile)
        for d in range(1, days + 1):
            delta = timedelta(d)
            before = self.eventdate - delta
            self._download_tileslog_day(before.strftime(LOGS_FORMAT), remove)
            after = self.eventdate + delta
            self._download_tileslog_day(after.strftime(LOGS_FORMAT), remove)

    def download_tileslog_month(self, month, year=None, remove=True):
        """Download the tiOsmEventAnalyst/les log files for a month"""
        year = year if year is not None else self.eventdate.year
        day = datetime(year, month, 1)
        endday = datetime(year, int(month) + 1, 1)
        delta = timedelta(1)
        while day < endday:
            self._download_tileslog_day(day.strftime(LOGS_FORMAT), remove)
            day = day + delta


    def download_tileslog_monthly(self, year=None, remove=True):
        """Download the tiles log files for each month"""
        year = year if year is not None else self.eventdate.year
        for m in range(1, 13):
            self.download_tileslog_month(m, year, remove)


    def download_tileslog_year(self, year=None, day='01', remove=True):
        """Download the tiles log files the first day of each month"""
        year = year if year is not None else self.eventdate.year
        for m in range(1, 13):
            fil = "tiles-{ye}-{mo:02}-{da}.txt.xz".format(ye=year, mo=m,
                                                          da=day)
            self._download_file(fil)
            self._extract_file(fil, remove)

    def _analyze_files(self, cpu=None):
        """Execute analysis using multiprocess"""
        import copy
        mgr = mltp.Manager()
        cpu = cpu if cpu is not None else mltp.cpu_count()
        output = mgr.dict(copy.deepcopy(self.out))
        pool = mltp.Pool(processes=cpu)
        for file in self.files:
            pool.apply_async(self._analyze_file, [file, output])
        pool.close()
        pool.join()
        return output

    def analyze(self, multi=True, cpu=None):
        """Analyze all the downloaded log files"""
        if len(self.files) == 0:
            print("No file loaded")
        if multi:
            self.multi = True
            self.out = self._analyze_files(cpu)
        else:
            for file in self.files:
                self._analyze_file(file)
        for k, v in self.out['dates'].items():
            try:
                valnump = np.array(list(v.values()))
                self.final_dates['sum'][k] = valnump.sum()
                self.final_dates['avg'][k] = valnump.mean()
                self.final_dates['min'][k] = valnump.min()
                self.final_dates['max'][k] = valnump.max()
            except ValueError:
                pass
        for k, v in self.out['tiles'].items():
            try:
                valnump = np.array(list(v.values()))
                self.final_tiles['sum'][k] = valnump.sum()
                self.final_tiles['avg'][k] = valnump.mean()
                self.final_tiles['min'][k] = valnump.min()
                self.final_tiles['max'][k] = valnump.max()
            except ValueError:
                pass
        return True

    def output(self, datespath=None, tilespath=None):
        """Write final result to json file"""
        if datespath:
            write_output(datespath, self.final_dates)
        if tilespath:
            write_output(tilespath, self.final_tiles)
        return True

def main():
    """Execute main code"""
    import argparse
    parser = argparse.ArgumentParser(description='OSM data analysis to check event')
    parser.add_argument('date', help='The date of event in iso format '
                        'YYYY-MM-DDTHH:MM:SSZ')
    parser.add_argument('geojson', help='Path to geojson of the area '
                        'to monitor')
    subparsers = parser.add_subparsers(help='sub-commands help',
                                       dest='subparser')
    parser_data = subparsers.add_parser('data')
    parser_data.add_argument('conn')
    parser_data.add_argument('-u', '--user_output', help='Path to output json '
                             'file with data related to users')
    parser_data.add_argument('-d', '--data_output', help='Path to output json '
                             'file with data related to data')
    parser_tiles = subparsers.add_parser('tiles')
    parser_tiles.add_argument('workdir')
    parser_tiles.add_argument('-d', '--dates_output', help='Path to output json'
                              ' file with data related to tiles grouped by '
                              'dates')
    parser_tiles.add_argument('-t', '--tile_output', help='Path to output json'
                              ' file with data related to tiles grouped by '
                              'tiles')
    parser_tiles.add_argument('-c', '--cpu', default=None, help='Run analysis '
                              'in using multiprocessing', type=int)
    args = parser.parse_args()
    if args.subparser == 'data':
        osmea = OsmDataEventAnalyze(args.conn, args.date, args.geojson)
        # get all user in the area
        osmea.get_users()
        # get info for each user
        osmea.get_info()
        # get old and new user in this area
        oldusersno, oldusersyes, newusers = osmea.get_new_old_user()
        # get real new user
        newusersarea, newusersrealout, newusersrealin = osmea.real_new_user(newusers)
        # get info about new user starting editing in the area
        osmea.get_info_newuser(newusersrealin)
        # get data for each table
        for table in TABLES:
            olddata, newdata, modidata = osmea.get_data(table)
            olds = osmea.compare_data(olddata, modidata)
            news = osmea.compare_data(newdata, modidata)
            osmea.analyze_data(olds, table, 'old')
            osmea.analyze_data(news, table, 'new')
        osmea.output(args.user_output, args.data_output)
    elif args.subparser == 'tiles':
        multi = False
        if args.cpu:
            multi = True
        osmtile = OsmTileLogEventAnalyze(args.date, args.geojson, args.workdir)
        # get tiles
        osmtile.get_tiles()
        osmtile.download_tileslog_days()
        osmtile.download_tileslog_year()
        osmtile.analyze(multi, args.cpu)
        osmtile.output(args.dates_output, args.tile_output)

if __name__ == "__main__":
    main()
