#!/usr/bin/python3
import os
import json
import argparse

import numpy as np

def make_db(calcite, tag):
    host = 'localhost'
    port = '1433'
    username = 'SA'
    password = 'mssql2019Admin'

    def findSchema(db):
        dataDir = 'wtune_data'
        fileName = db + '.sql'
        command = 'find {} -name {} | head -1'.format(dataDir, fileName)
        schemaFile = os.popen(command).readlines()[0].strip('\n')
        return schemaFile
    
    def doMakeTable(recreate, dbName, schemaFile):
        if recreate:
            print('drop table {}'.format(dbName))
            dropDB = 'sqlcmd -U {} -P {} -S {},{} <<EOF\n drop database if exists [{}];\n GO'.format(username, password, host, port, dbName)
            os.system(dropDB)
        print('create table {}'.format(dbName))
        createDB = 'sqlcmd -U {} -P {} -S {},{} <<EOF\n create database [{}];\n GO'.format(username, password, host, port, dbName)
        os.system(createDB)
        command = 'sqlcmd -U {} -P {} -S {},{} -d {} -i {} 1>/dev/null 2>&1'.format(username, password, host, port, dbName, schemaFile)
        os.system(command)
        # print("doMakeTable")


    for db in ['broadleaf','calcite_test','diaspora','discourse','eladmin','fatfreecrm','febs','forest_blog','gitlab','guns','halo','homeland','lobsters','publiccms','pybbs','redmine','refinerycms','sagan','shopizer','solidus','spree']:
        dbName=db + '_' + tag
        schemaFile = findSchema(db)
        if schemaFile == '':
            continue
        doMakeTable(True, dbName, schemaFile)
        
def generate_data(spes, calcite, tag): 
    host = 'localhost'
    port = '1433'
    username = 'SA'
    password = 'mssql2019Admin'

    target = 'used'



    

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-tag', type=str, default="base")
    parser.add_argument('-spes', action='store_true', default=False)
    parser.add_argument('-calcite', action='store_true', default=False)
    args = parser.parse_args()
    make_db(args.calcite, args.tag)
    generate_data(args.spes, args.calcite, args.tag)
