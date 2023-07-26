#!/usr/bin/python3
import os
import json
import argparse

import numpy as np

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('-time', action='store_true', default=False, help='Show statistics of running time.')
    parser.add_argument('-tsv', action='store', default=None, help='Output running time into the specified file in .tsv format.')
    parser.add_argument('-tsv_neq', action='store_true', default=None, help='Output running time of NEQ cases in .tsv as well.')
    parser.add_argument('-tests', action='store', default='all', help='Specify the test set. Possible values: all (by default), calcite, spark.')
    parser.add_argument('-rounds', action='store', default=5, help='Specify how many times each case is verified if -time is set.')
    parser.add_argument('-target', action='store', default=-1, help='Only verify the specified pair.')
    parser.add_argument('-skip', action='store', default='', help='Skip specified pairs (e.g. 2,3,5)')
    parser.add_argument('-out', action='store', default=None, help='Output to file')
    # parser.add_argument('--test2', type=int, required=True)
    args = parser.parse_args()
    tsv_str = '-tsv={}'.format(args.tsv) if args.tsv is not None else ''
    input_str = ''
    if args.tests == 'calcite':
        input_str = ''
    elif args.tests == 'spark':
        input_str = '-i=wtune_data/db_rule_instances/spark_tests'
    skip_str = ('-skip=' + args.skip) if args.skip else ''
    out_str = ('-out=' + args.out) if args.out else ''
    # print(args)
    os.system("gradle :superopt:run --args='RunSQLSolver -time={} {} -tsv_neq={} -rounds={} -target={} {} {} {}'".format(args.time, tsv_str, args.tsv_neq, args.rounds, args.target, out_str, skip_str, input_str))
