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
    parser.add_argument('-app', action='store', default=None, help='Specify the app name. Its corresponding table schemas should be in "wtune_data/schemas/APP_NAME.base.schema.sql"')
    parser.add_argument('-input', action='store', default=None, help='Specify the input file.')
    parser.add_argument('-rounds', action='store', default=5, help='Specify how many times each case is verified if -time is set.')
    parser.add_argument('-target', action='store', default=-1, help='Only verify the specified pair.')
    parser.add_argument('-skip', action='store', default='', help='Skip specified pairs (e.g. 2,3,5)')
    parser.add_argument('-out', action='store', default=None, help='Output to file')
    # parser.add_argument('--test2', type=int, required=True)
    args = parser.parse_args()
    tsv_str = '-tsv={}'.format(args.tsv) if args.tsv is not None else ''
    input_str = ('-i=' + args.input) if args.input else ''
    app_str = ('-app=' + args.app) if args.app else ''
    skip_str = ('-skip=' + args.skip) if args.skip else ''
    out_str = ('-out=' + args.out) if args.out else ''
    # print(args)
    os.system("gradle :superopt:run --args='RunSQLSolver -time={} {} -tsv_neq={} -rounds={} -target={} {} {} {} {}'".format(args.time, tsv_str, args.tsv_neq, args.rounds, args.target, out_str, skip_str, input_str, app_str))
