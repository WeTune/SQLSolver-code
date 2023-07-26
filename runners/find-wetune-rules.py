#!/usr/bin/python3
import os
import json
import argparse

import numpy as np

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    # parser.add_argument('--test1', type=str, required=True)
    # parser.add_argument('--test2', type=int, required=True)
    # args = parser.parse_args()
    # print(args)
    os.system("gradle :superopt:run --args='FindWeTuneRules'")
