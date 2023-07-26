#!/usr/bin/python3
import os
import sys
import glob

query_original = '''select t.id, count(distinct t.user_id)
from (select id, user_id from invitations
      union
      (select distinct *
       from (select id, user_id from invitations
             union
             select id, user_id from invitations)
       as t0)) as t
group by t.id'''

query_rewritten = '''select t.id, count(distinct t.user_id)
from invitations as t
group by t.id'''

# tag: base/large
def run_once(tag):
    print("Running the %s test" % tag)
    result = []
    # do evaluation & generate the result .csv
    os.system("bash -c \"click-to-run/run-useful-rewrite-example.sh -tag %s\" >/dev/null 2>&1" % tag)
    # read result .csv & output on the screen later
    csvs = glob.glob("wtune_data/profile/WeTune/%s_WeTune_ss.*.csv" % tag)
    if len(csvs) != 1:
        print("ERROR: there should be exactly one result .csv in wtune_data/profile/WeTune")
        sys.exit(1)
    with open(csvs[0], "r") as ofile:
        content = ofile.read()
        lines = content.split("\n")
        for line in lines:
            if line.strip() == "":
                continue
            cells = line.split(";")
            p50 = cells[3]
            p99 = cells[5]
            result.append({"p50":int(p50), "p99":int(p99)})
    return result

def print_result(result):
    print("-- original: p50 = %.3f ms, p99 = %.3f ms"
          % (result[0]["p50"] / 1000000, result[0]["p99"] / 1000000))
    print("-- rewritten: p50 = %.3f ms, p99 = %.3f ms"
          % (result[1]["p50"] / 1000000, result[1]["p99"] / 1000000))

if __name__ == "__main__":
    result_base = run_once("base")
    result_large = run_once("large")
    print("[RESULTS]\n")
    print("0. Tested queries\n")
    print("-- original: ")
    print(query_original)
    print()
    print("-- rewritten: ")
    print(query_rewritten)
    print()
    print("1. Base test (10K)\n")
    print_result(result_base)
    print()
    print("2. Large test (1M)\n")
    print_result(result_large)
