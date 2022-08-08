#!/usr/bin/env fish
source venv/bin/activate.fish
set -x PYTHONPATH (pwd)
set -x PYTHONHASHSEED 0

set curr_dir (pwd)
set db "$curr_dir/isla_evaluation_xml.sqlite"

# XML
set jobs "Grammar Fuzzer" "Def-Use" "Balance" "Balance + Def-Use" "Balance + Def-Use + No-Redef"
for j in $jobs
  for n in (seq 2)
    python3 -O evaluations/evaluate_xml.py -g -t 3600 -j "$j" --db "$db"
  end
end

set jobargs (string join "," $jobs)
python3 -O evaluations/evaluate_xml.py -v -p -n -1 --db "$db" -j "$jobargs"
