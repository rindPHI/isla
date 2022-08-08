#!/usr/bin/env fish
if test -d venv
  source venv/bin/activate.fish
end

set -x PYTHONPATH (pwd)
set -x PYTHONHASHSEED 0

set curr_dir (pwd)
set db "$curr_dir/isla_evaluation_csv.sqlite"

# CSV
set jobs "Grammar Fuzzer" "Cnt-Columns"
for j in $jobs
  for n in (seq 2)
    python3 -O evaluations/evaluate_csv.py -g -t 3600 -j "$j" --db "$db"
  end
end
    
set jobargs (string join "," $jobs)
python3 -O evaluations/evaluate_csv.py -v -p -n -1 --db "$db" -j "$jobargs"
