#!/usr/bin/env fish
if test -z "$VIRTUAL_ENV" -a -d venv
  source venv/bin/activate.fish
end

set -x PYTHONPATH (pwd)
set -x PYTHONHASHSEED 0

set curr_dir (pwd)
set db "$curr_dir/isla_evaluation_tar.sqlite"

# tar
set jobs "Grammar Fuzzer" "Length" "Length + Checksum" "Length + Checksum + Def-Use"
for j in $jobs
  for n in (seq 2)
    python3 -O evaluations/evaluate_tar.py -g -t 3600 -j "$j" --db "$db"
  end
end

set jobargs (string join "," $jobs)
python3 -O evaluations/evaluate_tar.py -v -p -a -n -1 --db "$db" -j "$jobargs"
