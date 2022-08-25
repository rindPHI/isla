#!/usr/bin/env fish

set script (basename (status -f))
argparse --name="$script" 's/seconds=' 'r/runs=' -- $argv or return

set secs 3600
if set -q _flag_s
  set secs $_flag_s
end

set runs 2
if set -q _flag_r
  set runs $_flag_r
end

if test -z "$VIRTUAL_ENV" -a -d venv
  source venv/bin/activate.fish
end

echo "Running each job $runs times for $secs seconds."

set -x PYTHONPATH (pwd)
set -x PYTHONHASHSEED 0

set curr_dir (pwd)
set db "$curr_dir/isla_evaluation_rest.sqlite"

# reST
set jobs "Grammar Fuzzer" "Def-Use" "Def-Use + Len" "Def-Use + Len + List Numbering" "Def-Use + Len + List Numbering + No-Redef"
for j in $jobs
  for n in (seq $runs)
    python3 -u -O evaluations/evaluate_rest.py -g -t $secs -j "$j" --db "$db"
  end
end

set jobargs (string join "," $jobs)
python3 -u -O evaluations/evaluate_rest.py -v -p -a -n -1 --db "$db" -j "$jobargs"
