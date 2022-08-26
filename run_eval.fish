#!/usr/bin/env fish

set script (basename (status -f))
argparse --name="$script" 's/subject=' 't/seconds=' 'r/runs=' 'j/jobs=' 'd/database=' 'h/help' -- $argv or return

if set -q _flag_h
  echo "Evaluate the performance of the ISLa solver."
  echo
  echo "$script [-h] [-s SUBJECT] [-t SECONDS] [-r RUNS] [-j JOBS]"
  echo
  echo "OPTIONS"
  echo "The following $script options are available."
  echo
  echo "-h or --help"
  echo "    Show this help message."
  echo
  echo "-d or --database"
  echo "    The path to the sqlite database where the results should be stored."
  echo
  echo "-j or --jobs"
  echo "    A comma-separated list of jobs that should be executed."
  echo
  echo "-r or --runs"
  echo "    The number of times each job should be run."
  echo
  echo "-t or --seconds"
  echo "    The number of seconds each individual job execution should run."
  echo
  echo "-s or --subject"
  echo "    The name of the subject to evaluate. This has to be one of (without the quotes):"
  echo
  echo "    - 'csv'"
  echo "    - 'rest'"
  echo "    - 'scriptsize_c'"
  echo "    - 'tar'"
  echo "    - 'xml'"
  exit
end

if set -q _flag_s
  set subject $_flag_s
else
  echo "You did not choose the subject to evaluate. I'm choosing 'scriptsize_c' for you."
  echo "Call '$script -h' for help."
  set subject "scriptsize_c"
end

set secs 3600
if set -q _flag_t
  set secs $_flag_t
end

set runs 2
if set -q _flag_r
  set runs $_flag_r
end

set curr_dir (pwd)
set db "$curr_dir/isla_evaluation_$subject.sqlite"
if set -q _flag_d
  set db $_flag_d
end

echo "Database: $db"

if set -q _flag_j
  set jobs (string split "," "$_flag_j")
else
  switch $subject
    case csv
      set jobs "Grammar Fuzzer" "Cnt-Columns"
    case rest
      set jobs "Grammar Fuzzer" "Def-Use" "Def-Use + Len" "Def-Use + Len + List Numbering" "Def-Use + Len + List Numbering + No-Redef"
    case scriptsize_c
      set jobs "Grammar Fuzzer" "Def-Use" "No-Redef" "Def-Use + No-Redef"
    case tar
      set jobs "Grammar Fuzzer" "Length" "Length + Checksum" "Length + Checksum + Def-Use"
    case xml
      set jobs "Grammar Fuzzer" "Def-Use" "Balance" "Balance + Def-Use" "Balance + Def-Use + No-Redef"
    case '*'
      echo "Unknown subject $subject"
      echo "Call '$script -h' for help."
      exit 1
  end
end

if test -z "$VIRTUAL_ENV" -a -d venv
  source venv/bin/activate.fish
end

echo "Jobs: "(string join ", " $jobs)
echo "Running each job $runs times for $secs seconds."

set -x PYTHONPATH (pwd)
set -x PYTHONHASHSEED 0

# Scriptsize-C
for j in $jobs
  for n in (seq $runs)
    python3 -u -O evaluations/evaluate_$subject.py -g -t $secs -j "$j" --db "$db"
  end
end

set jobargs (string join "," $jobs)
python3 -u -O evaluations/evaluate_$subject.py -v -p -a -n -1 --db "$db" -j "$jobargs"

