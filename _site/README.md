# ISLa Documentation

This directory contains the code for the ISLa web page
https://rindphi.github.io/isla/. Most notably, the file `islaspec.md` contains
the official ISLa language specification. To view the ISLa web page locally
(tested on macOS), you must install Ruby 2.1.0 or higher. Then, run inside the
`docs/` directory

```shell
gem install bundler
bundle install
bundle exec jekyll serve
```

If everything went as expected, you should be able to open the URL
`http://localhost:4000` in a web browser on your machine.
