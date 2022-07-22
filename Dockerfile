ARG BASE_CONTAINER=python:3.10.2-alpine3.15
FROM $BASE_CONTAINER
LABEL author="Dominic Steinhoefel"

USER root
RUN echo "https://dl-cdn.alpinelinux.org/alpine/edge/testing" >> /etc/apk/repositories
RUN apk update
RUN apk upgrade
# RUN apk add python3-dev git bash gcc g++ libgcc py3-scipy gfortran libgfortran musl musl-dev lapack lapack-dev freetype-dev libffi-dev make cmake clang
RUN apk add python3-dev git bash gcc g++ make cmake clang z3

RUN wget https://github.com/Clever/csvlint/releases/download/v0.3.0/csvlint-v0.3.0-linux-amd64.tar.gz -O /tmp/csvlint.tar.gz
RUN tar xzf /tmp/csvlint.tar.gz -C /tmp
RUN mv /tmp/csvlint-v0.3.0-linux-amd64/csvlint /usr/bin

RUN adduser -D isla
USER isla
WORKDIR /home/isla
ADD requirements_test.txt /home/isla

RUN pip install --upgrade pip
RUN pip install wheel
RUN pip install -r requirements_test.txt

CMD ["bash"]
