FROM python:3.13

WORKDIR /usr/src/implicit-rankings-timers
ADD docs docs
ADD examples/*.py examples/
ADD Makefile .
ADD ./*.py .
ADD requirements.txt .
RUN make install