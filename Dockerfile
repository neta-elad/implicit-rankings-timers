FROM python:3.13

WORKDIR /usr/src/implicit-rankings-timers
ADD docs docs
ADD ivy_files ivy_files
ADD examples/*.py examples/
ADD Makefile .
ADD ./*.py .
ADD requirements.txt .
ADD README.md .
ADD LICENSE .
RUN make install