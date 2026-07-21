FROM eclipse-temurin:22

ENV ALGO=dred
ENV CASE=random
ENV KB=path
ENV RUN=0

RUN apt-get update && \
	apt-get install -y swi-prolog

WORKDIR /app

COPY . /app
	
CMD java -jar inc-mat-mark-1.0.jar $ALGO $CASE $KB $RUN
