#!/usr/bin/env sh
docker run --link invenio_mysql_1:db -e CFG_DATABASE_HOST=db -e CACHE_REDIS_HOST=cache -e INVENIO_APP_CONFIG_ENVS=CACHE_REDIS_HOST,CFG_DATABASE_HOST invenio_web:latest inveniomanage database init --user=root --password=mysecretpassword --yes-i-know
docker run --link invenio_mysql_1:db -e CFG_DATABASE_HOST=db -e CACHE_REDIS_HOST=cache -e INVENIO_APP_CONFIG_ENVS=CACHE_REDIS_HOST,CFG_DATABASE_HOST invenio_web:latest inveniomanage database create
