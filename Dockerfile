# This file is part of Invenio.
# Copyright (C) 2015 CERN.
#
# Invenio is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License as
# published by the Free Software Foundation; either version 2 of the
# License, or (at your option) any later version.
#
# Invenio is distributed in the hope that it will be useful, but
# WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
# General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with Invenio; if not, write to the Free Software Foundation, Inc.,
# 59 Temple Place, Suite 330, Boston, MA 02111-1307, USA.

###############################################################################
## 1. Base (stable)                                                          ##
###############################################################################

FROM python:2.7

# nodejs repo
RUN curl -sL https://deb.nodesource.com/setup | bash -

# install requirements from repos
RUN apt-get update && apt-get -qy install poppler-utils git subversion nodejs --fix-missing

# install python requirements
RUN pip install --upgrade pip
RUN pip install mock

# install nodejs requirements
RUN npm update && npm install --silent -g bower less clean-css uglify-js requirejs


###############################################################################
## 2. Code (unstable)                                                        ##
###############################################################################

# select proper requierments level
#ENV REQUIREMENTS lowest
#ENV REQUIREMENTS release
ENV REQUIREMENTS devel

# Adding current directory as `/code`.
ADD . /code
WORKDIR /code


###############################################################################
## 3. Build (unstable)                                                       ##
###############################################################################

# install python requirements
RUN python requirements.py > .travis-lowest-requirements.txt
RUN touch .travis-release-requirements.txt
RUN pip install -r requirements.txt --quiet
RUN pip install -r .travis-$REQUIREMENTS-requirements.txt --allow-all-external --quiet
RUN pip install -e .[docs] --quiet

# build
RUN python setup.py compile_catalog
RUN inveniomanage bower -i bower-base.json > bower.json
RUN bower install --silent --allow-root


###############################################################################
## 4. Config (unstable)                                                       ##
###############################################################################

# setup
RUN inveniomanage config create secret-key
RUN inveniomanage config set CFG_EMAIL_BACKEND flask_email.backends.console.Mail
RUN inveniomanage config set CFG_BIBSCHED_PROCESS_USER `whoami`
RUN inveniomanage config set PACKAGES_EXCLUDE []
RUN inveniomanage config set CFG_TMPDIR /tmp

# standard dev setup
RUN inveniomanage config set COLLECT_STORAGE flask_collect.storage.link
RUN inveniomanage collect > /dev/null
RUN inveniomanage assets build
RUN inveniomanage config set CFG_SITE_URL http://localhost:5000
RUN inveniomanage config set CFG_SITE_SECURE_URL http://localhost:5000
RUN inveniomanage config set CLEANCSS_BIN false
RUN inveniomanage config set LESS_BIN false
RUN inveniomanage config set REQUIREJS_BIN false
RUN inveniomanage config set UGLIFYJS_BIN false
RUN inveniomanage config set ASSETS_AUTO_BUILD False

# before_script:
#   - "inveniomanage apache create-config"
#   - "sudo ln -s $VIRTUAL_ENV/var/invenio.base-instance/apache/invenio-apache-vhost.conf /etc/apache2/sites-enabled/invenio.conf"
#   - "sudo ln -s $VIRTUAL_ENV/var/invenio.base-instance/apache/invenio-apache-vhost-ssl.conf /etc/apache2/sites-enabled/invenio-ssl.conf"
#   - "sudo /usr/sbin/a2dissite *default* || echo ':('"
#   - "sudo /usr/sbin/a2enmod ssl" # enable SSL module
#   - "sudo apachectl configtest && sudo service apache2 restart || echo 'Apache failed ...'"
#   - "inveniomanage database init --yes-i-know || echo ':('"
#   - "inveniomanage database create --quiet || echo ':('"
# #  - "inveniomanage demosite populate --yes-i-know"
#
# script:
#   - "sphinx-build -qnNW docs docs/_build/html"
#   - "python setup.py test"
#

