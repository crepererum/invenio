# This file is part of Invenio.
# Copyright (C) 2006, 2007, 2008, 2009, 2010, 2011, 2012, 2013, 2014, 2015 CERN.
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

"""WebSearch URL handler."""

__revision__ = "$Id$"

import cgi
import os
import datetime
import time
import sys
from urllib import quote
from invenio.utils import apache
import threading
from werkzeug.local import LocalProxy

#maximum number of collaborating authors etc shown in GUI
MAX_COLLAB_LIST = 10
MAX_KEYWORD_LIST = 10
MAX_VENUE_LIST = 10

if sys.hexversion < 0x2040000:
    # pylint: disable=W0622
    from sets import Set as set
    # pylint: enable=W0622

from invenio.config import \
    CFG_SITE_URL, \
    CFG_SITE_NAME, \
    CFG_CACHEDIR, \
    CFG_SITE_LANG, \
    CFG_SITE_SECURE_URL, \
    CFG_BIBRANK_SHOW_DOWNLOAD_STATS, \
    CFG_WEBSEARCH_INSTANT_BROWSE_RSS, \
    CFG_WEBSEARCH_RSS_TTL, \
    CFG_WEBSEARCH_RSS_MAX_CACHED_REQUESTS, \
    CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE, \
    CFG_WEBSEARCH_ENABLED_SEARCH_INTERFACES, \
    CFG_WEBDIR, \
    CFG_WEBSEARCH_USE_MATHJAX_FOR_FORMATS, \
    CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS, \
    CFG_WEBSEARCH_RSS_I18N_COLLECTIONS, \
    CFG_INSPIRE_SITE, \
    CFG_WEBSEARCH_WILDCARD_LIMIT, \
    CFG_SITE_RECORD
from invenio.legacy.dbquery import Error
from invenio.ext.legacy.handler import wash_urlargd, WebInterfaceDirectory
from invenio.utils.url import redirect_to_url, make_canonical_urlargd, drop_default_urlargd
from invenio.utils.html import get_mathjax_header
from invenio.utils.html import nmtoken_from_string
from invenio.legacy.webuser import getUid, page_not_authorized, get_user_preferences, \
    collect_user_info, logoutUser, isUserSuperAdmin
from invenio.legacy.webcomment.webinterface import WebInterfaceCommentsPages
from invenio.legacy.weblinkback.webinterface import WebInterfaceRecordLinkbacksPages
from invenio.legacy.bibcirculation.webinterface import WebInterfaceHoldingsPages
from invenio.legacy.webpage import page, pageheaderonly, create_error_box
from invenio.base.i18n import gettext_set_language
from invenio.legacy.search_engine import check_user_can_view_record, \
    collection_reclist_cache, \
    collection_restricted_p, \
    get_coll_i18nname, \
    get_most_popular_field_values, \
    guess_primary_collection_of_a_record, \
    perform_request_search, \
    restricted_collection_cache, \
    EM_REPOSITORY
from invenio.modules.collections.models import Collection
from invenio.legacy.bibrecord import get_fieldvalues, \
     get_fieldvalues_alephseq_like
from invenio.modules.access.engine import acc_authorize_action
from invenio.modules.access.local_config import VIEWRESTRCOLL
from invenio.modules.access.mailcookie import mail_cookie_create_authorize_action
from invenio.modules.collections.cache import get_collection_reclist
from invenio.modules.formatter import registry
from invenio.modules.formatter.engine import get_output_formats
from intbitset import intbitset
from invenio.legacy.bibupload.engine import find_record_from_sysno
from invenio.legacy.bibrank.citation_searcher import get_cited_by_list
from invenio.legacy.bibrank.downloads_indexer import get_download_weight_total
from invenio.legacy.search_engine.summarizer import summarize_records
from invenio.ext.logging import register_exception
from invenio.legacy.bibeditmulti.webinterface import WebInterfaceMultiEditPages
from invenio.legacy.bibmerge.webinterface import WebInterfaceMergePages
from invenio.legacy.bibdocfile.webinterface import WebInterfaceManageDocFilesPages, WebInterfaceFilesPages
from invenio.legacy.search_engine import get_record
from invenio.utils.shell import mymkdir

import invenio.legacy.template
websearch_templates = invenio.legacy.template.load('websearch')

search_results_default_urlargd = websearch_templates.search_results_default_urlargd
search_interface_default_urlargd = websearch_templates.search_interface_default_urlargd

output_formats = LocalProxy(registry.output_formats.keys)


def wash_search_urlargd(form):
    """
    Create canonical search arguments from those passed via web form.
    """

    argd = wash_urlargd(form, search_results_default_urlargd)
    if 'as' in argd:
        argd['aas'] = argd['as']
        del argd['as']
    if argd.get('aas', CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE) not in CFG_WEBSEARCH_ENABLED_SEARCH_INTERFACES:
        argd['aas'] = CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE

    # Sometimes, users pass ot=245,700 instead of
    # ot=245&ot=700. Normalize that.
    ots = []
    for ot in argd['ot']:
        ots += ot.split(',')
    argd['ot'] = ots

    # We can either get the mode of function as
    # action=<browse|search>, or by setting action_browse or
    # action_search.
    if argd['action_browse']:
        argd['action'] = 'browse'
    elif argd['action_search']:
        argd['action'] = 'search'
    else:
        if argd['action'] not in ('browse', 'search'):
            argd['action'] = 'search'

    del argd['action_browse']
    del argd['action_search']

    if argd['em'] != "":
        argd['em'] = argd['em'].split(",")

    return argd


class WebInterfaceUnAPIPages(WebInterfaceDirectory):
    """ Handle /unapi set of pages."""
    _exports = ['']

    def __call__(self, req, form):
        argd = wash_urlargd(form, {
            'id' : (int, 0),
            'format' : (str, '')})

        formats_dict = get_output_formats(True)
        formats = {}
        for f in formats_dict.values():
            if f['attrs']['visibility']:
                formats[f['attrs']['code'].lower()] = f['attrs']['content_type']
        del formats_dict

        if argd['id'] and argd['format']:
            ## Translate back common format names
            f = {
                'nlm' : 'xn',
                'marcxml' : 'xm',
                'dc' : 'xd',
                'endnote' : 'xe',
                'mods' : 'xo'
            }.get(argd['format'], argd['format'])
            if f in formats:
                redirect_to_url(req, '%s/%s/%s/export/%s' % (CFG_SITE_URL, CFG_SITE_RECORD, argd['id'], f))
            else:
                raise apache.SERVER_RETURN, apache.HTTP_NOT_ACCEPTABLE
        elif argd['id']:
            return websearch_templates.tmpl_unapi(formats, identifier=argd['id'])
        else:
            return websearch_templates.tmpl_unapi(formats)

    index = __call__


class WebInterfaceRecordPages(WebInterfaceDirectory):
    """ Handling of a /CFG_SITE_RECORD/<recid> URL fragment """

    _exports = ['', 'files', 'reviews', 'comments', 'usage', 'references',
                'export', 'citations', 'holdings', 'keywords',
                'multiedit', 'merge', 'plots', 'linkbacks', 'hepdata']

    #_exports.extend(output_formats)

    def __init__(self, recid, tab, form=None):
        self.recid = recid
        self.tab = tab
        self.format = form

        self.files = WebInterfaceFilesPages(self.recid)
        self.reviews = WebInterfaceCommentsPages(self.recid, reviews=1)
        self.comments = WebInterfaceCommentsPages(self.recid)
        self.usage = self
        self.references = self
        self.keywords = self
        self.holdings = WebInterfaceHoldingsPages(self.recid)
        self.citations = self
        self.plots = self
        self.hepdata = self
        self.export = WebInterfaceRecordExport(self.recid, self.format)
        self.merge = WebInterfaceMergePages(self.recid)
        self.linkbacks = WebInterfaceRecordLinkbacksPages(self.recid)

        return

    def __call__(self, req, form):
        argd = wash_search_urlargd(form)

        argd['recid'] = self.recid

        argd['tab'] = self.tab

        # do we really enter here ?

        if self.format is not None:
            argd['of'] = self.format
        req.argd = argd
        uid = getUid(req)
        if uid == -1:
            return page_not_authorized(req, "../",
                text="You are not authorized to view this record.",
                                       navmenuid='search')
        elif uid > 0:
            pref = get_user_preferences(uid)
            try:
                if 'rg' not in form:
                    # fetch user rg preference only if not overridden via URL
                    argd['rg'] = int(pref['websearch_group_records'])
            except (KeyError, ValueError):
                pass

        user_info = collect_user_info(req)
        (auth_code, auth_msg) = check_user_can_view_record(user_info, self.recid)

        if argd['rg'] > CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS and acc_authorize_action(req, 'runbibedit')[0] != 0:
            argd['rg'] = CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS

        #check if the user has rights to set a high wildcard limit
        #if not, reduce the limit set by user, with the default one
        if CFG_WEBSEARCH_WILDCARD_LIMIT > 0 and (argd['wl'] > CFG_WEBSEARCH_WILDCARD_LIMIT or argd['wl'] == 0):
            if acc_authorize_action(req, 'runbibedit')[0] != 0:
                argd['wl'] = CFG_WEBSEARCH_WILDCARD_LIMIT

        # only superadmins can use verbose parameter for obtaining debug information
        if not isUserSuperAdmin(user_info):
            argd['verbose'] = 0

        if auth_code and user_info['email'] == 'guest':
            cookie = mail_cookie_create_authorize_action(VIEWRESTRCOLL, {'collection' : guess_primary_collection_of_a_record(self.recid)})
            target = CFG_SITE_SECURE_URL + '/youraccount/login' + \
                    make_canonical_urlargd({'action': cookie, 'ln' : argd['ln'], 'referer' : CFG_SITE_SECURE_URL + req.unparsed_uri}, {})
            return redirect_to_url(req, target, norobot=True)
        elif auth_code:
            return page_not_authorized(req, "../", \
                text=auth_msg, \
                navmenuid='search')

        from invenio.legacy.search_engine import record_exists, get_merged_recid
        # check if the current record has been deleted
        # and has been merged, case in which the deleted record
        # will be redirect to the new one
        record_status = record_exists(argd['recid'])
        merged_recid = get_merged_recid(argd['recid'])
        if record_status == -1 and merged_recid:
            url = CFG_SITE_URL + '/' + CFG_SITE_RECORD + '/%s?ln=%s'
            url %= (str(merged_recid), argd['ln'])
            redirect_to_url(req, url)
        elif record_status == -1:
            req.status = apache.HTTP_GONE ## The record is gone!

        # mod_python does not like to return [] in case when of=id:
        out = perform_request_search(req, **argd)
        if isinstance(out, intbitset):
            return out.fastdump()
        elif out == []:
            return str(out)
        else:
            return out

    # Return the same page wether we ask for /CFG_SITE_RECORD/123 or /CFG_SITE_RECORD/123/
    index = __call__


class WebInterfaceRecordRestrictedPages(WebInterfaceDirectory):
    """ Handling of a /record-restricted/<recid> URL fragment """

    _exports = ['', 'files', 'reviews', 'comments', 'usage', 'references',
                'export', 'citations', 'holdings', 'keywords',
                'multiedit', 'merge', 'plots', 'linkbacks', 'hepdata']

    #_exports.extend(output_formats)

    def __init__(self, recid, tab, format=None):
        self.recid = recid
        self.tab = tab
        self.format = format

        self.files = WebInterfaceFilesPages(self.recid)
        self.reviews = WebInterfaceCommentsPages(self.recid, reviews=1)
        self.comments = WebInterfaceCommentsPages(self.recid)
        self.usage = self
        self.references = self
        self.keywords = self
        self.holdings = WebInterfaceHoldingsPages(self.recid)
        self.citations = self
        self.plots = self
        self.export = WebInterfaceRecordExport(self.recid, self.format)
        self.merge = WebInterfaceMergePages(self.recid)
        self.linkbacks = WebInterfaceRecordLinkbacksPages(self.recid)
        self.hepdata = self

    def __call__(self, req, form):
        argd = wash_search_urlargd(form)
        argd['recid'] = self.recid
        if self.format is not None:
            argd['of'] = self.format

        req.argd = argd

        uid = getUid(req)
        user_info = collect_user_info(req)
        if uid == -1:
            return page_not_authorized(req, "../",
                text="You are not authorized to view this record.",
                                       navmenuid='search')
        elif uid > 0:
            pref = get_user_preferences(uid)
            try:
                if 'rg' not in form:
                    # fetch user rg preference only if not overridden via URL
                    argd['rg'] = int(pref['websearch_group_records'])
            except (KeyError, ValueError):
                pass

        if argd['rg'] > CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS and acc_authorize_action(req, 'runbibedit')[0] != 0:
            argd['rg'] = CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS

        #check if the user has rights to set a high wildcard limit
        #if not, reduce the limit set by user, with the default one
        if CFG_WEBSEARCH_WILDCARD_LIMIT > 0 and (argd['wl'] > CFG_WEBSEARCH_WILDCARD_LIMIT or argd['wl'] == 0):
            if acc_authorize_action(req, 'runbibedit')[0] != 0:
                argd['wl'] = CFG_WEBSEARCH_WILDCARD_LIMIT

        # only superadmins can use verbose parameter for obtaining debug information
        if not isUserSuperAdmin(user_info):
            argd['verbose'] = 0

        record_primary_collection = guess_primary_collection_of_a_record(self.recid)

        if collection_restricted_p(record_primary_collection):
            (auth_code, dummy) = acc_authorize_action(user_info, VIEWRESTRCOLL, collection=record_primary_collection)
            if auth_code:
                return page_not_authorized(req, "../",
                    text="You are not authorized to view this record.",
                    navmenuid='search')

        # Keep all the arguments, they might be reused in the
        # record page itself to derivate other queries
        req.argd = argd

        # mod_python does not like to return [] in case when of=id:
        out = perform_request_search(req, **argd)
        if isinstance(out, intbitset):
            return out.fastdump()
        elif out == []:
            return str(out)
        else:
            return out

    # Return the same page wether we ask for /CFG_SITE_RECORD/123 or /CFG_SITE_RECORD/123/
    index = __call__


class WebInterfaceSearchResultsPages(WebInterfaceDirectory):
    """ Handling of the /search URL and its sub-pages. """

    _exports = ['', 'authenticate', 'cache']

    def __call__(self, req, form):
        """ Perform a search. """
        argd = wash_search_urlargd(form)

        _ = gettext_set_language(argd['ln'])

        if req.method == 'POST':
            raise apache.SERVER_RETURN, apache.HTTP_METHOD_NOT_ALLOWED

        uid = getUid(req)
        user_info = collect_user_info(req)
        if uid == -1:
            return page_not_authorized(req, "../",
                text=_("You are not authorized to view this area."),
                                       navmenuid='search')
        elif uid > 0:
            pref = get_user_preferences(uid)
            try:
                if 'rg' not in form:
                    # fetch user rg preference only if not overridden via URL
                    argd['rg'] = int(pref['websearch_group_records'])
            except (KeyError, ValueError):
                pass

        if argd['rg'] > CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS and acc_authorize_action(req, 'runbibedit')[0] != 0:
            argd['rg'] = CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS

        involved_collections = set()
        involved_collections.update(argd['c'])
        involved_collections.add(argd['cc'])

        if argd['id'] > 0:
            argd['recid'] = argd['id']
        if argd['idb'] > 0:
            argd['recidb'] = argd['idb']
        if argd['sysno']:
            tmp_recid = find_record_from_sysno(argd['sysno'])
            if tmp_recid:
                argd['recid'] = tmp_recid
        if argd['sysnb']:
            tmp_recid = find_record_from_sysno(argd['sysnb'])
            if tmp_recid:
                argd['recidb'] = tmp_recid

        if argd['recid'] > 0:
            if argd['recidb'] > argd['recid']:
                # Hack to check if among the restricted collections
                # at least a record of the range is there and
                # then if the user is not authorized for that
                # collection.
                recids = intbitset(xrange(argd['recid'], argd['recidb']))
                restricted_collection_cache.recreate_cache_if_needed()
                for collname in restricted_collection_cache.cache:
                    (auth_code, auth_msg) = acc_authorize_action(user_info, VIEWRESTRCOLL, collection=collname)
                    if auth_code and user_info['email'] == 'guest':
                        coll_recids = get_collection_reclist(collname)
                        if coll_recids & recids:
                            cookie = mail_cookie_create_authorize_action(VIEWRESTRCOLL, {'collection' : collname})
                            target = CFG_SITE_SECURE_URL + '/youraccount/login' + \
                                    make_canonical_urlargd({'action': cookie, 'ln' : argd['ln'], 'referer' : CFG_SITE_SECURE_URL + req.unparsed_uri}, {})
                            return redirect_to_url(req, target, norobot=True)
                    elif auth_code:
                        return page_not_authorized(req, "../", \
                            text=auth_msg, \
                            navmenuid='search')
            else:
                involved_collections.add(guess_primary_collection_of_a_record(argd['recid']))

        # If any of the collection requires authentication, redirect
        # to the authentication form.
        for coll in involved_collections:
            if collection_restricted_p(coll):
                (auth_code, auth_msg) = acc_authorize_action(user_info, VIEWRESTRCOLL, collection=coll)
                if auth_code and user_info['email'] == 'guest':
                    cookie = mail_cookie_create_authorize_action(VIEWRESTRCOLL, {'collection' : coll})
                    target = CFG_SITE_SECURE_URL + '/youraccount/login' + \
                            make_canonical_urlargd({'action': cookie, 'ln' : argd['ln'], 'referer' : CFG_SITE_SECURE_URL + req.unparsed_uri}, {})
                    return redirect_to_url(req, target, norobot=True)
                elif auth_code:
                    return page_not_authorized(req, "../", \
                        text=auth_msg, \
                        navmenuid='search')

        #check if the user has rights to set a high wildcard limit
        #if not, reduce the limit set by user, with the default one
        if CFG_WEBSEARCH_WILDCARD_LIMIT > 0 and (argd['wl'] > CFG_WEBSEARCH_WILDCARD_LIMIT or argd['wl'] == 0):
            auth_code, auth_message = acc_authorize_action(req, 'runbibedit')
            if auth_code != 0:
                argd['wl'] = CFG_WEBSEARCH_WILDCARD_LIMIT

        # only superadmins can use verbose parameter for obtaining debug information
        if not isUserSuperAdmin(user_info):
            argd['verbose'] = 0

        # Keep all the arguments, they might be reused in the
        # search_engine itself to derivate other queries
        req.argd = argd

        # mod_python does not like to return [] in case when of=id:
        out = perform_request_search(req, **argd)
        if isinstance(out, intbitset):
            return out.fastdump()
        elif out == []:
            return str(out)
        else:
            return out

    def authenticate(self, req, form):
        """Restricted search results pages."""

        argd = wash_search_urlargd(form)

        user_info = collect_user_info(req)
        for coll in argd['c'] + [argd['cc']]:
            if collection_restricted_p(coll):
                (auth_code, auth_msg) = acc_authorize_action(user_info, VIEWRESTRCOLL, collection=coll)
                if auth_code and user_info['email'] == 'guest':
                    cookie = mail_cookie_create_authorize_action(VIEWRESTRCOLL, {'collection' : coll})
                    target = CFG_SITE_SECURE_URL + '/youraccount/login' + \
                            make_canonical_urlargd({'action': cookie, 'ln' : argd['ln'], 'referer' : CFG_SITE_SECURE_URL + req.unparsed_uri}, {})
                    return redirect_to_url(req, target, norobot=True)
                elif auth_code:
                    return page_not_authorized(req, "../", \
                        text=auth_msg, \
                        navmenuid='search')

        #check if the user has rights to set a high wildcard limit
        #if not, reduce the limit set by user, with the default one
        if CFG_WEBSEARCH_WILDCARD_LIMIT > 0 and (argd['wl'] > CFG_WEBSEARCH_WILDCARD_LIMIT or argd['wl'] == 0):
            auth_code, auth_message = acc_authorize_action(req, 'runbibedit')
            if auth_code != 0:
                argd['wl'] = CFG_WEBSEARCH_WILDCARD_LIMIT

        # only superadmins can use verbose parameter for obtaining debug information
        if not isUserSuperAdmin(user_info):
            argd['verbose'] = 0

        # Keep all the arguments, they might be reused in the
        # search_engine itself to derivate other queries
        req.argd = argd

        uid = getUid(req)
        if uid > 0:
            pref = get_user_preferences(uid)
            try:
                if 'rg' not in form:
                    # fetch user rg preference only if not overridden via URL
                    argd['rg'] = int(pref['websearch_group_records'])
            except (KeyError, ValueError):
                pass


        # mod_python does not like to return [] in case when of=id:
        out = perform_request_search(req, **argd)
        if isinstance(out, intbitset):
            return out.fastdump()
        elif out == []:
            return str(out)
        else:
            return out

    index = __call__


class WebInterfaceLegacySearchPages(WebInterfaceDirectory):
    """ Handling of the /search.py URL and its sub-pages. """

    _exports = ['', ('authenticate', 'index')]

    def __call__(self, req, form):
        """ Perform a search. """

        argd = wash_search_urlargd(form)

        # We either jump into the generic search form, or the specific
        # /CFG_SITE_RECORD/... display if a recid is requested
        if argd['recid'] != -1:
            target = '/%s/%d' % (CFG_SITE_RECORD, argd['recid'])
            del argd['recid']

        else:
            target = '/search'

        target += make_canonical_urlargd(argd, search_results_default_urlargd)
        return redirect_to_url(req, target, apache.HTTP_MOVED_PERMANENTLY)

    index = __call__


# Parameters for the legacy URLs, of the form /?c=ALEPH
legacy_collection_default_urlargd = {
    'as': (int, CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE),
    'aas': (int, CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE),
    'verbose': (int, 0),
    'c': (str, CFG_SITE_NAME)}

class WebInterfaceSearchInterfacePages(WebInterfaceDirectory):

    """ Handling of collection navigation."""

    _exports = [('index.py', 'legacy_collection'),
                ('', 'legacy_collection'),
                ('search.py', 'legacy_search'),
                'search', 'openurl',
                'opensearchdescription', 'logout_SSO_hook']

    search = WebInterfaceSearchResultsPages()
    legacy_search = WebInterfaceLegacySearchPages()

    def logout_SSO_hook(self, req, form):
        """Script triggered by the display of the centralized SSO logout
        dialog. It logouts the user from Invenio and stream back the
        expected picture."""
        logoutUser(req)
        req.content_type = 'image/gif'
        req.encoding = None
        req.filename = 'wsignout.gif'
        req.headers_out["Content-Disposition"] = "inline; filename=wsignout.gif"
        req.set_content_length(os.path.getsize('%s/img/wsignout.gif' % CFG_WEBDIR))
        req.send_http_header()
        req.sendfile('%s/img/wsignout.gif' % CFG_WEBDIR)

    def _lookup(self, component, path):
        """ This handler is invoked for the dynamic URLs (for
        collections and records)"""

        if component == 'collection':
            c = '/'.join(path)

            def answer(req, form):
                """Accessing collections cached pages."""
                # Accessing collections: this is for accessing the
                # cached page on top of each collection.

                argd = wash_urlargd(form, search_interface_default_urlargd)

                # We simply return the cached page of the collection
                argd['c'] = c

                if not argd['c']:
                    # collection argument not present; display
                    # home collection by default
                    argd['c'] = CFG_SITE_NAME

                # Treat `as' argument specially:
                if 'as' in argd:
                    argd['aas'] = argd['as']
                    del argd['as']
                if argd.get('aas', CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE) not in CFG_WEBSEARCH_ENABLED_SEARCH_INTERFACES:
                    argd['aas'] = CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE

                return display_collection(req, **argd)

            return answer, []

        elif component == CFG_SITE_RECORD and path and path[0] == 'merge':
            return WebInterfaceMergePages(), path[1:]

        elif component == CFG_SITE_RECORD and path and path[0] == 'multiedit':
            return WebInterfaceMultiEditPages(), path[1:]

        elif component == CFG_SITE_RECORD and path and path[0] in ('managedocfiles', 'managedocfilesasync'):
            return WebInterfaceManageDocFilesPages(), path

        elif component == CFG_SITE_RECORD or component == 'record-restricted':
            try:
                recid = int(path[0])
            except IndexError:
                # display record #1 for URL /CFG_SITE_RECORD without a number
                recid = 1
            except ValueError:
                if path[0] == '':
                    # display record #1 for URL /CFG_SITE_RECORD/ without a number
                    recid = 1
                else:
                    # display page not found for URLs like /CFG_SITE_RECORD/foo
                    return None, []

            from intbitset import __maxelem__
            if recid <= 0 or recid > __maxelem__:
                # __maxelem__ = 2147483647
                # display page not found for URLs like /CFG_SITE_RECORD/-5 or /CFG_SITE_RECORD/0 or /CFG_SITE_RECORD/2147483649
                return None, []

            format = None
            tab = ''
            try:
                if path[1] in ['', 'files', 'reviews', 'comments', 'usage',
                               'references', 'citations', 'holdings',
                               'keywords', 'multiedit', 'merge', 'plots',
                               'linkbacks', 'hepdata']:
                    tab = path[1]
                elif path[1] == 'export':
                    tab = ''
                    format = path[2]
#                    format = None
#                elif path[1] in output_formats:
#                    tab = ''
#                    format = path[1]
                else:
                    # display page not found for URLs like /CFG_SITE_RECORD/references
                    # for a collection where 'references' tabs is not visible
                    return None, []

            except IndexError:
                # Keep normal url if tabs is not specified
                pass

            #if component == 'record-restricted':
                #return WebInterfaceRecordRestrictedPages(recid, tab, format), path[1:]
            #else:
            return WebInterfaceRecordPages(recid, tab, format), path[1:]
        elif component == 'sslredirect':
            ## Fallback solution for sslredirect special path that should
            ## be rather implemented as an Apache level redirection
            def redirecter(req, form):
                real_url = "http://" + '/'.join(path)
                redirect_to_url(req, real_url)
            return redirecter, []
        elif component == 'doi':
            doi = '/'.join(path)

            def doi_answer(req, form):
                """Resolve DOI"""
                argd = wash_urlargd(form, {'verbose': (int, 0),})
                return resolve_doi(req, doi, verbose=argd['verbose'], ln=argd['ln'])

            return doi_answer, []

        return None, []

    def openurl(self, req, form):
        """ OpenURL Handler."""
        argd = wash_urlargd(form, websearch_templates.tmpl_openurl_accepted_args)
        ret_url = websearch_templates.tmpl_openurl2invenio(argd)
        if ret_url:
            return redirect_to_url(req, ret_url)
        else:
            return redirect_to_url(req, CFG_SITE_URL)

    def opensearchdescription(self, req, form):
        """OpenSearch description file"""
        req.content_type = "application/opensearchdescription+xml"
        req.send_http_header()
        argd = wash_urlargd(form, {'ln': (str, CFG_SITE_LANG),
                                   'verbose': (int, 0) })
        return websearch_templates.tmpl_opensearch_description(ln=argd['ln'])

    def legacy_collection(self, req, form):
        """Collection URL backward compatibility handling."""
        accepted_args = dict(legacy_collection_default_urlargd)
        argd = wash_urlargd(form, accepted_args)

        # Treat `as' argument specially:
        if 'as' in argd:
            argd['aas'] = argd['as']
            del argd['as']
        if argd.get('aas', CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE) not in CFG_WEBSEARCH_ENABLED_SEARCH_INTERFACES:
            argd['aas'] = CFG_WEBSEARCH_DEFAULT_SEARCH_INTERFACE

        # If we specify no collection, then we don't need to redirect
        # the user, so that accessing <http://yoursite/> returns the
        # default collection.
        if 'c' not in form:
            return display_collection(req, **argd)

        # make the collection an element of the path, and keep the
        # other query elements as is. If the collection is CFG_SITE_NAME,
        # however, redirect to the main URL.
        c = argd['c']
        del argd['c']

        if c == CFG_SITE_NAME:
            target = '/'
        else:
            target = '/collection/' + quote(c)

        # Treat `as' argument specially:
        # We are going to redirect, so replace `aas' by `as' visible argument:
        if 'aas' in argd:
            argd['as'] = argd['aas']
            del argd['aas']

        target += make_canonical_urlargd(argd, legacy_collection_default_urlargd)
        return redirect_to_url(req, target)


def display_collection(req, c, aas, verbose, ln, em=""):
    """Display search interface page for collection c by looking
    in the collection cache."""
    _ = gettext_set_language(ln)

    req.argd = drop_default_urlargd({'aas': aas, 'verbose': verbose, 'ln': ln, 'em' : em},
                                    search_interface_default_urlargd)

    if em != "":
        em = em.split(",")
    # get user ID:
    try:
        uid = getUid(req)
        user_preferences = {}
        if uid == -1:
            return page_not_authorized(req, "../",
                text="You are not authorized to view this collection",
                                       navmenuid='search')
        elif uid > 0:
            user_preferences = get_user_preferences(uid)
    except Error:
        register_exception(req=req, alert_admin=True)
        return page(title=_("Internal Error"),
                    body=create_error_box(req, verbose=verbose, ln=ln),
                    description="%s - Internal Error" % CFG_SITE_NAME,
                    keywords="%s, Internal Error" % CFG_SITE_NAME,
                    language=ln,
                    req=req,
                    navmenuid='search')

    # deduce collection id:
    collection = Collection.query.filter_by(name=c).first()
    colID = collection.id if collection else None
    normalised_name = collection.name if collection else c
    if type(colID) is not int:
        page_body = '<p>' + (_("Sorry, collection %(x_colname)s does not seem to exist.", x_colname='<strong>' + str(c) + '</strong>',)) + '</p>'
        page_body = '<p>' + (_("You may want to start browsing from %(x_sitehref)s.", x_sitehref='<a href="' + CFG_SITE_URL + '?ln=' + ln + '">' + get_coll_i18nname(CFG_SITE_NAME, ln) + '</a>')) + '</p>'
        if req.method == 'HEAD':
            raise apache.SERVER_RETURN, apache.HTTP_NOT_FOUND
        return page(title=_("Collection %(x_colname)s Not Found", x_colname=cgi.escape(c)),
                    body=page_body,
                    description=(CFG_SITE_NAME + ' - ' + _("Not found") + ': ' + cgi.escape(str(c))),
                    keywords="%s" % CFG_SITE_NAME,
                    uid=uid,
                    language=ln,
                    req=req,
                    navmenuid='search')

    from flask import redirect, url_for
    return redirect(url_for('collections.collection', name=collection.name))


def resolve_doi(req, doi, ln=CFG_SITE_LANG, verbose=0):
    """
    Redirect to given DOI, or display error page when DOI cannot be
    resolved.
    """
    _ = gettext_set_language(ln)
    # Fetch user ID:
    try:
        uid = getUid(req)
    except Error:
        register_exception(req=req, alert_admin=True)
        return page(title=_("Internal Error"),
                    body=create_error_box(req, verbose=verbose, ln=ln),
                    description="%s - Internal Error" % CFG_SITE_NAME,
                    keywords="%s, Internal Error" % CFG_SITE_NAME,
                    language=ln,
                    req=req,
                    navmenuid='search')
    # Resolve DOI
    recids = perform_request_search(p='doi:"%s"' % doi, of="id", verbose=verbose)
    recids = [recid for recid in recids if doi.lower() in \
              [doi.lower() for doi in get_record(recid).get('doi', '') if doi]]

    # Answer
    if len(recids) == 1:
        # Found unique matching record
        return redirect_to_url(req, CFG_SITE_URL + '/' + CFG_SITE_RECORD + '/' + str(recids[0]))
    elif len(recids) == 0:
        # No corresponding record found
        page_body = '<p>' + (_("Sorry, DOI %(x_doi)s could not be resolved.", x_doi=('<strong>' + str(doi) + '</strong>'))) + '</p>'
        if req.header_only:
            raise apache.SERVER_RETURN, apache.HTTP_NOT_FOUND
        return page(title=_('DOI "%(x_doi)s" Not Found', x_doi=cgi.escape(doi)),
                    body=page_body,
                    description=(CFG_SITE_NAME + ' - ' + _("Not found") + ': ' + cgi.escape(str(doi))),
                    keywords="%s" % CFG_SITE_NAME,
                    uid=uid,
                    language=ln,
                    req=req,
                    navmenuid='search')
    else:
        # Found multiple matching records
        try:
            raise Exception('DOI "%s" matched multiple records (%s) -- Please check' % (doi, ', '.join([str(recid) for recid in recids])))
        except Exception, e:
            register_exception(req=req, alert_admin=True)
        page_body = websearch_templates.tmpl_multiple_dois_found_page(doi, recids, ln)
        return page(title=_('Found multiple records matching DOI %(x_doi)s', x_doi=cgi.escape(doi)),
                    body=page_body,
                    description=(CFG_SITE_NAME + ' - ' + _("Found multiple records matching DOI") + ': ' + cgi.escape(str(doi))),
                    keywords="%s" % CFG_SITE_NAME,
                    uid=uid,
                    language=ln,
                    req=req,
                    navmenuid='search')
    return


class WebInterfaceRSSFeedServicePages(WebInterfaceDirectory):
    """RSS 2.0 feed service pages."""

    def __call__(self, req, form):
        """RSS 2.0 feed service."""
        import warnings
        warnings.warn("Legacy RSS handler has been deprecated.",
                      DeprecationWarning)

    index = __call__


class WebInterfaceRecordExport(WebInterfaceDirectory):
    """ Handling of a /<CFG_SITE_RECORD>/<recid>/export/<format> URL fragment """

    _exports = output_formats

    def __init__(self, recid, format=None):
        self.recid = recid
        self.format = format

        for output_format in output_formats:
            self.__dict__[output_format] = self

        return

    def __call__(self, req, form):
        argd = wash_search_urlargd(form)
        argd['recid'] = self.recid

        if self.format is not None:
            argd['of'] = self.format
        req.argd = argd
        uid = getUid(req)
        if uid == -1:
            return page_not_authorized(req, "../",
                text="You are not authorized to view this record.",
                                       navmenuid='search')
        elif uid > 0:
            pref = get_user_preferences(uid)
            try:
                if 'rg' not in form:
                    # fetch user rg preference only if not overridden via URL
                    argd['rg'] = int(pref['websearch_group_records'])
            except (KeyError, ValueError):
                pass

        # Check if the record belongs to a restricted primary
        # collection.  If yes, redirect to the authenticated URL.
        user_info = collect_user_info(req)
        (auth_code, auth_msg) = check_user_can_view_record(user_info, self.recid)

        if argd['rg'] > CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS and acc_authorize_action(req, 'runbibedit')[0] != 0:
            argd['rg'] = CFG_WEBSEARCH_MAX_RECORDS_IN_GROUPS

        #check if the user has rights to set a high wildcard limit
        #if not, reduce the limit set by user, with the default one
        if CFG_WEBSEARCH_WILDCARD_LIMIT > 0 and (argd['wl'] > CFG_WEBSEARCH_WILDCARD_LIMIT or argd['wl'] == 0):
            if acc_authorize_action(req, 'runbibedit')[0] != 0:
                argd['wl'] = CFG_WEBSEARCH_WILDCARD_LIMIT

        # only superadmins can use verbose parameter for obtaining debug information
        if not isUserSuperAdmin(user_info):
            argd['verbose'] = 0

        if auth_code and user_info['email'] == 'guest':
            cookie = mail_cookie_create_authorize_action(VIEWRESTRCOLL, {'collection' : guess_primary_collection_of_a_record(self.recid)})
            target = CFG_SITE_SECURE_URL + '/youraccount/login' + \
                    make_canonical_urlargd({'action': cookie, 'ln' : argd['ln'], 'referer' : CFG_SITE_SECURE_URL + req.unparsed_uri}, {})
            return redirect_to_url(req, target, norobot=True)
        elif auth_code:
            return page_not_authorized(req, "../", \
                text=auth_msg, \
                navmenuid='search')

        # mod_python does not like to return [] in case when of=id:
        out = perform_request_search(req, **argd)
        if isinstance(out, intbitset):
            return out.fastdump()
        elif out == []:
            return str(out)
        else:
            return out

    # Return the same page wether we ask for /CFG_SITE_RECORD/123/export/xm or /CFG_SITE_RECORD/123/export/xm/
    index = __call__
