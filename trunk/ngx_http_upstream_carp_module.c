
/*
 * Copyright (C) Weibin Yao
 * Email: yaoweibin@gmail.com
 * Licence: the same as Nginx
 * Version: $Id$
 */


#include <ngx_config.h>
#include <ngx_core.h>
#include <ngx_http.h>

#include <math.h>


#define ROTATE_LEFT(x, n) (((x) << (n)) | ((x) >> (32-(n))))


typedef struct {
    struct sockaddr                *sockaddr;
    socklen_t                       socklen;
    ngx_str_t                       name;

    ngx_int_t                       weight;

    ngx_uint_t                      fails;
    time_t                          accessed;

    ngx_uint_t                      max_fails;
    time_t                          fail_timeout;

    ngx_uint_t                      hash;
    double                          load_factor;
    double                          load_multiplier;
    double                          score;

    unsigned                        down;        
    unsigned                        temp_down;        

} ngx_http_upstream_carp_peer_t;

typedef struct {
    ngx_array_t                     *lengths;
    ngx_array_t                     *values;

    ngx_str_t                        carp_str;
} ngx_http_upstream_carp_str_init_t;

typedef struct ngx_http_upstream_carp_peers_s  ngx_http_upstream_carp_peers_t;

struct ngx_http_upstream_carp_peers_s {
    ngx_http_upstream_carp_str_init_t *hash_str;

    ngx_uint_t                         single;        /* unsigned  single:1; */
    ngx_uint_t                         number;
    ngx_uint_t                         weight_total;
    ngx_uint_t                         last_cached;

 /* ngx_mutex_t                       *mutex; */
    ngx_connection_t                 **cached;

    ngx_str_t                         *name;

    ngx_http_upstream_carp_peers_t    *next;

    ngx_http_upstream_carp_peer_t      peer[1];
};

typedef struct {
    ngx_http_upstream_carp_peers_t *peers;
    ngx_uint_t                      user_hash;
    ngx_uint_t                      current;
    uintptr_t                      *tried;
    uintptr_t                       data;
} ngx_http_upstream_carp_peer_data_t;


static char * ngx_http_upstream_carp(ngx_conf_t *cf, ngx_command_t *cmd,
        void *conf);
static ngx_int_t ngx_http_upstream_init_carp(ngx_conf_t *cf,
    ngx_http_upstream_srv_conf_t *us);
static ngx_int_t ngx_http_upstream_init_carp_peer(ngx_http_request_t *r,
    ngx_http_upstream_srv_conf_t *us);
static ngx_int_t ngx_http_upstream_get_carp_peer(ngx_peer_connection_t *pc,
    void *data);
static void ngx_http_upstream_free_carp_peer(ngx_peer_connection_t *pc,
    void *data, ngx_uint_t state);

#if (NGX_HTTP_SSL)
static ngx_int_t
    ngx_http_upstream_set_carp_peer_session(ngx_peer_connection_t *pc,
    void *data);
static void ngx_http_upstream_save_carp_peer_session(ngx_peer_connection_t *pc,
    void *data);
#endif

static ngx_int_t ngx_http_upstream_cmp_servers(const void *one,
    const void *two);
static ngx_uint_t
ngx_http_upstream_get_peer(ngx_http_upstream_carp_peer_data_t *ucpd);


static ngx_command_t  ngx_http_upstream_carp_commands[] = {

    { ngx_string("carp"),
      NGX_HTTP_UPS_CONF|NGX_CONF_TAKE1|NGX_CONF_NOARGS,
      ngx_http_upstream_carp,
      0,
      0,
      NULL },

      ngx_null_command
};

static ngx_http_module_t  ngx_http_upstream_carp_module_ctx = {
    NULL,                                  /* preconfiguration */
    NULL,                                  /* postconfiguration */

    NULL,                                  /* create main configuration */
    NULL,                                  /* init main configuration */

    NULL,                                  /* create server configuration */
    NULL,                                  /* merge server configuration */

    NULL,                                  /* create location configuration */
    NULL                                   /* merge location configuration */
};

ngx_module_t  ngx_http_upstream_carp_module = {
    NGX_MODULE_V1,
    &ngx_http_upstream_carp_module_ctx,    /* module context */
    ngx_http_upstream_carp_commands,       /* module directives */
    NGX_HTTP_MODULE,                       /* module type */
    NULL,                                  /* init master */
    NULL,                                  /* init module */
    NULL,                                  /* init process */
    NULL,                                  /* init thread */
    NULL,                                  /* exit thread */
    NULL,                                  /* exit process */
    NULL,                                  /* exit master */
    NGX_MODULE_V1_PADDING
};

static ngx_int_t
ngx_http_upstream_init_carp_peers(ngx_http_upstream_carp_peers_t *peers)
{
    ngx_uint_t i, j, k, K;
    double P_last, X_last, Xn;
    ngx_http_upstream_carp_peer_t *peer, *p;


    for (i = 0; i < peers->number; i++) {
        if (peers->peer[i].weight == 0) {
            continue;
        }

        peer = &peers->peer[i];
        for (j = 0; j < peer->name.len; j++) {
            peer->hash += ROTATE_LEFT(peer->hash, 19) + peer->name.data[j];
        }
        peer->hash += peer->hash * 0x62531965;
        peer->hash = ROTATE_LEFT(peer->hash, 21);

        peer->load_factor =  ((double) peer->weight) / (double) peers->weight_total;
        if (floor(peer->load_factor * 1000) == 0.0) {
            peer->load_factor = 0.0;
        } 
    }

    /* Calculate the load factor multipliers X_k
     *
     * X_1 = pow ((K*p_1), (1/K))
     * X_k = ([K-k+1] * [P_k - P_{k-1}])/(X_1 * X_2 * ... * X_{k-1})
     * X_k += pow ((X_{k-1}, {K-k+1})
     * X_k = pow (X_k, {1/(K-k+1)})
     * simplified to have X_1 part of the loop
     */
    K = peers->number;
    P_last = 0.0;       /* Empty P_0 */
    Xn = 1.0;           /* Empty starting point of X_1 * X_2 * ... * X_{x-1} */
    X_last = 0.0;       /* Empty X_0, nullifies the first pow statement */

    for (k = 1; k <= K; k++) {
        double Kk1 = (double) (K - k + 1);
        p = &peers->peer[k - 1];
        p->load_multiplier = (Kk1 * (p->load_factor - P_last)) / Xn;
        p->load_multiplier += pow(X_last, Kk1);
        p->load_multiplier = pow(p->load_multiplier, 1.0 / Kk1);
        Xn *= p->load_multiplier;
        X_last = p->load_multiplier;
        P_last = p->load_factor;
    }

    return NGX_OK;
}

static ngx_int_t
ngx_http_upstream_init_carp(ngx_conf_t *cf,
    ngx_http_upstream_srv_conf_t *us)
{
    ngx_uint_t                      i, j, n, sum_weight;
    ngx_http_upstream_server_t     *server;
    ngx_http_upstream_carp_peers_t *peers, *backup;

    us->peer.init = ngx_http_upstream_init_carp_peer;

    if (us->servers) {
        server = us->servers->elts;

        n = 0;

        for (i = 0; i < us->servers->nelts; i++) {
            if (server[i].backup) {
                continue;
            }

            n += server[i].naddrs;
        }

        peers = ngx_pcalloc(cf->pool, sizeof(ngx_http_upstream_carp_peers_t)
                              + sizeof(ngx_http_upstream_carp_peer_t) * (n - 1));
        if (peers == NULL) {
            return NGX_ERROR;
        }

        peers->hash_str = us->peer.data;
        peers->single = (n == 1);
        peers->number = n;
        peers->name = &us->host;

        n = sum_weight = 0;

        for (i = 0; i < us->servers->nelts; i++) {
            for (j = 0; j < server[i].naddrs; j++) {
                if (server[i].backup) {
                    continue;
                }

                peers->peer[n].sockaddr = server[i].addrs[j].sockaddr;
                peers->peer[n].socklen = server[i].addrs[j].socklen;
                peers->peer[n].name = server[i].addrs[j].name;
                peers->peer[n].max_fails = server[i].max_fails;
                peers->peer[n].fail_timeout = server[i].fail_timeout;
                peers->peer[n].down = server[i].down;
                peers->peer[n].weight = server[i].down ? 0 : server[i].weight;

                sum_weight += peers->peer[n].weight;
                n++;
            }
        }

        peers->weight_total = sum_weight;
        us->peer.data = peers;

        ngx_sort(&peers->peer[0], (size_t) n,
                 sizeof(ngx_http_upstream_carp_peer_t),
                 ngx_http_upstream_cmp_servers);

        ngx_http_upstream_init_carp_peers(peers);

        /* backup servers */

        n = 0;

        for (i = 0; i < us->servers->nelts; i++) {
            if (!server[i].backup) {
                continue;
            }

            n += server[i].naddrs;
        }

        if (n == 0) {
            return NGX_OK;
        }

        backup = ngx_pcalloc(cf->pool, sizeof(ngx_http_upstream_carp_peers_t)
                              + sizeof(ngx_http_upstream_carp_peer_t) * (n - 1));
        if (backup == NULL) {
            return NGX_ERROR;
        }

        peers->single = 0;
        backup->single = 0;
        backup->number = n;
        backup->name = &us->host;

        n = sum_weight = 0;

        for (i = 0; i < us->servers->nelts; i++) {
            for (j = 0; j < server[i].naddrs; j++) {
                if (!server[i].backup) {
                    continue;
                }

                backup->peer[n].sockaddr = server[i].addrs[j].sockaddr;
                backup->peer[n].socklen = server[i].addrs[j].socklen;
                backup->peer[n].name = server[i].addrs[j].name;
                backup->peer[n].weight = server[i].weight;
                backup->peer[n].max_fails = server[i].max_fails;
                backup->peer[n].fail_timeout = server[i].fail_timeout;
                backup->peer[n].down = server[i].down;

                sum_weight += peers->peer[n].weight;
                n++;
            }
        }

        backup->weight_total = sum_weight;

        peers->next = backup;

        ngx_sort(&backup->peer[0], (size_t) n,
                 sizeof(ngx_http_upstream_carp_peer_t),
                 ngx_http_upstream_cmp_servers);

        ngx_http_upstream_init_carp_peers(backup);

        return NGX_OK;
    }

    ngx_log_error(NGX_LOG_EMERG, cf->log, 0,
            "carp# No upstream server in upstream \"%V\" in %s:%ui",
            &us->host, us->file_name, us->line);
    return NGX_ERROR;
}


static ngx_int_t
ngx_http_upstream_cmp_servers(const void *one, const void *two)
{
    ngx_http_upstream_carp_peer_t  *first, *second;

    first = (ngx_http_upstream_carp_peer_t *) one;
    second = (ngx_http_upstream_carp_peer_t *) two;

    return (first->weight > second->weight);
}


static ngx_int_t
ngx_http_upstream_init_carp_peer(ngx_http_request_t *r,
    ngx_http_upstream_srv_conf_t *us)
{
    double                               high_score;
    ngx_uint_t                           i, n, hash, combined_hash;
    ngx_str_t                            val;
    ngx_http_upstream_carp_peer_data_t  *ucpd;
    ngx_http_upstream_carp_peer_t       *peer;
    ngx_http_upstream_carp_str_init_t   *init_str;

    ucpd = r->upstream->peer.data;

    if (ucpd == NULL) {
        ucpd = ngx_palloc(r->pool, sizeof(ngx_http_upstream_carp_peer_data_t));
        if (ucpd == NULL) {
            return NGX_ERROR;
        }

        r->upstream->peer.data = ucpd;
    }
    ucpd->peers = us->peer.data;
    init_str = ucpd->peers->hash_str;

    ngx_log_debug4(NGX_LOG_DEBUG_HTTP, r->connection->log, 0,
                   "carp# start, upstream:\"%V\", number:%ui, "
                   "weight: %ui, carp_str: \"%V\" ",
                   ucpd->peers->name, 
                   ucpd->peers->number,
                   ucpd->peers->weight_total, 
                   &init_str->carp_str);

    val.len = 0;
    if (init_str->lengths != NULL && init_str->values != NULL) {
        if (ngx_http_script_run(r, &val, init_str->lengths->elts, 
                    0, init_str->values->elts) == NULL) {
            return NGX_ERROR;
        }
    } 

    if (val.len == 0) {
        val.data = r->uri.data;
        val.len = r->uri.len;
    }

    hash = 0;
    for (i = 0; i < val.len; i++) {
        hash += ROTATE_LEFT(hash, 19) + val.data[i];
    }
    ucpd->user_hash = hash;
    ngx_log_debug2(NGX_LOG_DEBUG_HTTP, r->connection->log, 0,
                   "carp# user_hash: %ui from string:\"%V\"",
                   ucpd->user_hash, &val);

    high_score = 0.0;
    n = 0;
    peer = &ucpd->peers->peer[0];
    for (i = 0; i < ucpd->peers->number; i++) {
        if (peer[i].weight <= 0 || peer[i].load_factor <= 0.0) {
            continue;
        }
        
        combined_hash = (hash ^ peer[i].hash);
        combined_hash += combined_hash * 0x62531965;
        combined_hash = ROTATE_LEFT(combined_hash, 21);
        peer[i].score = (double)combined_hash * (double)peer[i].load_multiplier;

        if (peer[i].score > high_score) {
            high_score = peer[i].score;
            n = i;
        }
        ngx_log_debug7(NGX_LOG_DEBUG_HTTP, r->connection->log, 0,
                "carp# init score, peer[%02ui]: {name=\"%V\", weight=%ui, " 
                "hash=%ui, load_factor=%.6f, load_multiplier=%.6f, score=%.6f}",
                i, &peer[i].name, peer[i].weight,  
                peer[i].hash, peer[i].load_factor,
                peer[i].load_multiplier, peer[i].score);
    }
    ucpd->current = n;

    if (ucpd->peers->number <= 8 * sizeof(uintptr_t)) {
        ucpd->tried = &ucpd->data;
        ucpd->data = 0;

    } else {
        n = (ucpd->peers->number + (8 * sizeof(uintptr_t) - 1))
                / (8 * sizeof(uintptr_t));

        ucpd->tried = ngx_pcalloc(r->pool, n * sizeof(uintptr_t));
        if (ucpd->tried == NULL) {
            return NGX_ERROR;
        }
    }

    r->upstream->peer.get = ngx_http_upstream_get_carp_peer;
    r->upstream->peer.free = ngx_http_upstream_free_carp_peer;
    r->upstream->peer.tries = ucpd->peers->number;
#if (NGX_HTTP_SSL)
    r->upstream->peer.set_session =
                               ngx_http_upstream_set_carp_peer_session;
    r->upstream->peer.save_session =
                               ngx_http_upstream_save_carp_peer_session;
#endif

    return NGX_OK;
}


ngx_int_t
ngx_http_upstream_get_carp_peer(ngx_peer_connection_t *pc, void *data)
{
    ngx_http_upstream_carp_peer_data_t  *ucpd = data;

    time_t                          now;
    uintptr_t                       m;
    ngx_int_t                       rc;
    ngx_uint_t                      i, n;
    ngx_connection_t               *c;
    ngx_http_upstream_carp_peer_t  *peer;
    ngx_http_upstream_carp_peers_t *peers;

    ngx_log_debug1(NGX_LOG_DEBUG_HTTP, pc->log, 0,
                   "carp# get carp peer, try: %ui", pc->tries);

    now = ngx_time();

    /* ngx_lock_mutex(ucpd->peers->mutex); */

    if (ucpd->peers->last_cached) {

        /* cached connection */

        c = ucpd->peers->cached[ucpd->peers->last_cached];
        ucpd->peers->last_cached--;

        /* ngx_unlock_mutex(ppr->peers->mutex); */

#if (NGX_THREADS)
        c->read->lock = c->read->own_lock;
        c->write->lock = c->write->own_lock;
#endif

        pc->connection = c;
        pc->cached = 1;

        return NGX_OK;
    }

    pc->cached = 0;
    pc->connection = NULL;

    if (ucpd->peers->single) {
        peer = &ucpd->peers->peer[0];

    } else {

        /* there are several peers */

        i = pc->tries;
        for ( ;; ) {

            ngx_log_debug2(NGX_LOG_DEBUG_HTTP, pc->log, 0,
                    "carp# try carp peer, current: %ui, score: %f",
                    ucpd->current,
                    ucpd->peers->peer[ucpd->current].score);

            n = ucpd->current / (8 * sizeof(uintptr_t));
            m = (uintptr_t) 1 << ucpd->current % (8 * sizeof(uintptr_t));

            if (!(ucpd->tried[n] & m)) {
                peer = &ucpd->peers->peer[ucpd->current];

                if (!peer->down) {

                    if (peer->max_fails == 0
                            || peer->fails < peer->max_fails)
                    {
                        peer->temp_down = 0;
                        break;
                    }

                    if (now - peer->accessed > peer->fail_timeout) {
                        peer->fails = 0;
                        peer->temp_down = 0;
                        break;
                    }

                    /* temporary unavailable */
                    peer->temp_down = 1;

                } 

                ucpd->tried[n] |= m;
                pc->tries--;
            }

            if (pc->tries <= 0 || --i <= 0) {
                goto failed;
            }

            ucpd->current = 
                ngx_http_upstream_get_peer(ucpd);
        }

        ucpd->tried[n] |= m;
    }


    pc->sockaddr = peer->sockaddr;
    pc->socklen = peer->socklen;
    pc->name = &peer->name;

    /* ngx_unlock_mutex(ucpd->peers->mutex); */

    if (pc->tries == 1 && ucpd->peers->next) {
        pc->tries += ucpd->peers->next->number;

        /* backup servers' number must be less than the active server */
        n = ucpd->peers->next->number / (8 * sizeof(uintptr_t)) + 1;
        for (i = 0; i < n; i++) {
             ucpd->tried[i] = 0;
        }
    }

    return NGX_OK;

failed:

    peers = ucpd->peers;

    if (peers->next) {

        /* ngx_unlock_mutex(peers->mutex); */

        ngx_log_debug0(NGX_LOG_DEBUG_HTTP, pc->log, 0, "backup servers");

        ucpd->peers = peers->next;
        pc->tries = ucpd->peers->number;

        /* backup servers' number must be less than the active server */
        n = ucpd->peers->number / (8 * sizeof(uintptr_t)) + 1;
        for (i = 0; i < n; i++) {
             ucpd->tried[i] = 0;
        }

        rc = ngx_http_upstream_get_carp_peer(pc, ucpd);

        if (rc != NGX_BUSY) {
            return rc;
        }

        /* ngx_lock_mutex(peers->mutex); */
    }

    /* all peers failed, mark them as live for quick recovery */

    for (i = 0; i < peers->number; i++) {
        peers->peer[i].fails = 0;
    }

    /* ngx_unlock_mutex(peers->mutex); */

    pc->name = peers->name;

    return NGX_BUSY;
}


static ngx_uint_t
ngx_http_upstream_get_peer(ngx_http_upstream_carp_peer_data_t *ucpd)
{
    uintptr_t                       m;
    ngx_uint_t                      i, n, select = 0;
    double                          high_score = 0.0;
    ngx_http_upstream_carp_peer_t  *peer;

    peer = &ucpd->peers->peer[0];

    for (i = 0; i < ucpd->peers->number; i++) {

        if (peer[i].weight <= 0 || peer[i].load_factor <= 0.0) {
            continue;
        }

        n = i / (8 * sizeof(uintptr_t));
        m = (uintptr_t) 1 << i % (8 * sizeof(uintptr_t));

        /* get the highest score server which has not been tried. */
        if (!(ucpd->tried[n] & m)) {
            if (peer[i].score > high_score) {
                high_score = peer[i].score;
                select = i;
            }
        }
    }

    return select;
}


static void
ngx_http_upstream_free_carp_peer(ngx_peer_connection_t *pc, void *data,
    ngx_uint_t state)
{
    ngx_http_upstream_carp_peer_data_t  *ucpd = data;

    time_t                         now;
    ngx_http_upstream_carp_peer_t *peer;

    ngx_log_debug2(NGX_LOG_DEBUG_HTTP, pc->log, 0,
                   "free carp peer %ui %ui", pc->tries, state);

    if (state == 0 && pc->tries == 0) {
        return;
    }

    /* TODO: NGX_PEER_KEEPALIVE */

    if (ucpd->peers->single) {
        pc->tries = 0;
        return;
    }

    if (state & NGX_PEER_FAILED) {
        now = ngx_time();

        peer = &ucpd->peers->peer[ucpd->current];

        /* ngx_lock_mutex(ucpd->peers->mutex); */

        peer->fails++;
        peer->accessed = now;

        /* ngx_unlock_mutex(ucpd->peers->mutex); */
    }

    ucpd->current = ngx_http_upstream_get_peer(ucpd);

    if (pc->tries > 0) {
        pc->tries--;
    }
    
    ngx_log_debug2(NGX_LOG_DEBUG_HTTP, pc->log, 0,
                   "carp# free and tries 0x%p, current %ui", 
                   ucpd->tried[0], ucpd->current);

    /* ngx_unlock_mutex(ucpd->peers->mutex); */
}


#if (NGX_HTTP_SSL)

ngx_int_t
ngx_http_upstream_set_carp_peer_session(ngx_peer_connection_t *pc,
    void *data)
{
    ngx_http_upstream_carp_peer_data_t  *ucpd = data;

    ngx_int_t                     rc;
    ngx_ssl_session_t            *ssl_session;
    ngx_http_upstream_carp_peer_t  *peer;

    peer = &ucpd->peers->peer[ucpd->current];

    /* TODO: threads only mutex */
    /* ngx_lock_mutex(ucpd->peers->mutex); */

    ssl_session = peer->ssl_session;

    rc = ngx_ssl_set_session(pc->connection, ssl_session);

    ngx_log_debug2(NGX_LOG_DEBUG_HTTP, pc->log, 0,
                   "set session: %p:%d",
                   ssl_session, ssl_session ? ssl_session->references : 0);

    /* ngx_unlock_mutex(ucpd->peers->mutex); */

    return rc;
}


void
ngx_http_upstream_save_carp_peer_session(ngx_peer_connection_t *pc,
    void *data)
{
    ngx_http_upstream_carp_peer_data_t  *ucpd = data;

    ngx_ssl_session_t            *old_ssl_session, *ssl_session;
    ngx_http_upstream_carp_peer_t  *peer;

    ssl_session = ngx_ssl_get_session(pc->connection);

    if (ssl_session == NULL) {
        return;
    }

    ngx_log_debug2(NGX_LOG_DEBUG_HTTP, pc->log, 0,
                   "save session: %p:%d", ssl_session, ssl_session->references);

    peer = &ucpd->peers->peer[ucpd->current];

    /* TODO: threads only mutex */
    /* ngx_lock_mutex(ucpd->peers->mutex); */

    old_ssl_session = peer->ssl_session;
    peer->ssl_session = ssl_session;

    /* ngx_unlock_mutex(ucpd->peers->mutex); */

    if (old_ssl_session) {

        ngx_log_debug2(NGX_LOG_DEBUG_HTTP, pc->log, 0,
                       "old session: %p:%d",
                       old_ssl_session, old_ssl_session->references);

        /* TODO: may block */

        ngx_ssl_free_session(old_ssl_session);
    }
}

#endif


static char *
ngx_http_upstream_carp(ngx_conf_t *cf, ngx_command_t *cmd, void *conf)
{
    ngx_uint_t                         n;
    ngx_str_t                         *value, *url;
    ngx_http_script_compile_t          sc;
    ngx_http_upstream_srv_conf_t      *uscf;
    ngx_http_upstream_carp_str_init_t *hash_str;

    uscf = ngx_http_conf_get_module_srv_conf(cf, ngx_http_upstream_module);

    hash_str = ngx_pcalloc(cf->pool, sizeof(ngx_http_upstream_carp_str_init_t));
    if (hash_str == NULL) {
        return NGX_CONF_ERROR;
    }

    if (cf->args->nelts > 1) {
        value = cf->args->elts;

        url = &value[1];

        n = ngx_http_script_variables_count(url);

        if (n) {
            ngx_memzero(&sc, sizeof(ngx_http_script_compile_t));

            sc.cf = cf;
            sc.source = url;
            sc.lengths = &hash_str->lengths;
            sc.values = &hash_str->values;
            sc.variables = n;
            sc.complete_lengths = 1;
            sc.complete_values = 1;

            if (ngx_http_script_compile(&sc) != NGX_OK) {
                return NGX_CONF_ERROR;
            }
        }

        hash_str->carp_str.data = ngx_pstrdup(cf->pool, url);
        hash_str->carp_str.len = url->len;
    }

    /* It's a trick, avoid to modify the core upstream souce code. */
    uscf->peer.data = hash_str;

    uscf->peer.init_upstream = ngx_http_upstream_init_carp;

    uscf->flags = NGX_HTTP_UPSTREAM_CREATE
                  |NGX_HTTP_UPSTREAM_WEIGHT
                  |NGX_HTTP_UPSTREAM_MAX_FAILS
                  |NGX_HTTP_UPSTREAM_FAIL_TIMEOUT
                  |NGX_HTTP_UPSTREAM_DOWN;

    return NGX_CONF_OK;
}

