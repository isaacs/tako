var util = require('util')
  , events = require('events')
  , crypto = require('crypto')
  , path = require('path')
  , url = require('url')
  , fs = require('fs')
  , util = require('util')
  , stream = require('stream')
  , qs = require('querystring')
  , http = require('http')
  , https = require('https')
  // Dependencies
  , routes = require('routes')
  , filed = require('filed')
  // Local Imports
  , handlebars = require('./handlebars')
  , rfc822 = require('./rfc822')
  , io = null
  , keygrip = require('keygrip')
  , Cookies = require('cookies')
  ;

try {
  io = require('socket.io')
} catch (er) {
  // oh well, no socket.io.
}

var cap = function (stream, limit) {
  if (!limit) limit = Infinity
  stream.caplimit = limit
  stream.bufferedData = []
  stream.bufferedLength = 0

  stream._capemit = stream.emit
  stream.emit = function () {
    if (arguments[0] === 'data') {
      stream.bufferedData.push(arguments)
      stream.bufferedLength += arguments[1].length
      if (stream.bufferedLength > stream.caplimit) {
        stream.pause()
      }
    } else if (arguments[0] === 'end') {
      stream.ended = true
    } else {
      stream._capemit.apply(stream, arguments)
    }
  }

  stream.release = function () {
    stream.emit = stream._capemit
    while (stream.bufferedData.length) {
      stream.emit.apply(stream, stream.bufferedData.shift())
    }
    if (stream.ended) stream.emit('end')
    if (stream.readable) stream.resume()
  }

  return stream
}

module.exports = function (options) {
  return new Application(options)
}

function BufferResponse (buffer, mimetype) {
  if (!Buffer.isBuffer(buffer)) this.body = new Buffer(buffer)
  else this.body = buffer
  this.timestamp = rfc822.getRFC822Date(new Date())
  this.etag = crypto.createHash('md5').update(buffer).digest("hex")
  this.mimetype = mimetype
  this.cache = true
}
BufferResponse.prototype.request = function (req, resp) {
  if (resp._header) return // This response already started
  resp.setHeader('content-type', this.mimetype)
  if (this.cache) {
    resp.setHeader('last-modified',  this.timestamp)
    resp.setHeader('etag', this.etag)
  }
  if (req.method !== 'GET' && req.method !== 'HEAD') {
    resp.statusCode = 405
    return (resp._end ? resp._end : resp.end).call(resp)
  }
  if (this.cache && 
      req.headers['if-none-match'] === this.etag ||
      req.headers['if-modified-since'] === this.timestamp
      ) {
    resp.statusCode = 304
    return (resp._end ? resp._end : resp.end).call(resp)
  }
  resp.statusCode = this.statusCode || 200
  ;(resp._write ? resp._write : resp.write).call(resp, this.body)
  return (resp._end ? resp._end : resp.end).call(resp)
}

function Page (templatename) {
  var self = this
  self.promises = {}
  self.counter = 0
  self.results = {}
  self.dests = []
  self.on('pipe', function (src) {
    if (src.method && (src.method === 'PUT' || src.method == 'POST')) {
      var p = self.promise('body')
      src.on('error', function (e) {
        p(e)
      })
      src.on('body', function (body) {
        p(null, body)
      })
      if (src.json) {
        var jp = self.promise('json')
        src.on('json', function (obj) {
          jp(null, obj)
        })
      }
    }
  })
  process.nextTick(function () {
    if (self.listeners('error').length === 0) {
      self.on('error', function (err) {
        if (self.dests.length) {
          self.dests.forEach(function (resp) {
            if (resp.error) return resp.error(err)
          })
        } else {
          self.application.logger.error('Page::Uncaught Error:')
          self.application.logger.error(e)
        }
      })
    }
    
    if (templatename) {
      self.template(templatename)
    }
    if (self.counter === 0) self.emit('finish', self.results)
  })
}
util.inherits(Page, stream.Stream)
Page.prototype.promise = function (name, cb) {
  if (name === 'error') throw new Error("You cannot name a promise 'error'")
  if (name === 'finish') throw new Error("You cannot name a promise 'finish'")
  if (name === 'resolved') throw new Error("You cannot name a promise 'resolved'")
  var self = this;
  self.counter += 1
  self.promises[name] = function (e, result) {
    self.emit('resolved', name, e, result)
    if (e) {
      e.promise = name
      return self.emit('error', e, name)
    }
    self.emit(name, result)
    self.results[name] = result
    self.counter = self.counter - 1
    if (self.counter === 0) self.emit('finish', self.results)
  }
  if (cb) self.on(name, cb)
  return self.promises[name]
}
Page.prototype.event = function (name, cb) {
  var p = this.promise(name, cb)
    , r = function (r) { p(null, r) }
    ;
  return r
}
Page.prototype.pipe = function (dest) {
  this.dests.push(dest)
}
Page.prototype.write = function () {}
Page.prototype.end = function () {}
Page.prototype.destroy = function () {}

// Templates implementation
function Templates (app) {
  this.files = {}
  this.loaded = true
  this.after = {}
  this.app = app
  this.names = {}
  this.loading = 0
  this.tempcache = {}
  this.Template = function (text) {
    this.compiled = handlebars.compile(text)
  }
  this.Template.prototype.render = function (obj) {
    return new Buffer(this.compiled(obj))
  }
}
util.inherits(Templates, events.EventEmitter)
Templates.prototype.get = function (name, cb) {
  var self = this
  
  if (name.indexOf(' ') !== -1 || name[0] === '<') {
    process.nextTick(function () {
      if (!self.tempcache[name]) {
        self.tempcache[name] = new self.Template(name)
      }
      cb(null, self.tempcache[name])
    })
    return
  }
  
  function finish () {
    if (name in self.names) {
      cb(null, self.files[self.names[name]])
    } else {
      cb(new Error("Cannot find template"))
    }
  }
  if (this.loaded) {
    process.nextTick(finish)
  } else {
    self.once('loaded', finish)
  }
}
Templates.prototype.directory = function (dir) {
  var self = this
  this.loaded = false
  this.loading += 1
  loadfiles(dir, function (e, filemap) {
    if (e) return self.emit('error', e)
    for (i in filemap) {
      self.files[i] = new self.Template(filemap[i])
      self.names[path.basename(i)] = i
      self.names[path.basename(i, path.extname(i))] = i
    }
    self.loading -= 1
    self.loaded = true
    if (self.loading === 0) self.emit('loaded')
  })
} 

function loadfiles (f, cb) {
  var filesmap = {}
  fs.readdir(f, function (e, files) {
    if (e) return cb(e)
    var counter = 0
    files.forEach(function (filename) {
      counter += 1
      fs.stat(path.join(f, filename), function (e, stat) {
        if (stat.isDirectory()) {
          loadfiles(path.join(f, filename), function (e, files) {
            if (e) return cb(e)
            for (i in files) {
              filesmap[i] = files[i]
            }
            counter -= 1
            if (counter === 0) cb(null, filesmap)
          })
        } else {
          fs.readFile(path.join(f, filename), function (e, data) {
            filesmap[path.join(f, filename)] = data.toString()
            counter -= 1
            if (counter === 0) cb(null, filesmap)
          })
        }
      })
    })
  })
}

function Application (options) {
  var self = this
  if (!options) options = {}
  self.options = options

  if (options.keys) {
    self.keys = new KeyGrip(options.keys)
  }

  self._plugins = {}
  self._pluginCount = 0

  self.addHeaders = {}
  if (self.options.logger) {
    self.logger = self.options.logger
  } 
  
  self.onRequest = function (req, resp) {
    if (self.logger.info) self.logger.info('Request', req.url, req.headers)
    // Opt out entirely if this is a socketio request
    if (self.socketio && req.url.slice(0, '/socket.io/'.length) === '/socket.io/') {
      return self._ioEmitter.emit('request', req, resp)
    }
    
    if (options.cookies !== false) {
      req.cookies = resp.cookies = new Cookies(req, resp, self.keys)
    }

    for (i in self.addHeaders) {
      resp.setHeader(i, self.addHeaders[i])
    }
    
    req.accept = function () {
      if (!req.headers.accept) return '*/*'
      var cc = null
      var pos = 99999999
      for (var i=arguments.length-1;i!==-1;i--) {
        var ipos = req.headers.accept.indexOf(arguments[i])
        if ( ipos !== -1 && ipos < pos ) cc = arguments[i]
      }
      return cc
    }

    resp.error = function (err) {
      if (typeof(err) === "string") err = {message: err}
      if (!err.statusCode) err.statusCode = 500
      resp.statusCode = err.statusCode || 500
      self.logger.log('error %statusCode "%message "', err)
      resp.end(err.message || err) // this should be better
    }
    
    resp.notfound = function (log) {
      if (log) self.logger.log(log)
      self.notfound(req, resp)
    }

    // Get all the parsed url properties on the request
    // This is the same style express uses and it's quite nice
    var parsed = url.parse(req.url)
    for (i in parsed) {
      req[i] = parsed[i]
    }
    
    if (req.query) req.qs = qs.parse(req.query)

    req.route = self.router.match(req.pathname)

    if (!req.route) return self.notfound(req, resp)

    req.params = req.route.params

    var onWrites = []
    resp._write = resp.write
    resp.write = function () {
      if (resp.statusCode === 404 && self._notfound) {
        return self._notfound.request(req, resp)
      }
      if (onWrites.length === 0) return resp._write.apply(resp, arguments)
      var args = arguments
      onWrites.forEach(function (onWrite) {
        var c = onWrite.apply(resp, args)
        if (c !== undefined) args[0] = c
      })
      return resp._write.apply(resp, args)
    }

    // Fix for node's premature header check in end()
    resp._end = resp.end
    resp.end = function (chunk) {
      if (resp.statusCode === 404 && self._notfound) {
        return self._notfound.request(req, resp)
      }
      if (chunk) resp.write(chunk)
      resp._end()
      self.logger.info('Response', resp.statusCode, req.url, resp._headers)
    }

    // cookie support
    req.cookies = resp.cookies = new Cookies(req, resp, keygrip)


    cap(req)
    // first, any 'request' listeners get a crack at things.
    // this is enough for things that don't need to do IO, since
    // we don't wait for them.
    self.emit('request', req, resp)

    self._plug(req, resp, function () {
      req.route.fn(req, resp)
      req.release()

      if (req.listeners('body').length) {
        var buffer = ''
        req.on('data', function (chunk) {
          buffer += chunk
        })
        req.on('end', function (chunk) {
          if (chunk) buffer += chunk
          req.emit('body', buffer)
        })
      }
    })

  }

  self.router = new routes.Router()
  self.on('newroute', function (route) {
    self.router.addRoute(route.path, function (req, resp, authHandler) {
      route.handler(req, resp, authHandler)
    })
  })
  
  self.templates = new Templates(self)
  
  // Default to having json enabled
  self.on('request', JSONRequestHandler)
  
  // setup servers
  self.http = options.http || {}
  self.https = options.https || {}
  if (io) {
    self.socketio = options.socketio === undefined ? {} : options.socketio
    if (!self.socketio.logger && self.logger) {
      self.socketio.logger = self.logger
    }
  } else if (options.socketio) {
    throw new Error('socket.io is not available');
  }
  
  self.httpServer = http.createServer()
  self.httpsServer = https.createServer(self.https)
  
  self.httpServer.on('request', self.onRequest)
  self.httpsServer.on('request', self.onRequest)
  
  var _listenProxied = false
  var listenProxy = function () {
    if (!_listenProxied && self._ioEmitter) self._ioEmitter.emit('listening')
    _listenProxied = true
  }
  
  self.httpServer.on('listening', listenProxy)
  self.httpsServer.on('listening', listenProxy)
  
  if (io && self.socketio) {
    // setup socket.io
    self._ioEmitter = new events.EventEmitter()
    
    self.httpServer.on('upgrade', function (request, socket, head) {
      self._ioEmitter.emit('upgrade', request, socket, head)
    })
    self.httpsServer.on('upgrade', function (request, socket, head) {
      self._ioEmitter.emit('upgrade', request, socket, head)
    })
    
    self.socketioManager = new io.Manager(self._ioEmitter, self.socketio)
    self.sockets = self.socketioManager.sockets
  }
  
  if (!self.logger) {
    self.logger = 
      { log: console.log
      , error: console.error
      , info: function () {}
      }
  }
}
util.inherits(Application, events.EventEmitter)

// A plugin is like a 'request' event handler, except with a 'done'
// callback.  Resume to the route handler after all plugins are finished,
// but they do not wait for one another.
Application.prototype.plugin = function (name, handler) {
  if (this._plugins[name]) {
    // XXX too forceful?
    throw new Error('Already have a plugin named '+name)
  }

  this._plugins[name] = handler
  this._pluginCount ++
}

Application.prototype.unplug = function (name) {
  delete this._plugins[name]
  this._pluginCount --
}

Application.prototype._plug = function (req, res, cb) {
  if (this._pluginCount === 0) return cb()

  var l = this._pluginCount
    , self = this
    ;

  Object.keys(self._plugins).forEach(function (name) {
    var plug = self._plugins[name]
    plug(req, res, function (er) {
      if (er) req.pluginErrors[name] = er
      else req.pluginLoaded[name] = true
      if (-- l === 0) return cb()
    })
  })

}

Application.prototype.auth = function (handler) {
  this.plugin("auth", handler)
}

Application.prototype.session = function (handler) {
  this.plugin("session", handler)
}

Application.prototype.addHeader = function (name, value) {
  this.addHeaders[name] = value
}

Application.prototype.route = function (path, cb) {
  var r = new Route(path, this)
  if (cb) r.on('request', cb)
  return r
}
Application.prototype.middle = function (mid) {
  throw new Error('Middleware is dumb. Just listen to the app "request" event.')
}

Application.prototype.listen = function (createServer, port, cb) {
  var self = this
  if (!cb) {
    cb = port
    port = createServer
  }
  self.server = createServer(function (req, resp) {
    self.onRequest(req, resp)
  })
  self.server.listen(port, cb)
  return this
}
Application.prototype.close = function (cb) {
  var counter = 1
    , self = this
    ;
  function end () {
    counter = counter - 1
    self.emit('close')
    if (io && self.socketio) {
      self._ioEmitter.emit('close')
    }
    if (counter === 0 && cb) cb()
  }
  if (self.httpServer._handle) {
    counter++
    self.httpServer.once('close', end)
    self.httpServer.close()
  }
  if (self.httpsServer._handle) {
    counter++
    self.httpsServer.once('close', end)
    self.httpsServer.close()
  }
  end()
  return self
}
Application.prototype.notfound = function (req, resp) {
  if (!resp) {
    if (typeof req === "string") {
      if (req[0] === '/') req = new BufferResponse(fs.readFileSync(req), 'text/html')
      else req = new BufferResponse(req, 'text/html')
    } else if (typeof req === "function") {
      this._notfound = {}
      this._notfound.request = function (r, resp) {
        if (resp._write) resp.write = resp._write
        if (resp._end) resp.end = resp._end
        req(r, resp)
      }
      return
    } else if (typeof req === 'object') {
      req = new BufferResponse(JSON.stringify(req), 'application/json')
    }
    req.statusCode = 404
    req.cache = false
    this._notfound = req
    return
  }
  
  if (resp._header) return // This response already started
  
  if (this._notfound) return this._notfound.request(req, resp)
  
  var cc = req.accept('text/html', 'application/json', 'text/plain', '*/*') || 'text/plain'
  if (cc === '*/*') cc = 'text/plain'
  resp.statusCode = 404
  resp.setHeader('content-type', cc)
  if (cc === 'text/html') {
    body = '<html><body>Not Found</body></html>'
  } else if (cc === 'application/json') {
    body = JSON.stringify({status:404, reason:'not found', message:'not found'})
  } else {
    body = 'Not Found'
  }
  resp.end(body)
}
Application.prototype.auth = function (handler) {
  if (!handler) return this.authHandler
  this.authHandler = handler
}
Application.prototype.page = function () {
  var page = new Page()
    , self = this
    ;
  page.application = self
  page.template = function (name) {    
    var p = page.promise("template")
    self.templates.get(name, function (e, template) {
      if (e) return p(e)
      if (p.src) p.src.pipe(template)
      page.on('finish', function () {
        process.nextTick(function () {
          var text = template.render(page.results)
          page.dests.forEach(function (d) {
            if (d._header) return // Don't try to write to a response that's already finished
            if (d.writeHead) {
              d.statusCode = 200
              d.setHeader('content-type', page.mimetype || 'text/html')
              d.setHeader('content-length', text.length)
            }
            d.write(text)
            d.end()
          })
        })
      })
      p(null, template)
    })
  }
  return page
}

module.exports.JSONRequestHandler = JSONRequestHandler
function JSONRequestHandler (req, resp) {
  var orig = resp.write
  resp.write = function (chunk) {
    if (resp._header) return orig.call(this, chunk) // This response already started
    // bail fast for chunks to limit impact on streaming
    if (Buffer.isBuffer(chunk)) return orig.call(this, chunk)
    // if it's an object serialize it and set proper headers
    if (typeof chunk === 'object') {
      chunk = new Buffer(JSON.stringify(chunk))
      resp.setHeader('content-type', 'application/json')
      resp.setHeader('content-length', chunk.length)
      if (!resp.statusCode && (req.method === 'GET' || req.method === 'HEAD')) {
        resp.statusCode = 200
      }
    }
    return orig.call(resp, chunk)
  }
  if (req.method === "PUT" || req.method === "POST") {
    if (req.headers['content-type'] === 'application/json') {
      req.on('body', function (body) {
        req.emit('json', JSON.parse(body))
      })
    }
  }
}


function Route (path, application) {
  // This code got really crazy really fast.
  // There are a lot of different states that close out of other logic.
  // This could be refactored but it's hard because there is so much
  // cascading logic.
  var self = this
  self.path = path
  self.app = application
  self.byContentType = {}



  var returnEarly = function (req, resp, keys, authHandler) {
    if (self._events && self._events['request']) {
      if (authHandler) {
        cap(req)
        authHandler(req, resp, function (user) {
          if (resp._header) return // This response already started
          req.user = user
          if (self._must && self._must.indexOf('auth') !== -1 && !req.user) {
            resp.statusCode = 403
            resp.setHeader('content-type', 'application/json')
            resp.end(JSON.stringify({error: 'This resource requires auth.'}))
            return
          }
          self.emit('request', req, resp)
          req.release()
        })
      } else {
        if (resp._header) return // This response already started
        if (self._must && self._must.indexOf('auth') !== -1 && !req.user) {
          resp.statusCode = 403
          resp.setHeader('content-type', 'application/json')
          resp.end(JSON.stringify({error: 'This resource requires auth.'}))
          return
        }
        self.emit('request', req, resp)
      }
    } else {
      if (resp._header) return // This response already started
      resp.statusCode = 406
      resp.setHeader('content-type', 'text/plain')
      resp.end('Request does not include a valid mime-type for this resource: '+keys.join(', '))
    }
  }

  self.handler = function (req, resp, authHandler) {
    if (self._methods && self._methods.indexOf(req.method) === -1) {
      resp.statusCode = 405
      resp.end('Method not Allowed.')
      return
    }
    
    self.emit('before', req, resp)
    if (self.authHandler) {
      authHandler = self.authHandler
    }

    var keys = Object.keys(self._byContentType).concat(['*/*'])
    if (req.method !== 'PUT' && req.method !== 'POST') {
      var cc = req.accept.apply(req, keys)
    } else {
      var cc = req.headers['content-type']
    }

    if (!cc) return returnEarly(req, resp, keys, authHandler)
    if (cc === '*/*') {
      var h = this.byContentType[Object.keys(this.byContentType)[0]]
    } else {
      var h = this.byContentType[cc]
    }
    if (!h) return returnEarly(req, resp, keys, authHandler)
    if (resp._header) return // This response already started
    resp.setHeader('content-type', cc)

    var run = function () {
      if (h.request) {
        return h.request(req, resp)
      }
      if (h.pipe) {
        req.pipe(h)
        h.pipe(resp)
        return
      }
      h.call(req.route, req, resp)
    }

    if (authHandler) {
      cap(req)
      authHandler(req, resp, function (user) {
        req.user = user
        if (self._must && self._must.indexOf('auth') !== -1 && !req.user) {
          if (resp._header) return // This response already started
          resp.statusCode = 403
          resp.setHeader('content-type', 'application/json')
          resp.end(JSON.stringify({error: 'This resource requires auth.'}))
          return
        }
        run()
        req.release()
      })
    } else {
      if (resp._header) return // This response already started
      if (self._must && self._must.indexOf('auth') !== -1) {
        resp.statusCode = 403
        resp.setHeader('content-type', 'application/json')
        resp.end(JSON.stringify({error: 'This resource requires auth.'}))
        return
      }
      run()
    }

  }
  application.emit('newroute', self)
}
util.inherits(Route, events.EventEmitter)


// requests that should never SEND a request body to us
var noBodyReqs = [ 'GET', 'HEAD', 'DELETE', 'TRACE', 'DELETE' ]

// route.contentTypes('text/json', 'application/json', jsonUploadHandler)
Route.prototype.contentTypes = function () {
  var contentTypes = new Array(arguments.length)
    , handler
  for (var i = 0; i < contentTypes.length; i ++) {
    contentTypes[i] = arguments[i]
  }
  if (typeof contentTypes[contentTypes.length-1] !== 'string') {
    handler = makeHandler(contentTypes.pop())
  }
  if (!this._contentTypes) {
    this._contentTypes = contentTypes
  } else {
    this._contentTypes = this._contentTypes.concat(contentTypes)
  }

  this.on('request', function (req, res) {
    // not relevant for reqs where no body is present
    if (noBodyReqs.indexOf(req) !== -1 || !req.contentLength) {
      return
    }

    var ct = req.headers['content-type']
    if (this._contentTypes.indexOf(ct) === -1) {
      res.error(415)
    }
    if (handler && !req.handler && contentTypes.indexOf(ct) !== -1) {
      req.handler = handler
    }
  })
}

Route.prototype.maxLength = function (n) {
  if (typeof n !== 'number') {
    throw new Error('please specify length in bytes for maxLength')
  }
  return this.on('request', function (req, res) {
    var len = +(req.headers['content-length'])
    if (isNaN(len)) return res.error(411)
    if (len > n) return res.error(413)
  })
}

// route.methods('POST', 'PUT', handler).methods('GET', 'HEAD', otherhandler)
Route.prototype.methods = function () {
  var handler
    , methods = new Array(arguments.length)
  for (var i = 0; i < methods.length; i ++) {
    methods[i] = arguments[i]
  }
  if (typeof methods[methods.length-1] !== 'string') {
    handler = makeHandler(methods.pop())
  }

  if (!this._methods) {
    this._methods = methods
  } else {
    this._methods = this._methods.concat(methods)
  }

  return this.on('request', function (req, res) {
    if (this._methods.indexOf(req.method) === -1) {
      res.error(405)
    }
    if (handler && !req.handler && methods.indexOf(req.method) !== -1) {
      req.handler = handler
    }
  })
}

// r.accepts('application/json', sendJson).accepts('text/html', sendHTML)
Route.prototype.accepts = function () {
  var accepts = new Array(arguments.length)
  for (var i = 0; i < accepts.length; i ++) {
    accepts[i] = arguments[i]
  }
  if (typeof accepts[accepts.length-1] !== 'string') {
    handler = makeHandler(accepts.pop())
  }

  if (!this._accepts) {
    this._accepts = accepts
  } else {
    this._accepts = this._accepts.concat(accepts)
  }

  return this.on('request', function (req, res) {
    if (!req.accepts(this._accepts)) {
      res.error(406)
    }
    if (handler && !req.handler && accepts.indexOf(req.method) !== -1) {
      req.handler = handler
    }
  })
}


Route.prototype.json = function (cb) {
  return this.accepts('application/json', 'application/x-json', 'text/json', makeHandler(cb))
}

// Route.prototype.json = function (cb) {
//   if (Buffer.isBuffer(cb)) cb = new BufferResponse(cb, 'application/json')
//   else if (typeof cb === 'object') cb = new BufferResponse(JSON.stringify(cb), 'application/json')
//   else if (typeof cb === 'string') {
//     if (cb[0] === '/') cb = filed(cb)
//     else cb = new BufferResponse(cb, 'application/json')
//   }
//   this.byContentType['application/json'] = cb
//   return this
// }
Route.prototype.html = function (cb) {
  return this.accepts('text/html', '*/*', makeHandler(cb))
}

// interpret cb as some sort of handler.
//
// route.json(function (req, res) { ... }) // you handle the json
// route.json(404) // couldn't find your json.
// route.json(410) // json is gone.  stop asking.
// route.json({ok: true}) // jsonify
// route.json('{"ok":true}') // return this exact json
// route.json(new Buffer('{"ok":true}')) // return this exact json
// route.json('/path/to/foo.json') // send this file
// If none of these match, returns null, which means 'no handler'
function makeHandler (cb) {
  if (cb instanceof BufferResponse) {
    // already a handler
    return cb
  }

  if (typeof cb === 'function') {
    return cb.request = cb
  }

  if (typeof cb === 'number') {
    return function (req, res) {
      return res.error(cb)
    }
  }
  if (Buffer.isBuffer(cb)) {
    return new BufferResponse(cb, 'application/json')
  }
  if (typeof cb === 'object') {
    return new BufferResponse(JSON.stringify(cb), 'application/json')
  }
  if (typeof cb === 'string') {
    if (cb[0] === '/') return filed(cb)
    return new BufferResponse(cb, 'application/json')
  }
  return null
}

Route.prototype.text = function (cb) {
  return this.accepts('text/plain', '*/*', cb)
}

Route.prototype.file = function (filepath) {
  return this.on('request', function (req, resp) {
    var f = filed(filepath)
    req.pipe(f)
    f.pipe(resp)
  })
}

Route.prototype.files = function (filepath) {
  return this.on('request', function (req, resp) {
    req.route.splats.unshift(filepath)
    var p = path.join.apply(path.join, req.route.splats)
    if (p.slice(0, filepath.length) !== filepath) {
      resp.statusCode = 403
      return resp.end('Naughty Naughty!')
    }
    var f = filed(p)
    req.pipe(f)
    f.pipe(resp)
  })
}

Route.prototype.auth = function () {
  // if auth is not available, then do the login dance.
  // auth could be implemented as either a plugin that does some IO,
  // or as a simple basic auth handler.
  return this.must('auth', 401)
}

// list out the plugins that must successfully load.
Route.prototype.must = function (thing, orelse) {
  orelse = makeHandler(orelse || 400)
  return this.on('request', function (req, res) {
    // defer to 'request' event, since we don't know
    // plugins might be added after the route is added
    var when = 'pluginsDone'
    if (this.app._plugins[thing]) {
      when = 'plugin:' + thing
    } else {
      // not the name of a plugin.
      // should be set by a request handler, before pluginsStart happens.
      when = 'pluginsStart'
    }
    req.on(when, function () {
      if (!req[thing]) req.handler = orelse
    })
  })
}

function ServiceError(msg) {
  this.message = msg
  if (Error.captureStackTrace) {
    Error.captureStackTrace(this, ServiceError);
  }
}
util.inherits(ServiceError, Error)
ServiceError.prototype.constructor = ServiceError
ServiceError.prototype.name = 'ServiceError'

module.exports.ServiceError = ServiceError

