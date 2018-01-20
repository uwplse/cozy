from threading import Thread
from http.server import HTTPServer, BaseHTTPRequestHandler

def handler_class(callback):
    class Handler(BaseHTTPRequestHandler):
        def do_GET(self):
            if self.path != "/":
                self.send_response(404)
                content = "not found"
                self.send_header("Content-Type", "text/plain")
                self.send_header("Content-Length", str(len(content)))
                self.end_headers()
                self.wfile.write(content.encode("utf-8"))
                return
            content = callback()
            self.send_response(200)
            self.send_header("Content-Type", "text/html")
            self.send_header("Content-Length", str(len(content)))
            self.end_headers()
            self.wfile.write(content.encode("ascii"))
    return Handler

class ProgressServer(HTTPServer):
    def __init__(self, callback, port=8080):
        super().__init__(('', port), handler_class(callback))
    def start_async(self):
        self.thread = Thread(target=self.serve_forever, daemon=True)
        self.thread.start()
    def join(self):
        self.shutdown()
        self.thread.join()
