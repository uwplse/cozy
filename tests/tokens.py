"""
Tests for tokenization.
"""

import unittest
from itertools import zip_longest

from cozy.parse import tokenize

def assert_token_stream_matches(s, *types):
    for tok, t in zip_longest(tokenize(s), types):
        assert tok.type == t

class TokenizerTests(unittest.TestCase):
    def test_ints(self):
        assert_token_stream_matches("0", 'NUM')
        assert_token_stream_matches("01", 'NUM')

    def test_floats(self):
        assert_token_stream_matches("1.0f", 'FLOAT')
        assert_token_stream_matches("0.1f", 'FLOAT')
        assert_token_stream_matches("0123.1321f", 'FLOAT')
        assert_token_stream_matches("72f", 'FLOAT')

    def test_math_expr(self):
        assert_token_stream_matches("7-6.0f", 'NUM', 'OP_MINUS', 'FLOAT')

    def test_tuple_field_access(self):
        assert_token_stream_matches("invariant foo.1 < 9",
            'KW_INVARIANT', 'WORD', 'OP_DOT', 'NUM', 'OP_LT', 'NUM')

        assert_token_stream_matches("invariant foo.1.4.f < 9",
            'KW_INVARIANT', 'WORD', 'OP_DOT', 'NUM', 'OP_DOT', 'NUM',
            'OP_DOT', 'WORD', 'OP_LT', 'NUM')

    def test_multiline_comments(self):
        assert_token_stream_matches("foo /* bar */ 1", 'WORD', 'NUM')
        assert_token_stream_matches("foo /* bar **/ 1", 'WORD', 'NUM')
        assert_token_stream_matches("foo /* bar ***/ 1", 'WORD', 'NUM')
        assert_token_stream_matches("foo /* \n bar \n ***/ 1", 'WORD', 'NUM')
        assert_token_stream_matches("foo /* \n bar /* / \n ***/ 1", 'WORD', 'NUM')
