ace.define("ace/mode/abella", ["require", "exports", "module", "ace/lib/oop", "ace/mode/text", "ace/mode/text_highlight_rules", "ace/mode/behaviour"], function(require, exports, module){

"use strict";

var oop = require("../lib/oop");
var TextMode = require("./text").Mode;
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;
var Behaviour = require("./behaviour").Behaviour;

var AbellaHighlightRules = function(){
    this.$rules = {
        start: [ { include: '#comment' },
                 { include: '#dot' },
                 { include: '#qstring' },
                 { include: '#identifiers' },
                 { include: '#lprolog_keywords' },
                 { include: '#abella_operators' },
                 { include: '#lprolog_operators' },
                 { include: '#abella_top_keywords' },
                 { include: '#abella_constants' },
                 { include: '#abella_proof_keywords' },
                 { include: '#abella_bad_proof_keywords' },
               ],
        '#comment': [
            { token: ['punctuation.definition.comment', 'comment.line.percentage'],
              regex: /(%)(.*$)/ },
            { token: 'punctuation.definition.comment',
              regex: '/\\*',
              push: [
                  { token: 'punctuation.definition.comment',
                    regex: '\\*/',
                    next: 'pop' },
                  { defaultToken: 'comment.block' }
              ] }
        ],
        '#dot': [
            { token: 'punctuation.dot',
              regex: /\./ },
        ],
        '#qstring': [
            { token: 'string',
              regex: /"(?:(?:\\.)|[^"\\])*"/ },
        ],
        '#identifiers': [
            { token: 'random_identifier',
              regex: /[`\\?$^][A-Za-z0-9^=`\\?$0-9_\/\*@+#!*~-]*/ },
        ],
        '#lprolog_operators': [
            { token: 'keyword.operator', regex: /->|=>|:-|<=|\\|::/ }
        ],
        '#lprolog_keywords': [
            { token: 'keyword.other.spec', regex: /\b(sig|module|end|kind|type|o|olist)\b/ }
        ],
        '#abella_top_keywords': [
            { token: 'keyword.other.abella',
              regex: /\b(Close|CoDefine|Define|Import|Kind|Query|Quit|Schema|Set|Show|Specification|Split|Theorem|Type)\b/ }
        ],
        '#abella_constants': [
            { token: 'constant.buildin',
              regex: /\b(forall|exists|nabla|true|false|prop)\b/ }
        ],
        '#abella_proof_keywords': [
            { token: 'keyword.other.proof',
              regex: /\b(abbrev|accum|accumulate|apply|as|assert|backchain|by|case|clear|coinduction|cut|from|induction|inst|intros|left|monotone|on|permute|pick|rename|right|search|split|to|unabbrev|unfold|with|witness)\b/ }
        ],
        '#abella_bad_proof_keywords': [
            { token: 'invalid.illegal',
              regex: '\b(skip|abort|undo)\b' }
        ],
        '#abella_operators': [
            { token: 'keyword.operator',
              regex: '\\\\/|/\\\\|:=|=|\\{|\\}|\\[|\\]|\\|-' }
        ]
    };

    this.normalizeRules();
};

oop.inherits(AbellaHighlightRules, TextHighlightRules);

var Mode = function(){
    this.HighlightRules = AbellaHighlightRules;
    this.$behaviour = new Behaviour();
};

oop.inherits(Mode, TextMode);

(function(){
    this.type = "abella";
    this.getNextLineIndent = function(state, line, tab){
        return '';
    };
    this.$id = "ace/mode/abella";
}).call(Mode.prototype);

exports.Mode = Mode;

});
