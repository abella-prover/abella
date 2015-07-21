define("ace/mode/abella", ["require", "exports", "module", "ace/lib/oop", "ace/mode/text", "ace/mode/text_highlight_rules", "ace/mode/behaviour"], function(require, exports, module){

"use strict";

var oop = require("../lib/oop");
var TextMode = require("./text").Mode;
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;
var Behaviour = require("./behaviour").Behaviour;

var AbellaHighlightRules = function(){
    this.$rules = {
        start: [ { include: '#comment' },
                 { include: '#lprolog_keywords' },
                 { include: '#lprolog_operators' },
                 { include: '#abella_top_keywords' },
                 { include: '#abella_constants' },
                 { include: '#abella_proof_keywords' },
                 { include: '#abella_bad_proof_keywords' },
                 { include: '#abella_operators' } ],
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
        '#lprolog_operators': [
            { token: 'keyword.operator', regex: /->|=>|:-|<=|\\|::/ }
        ],
        '#lprolog_keywords': [
            { token: 'keyword.other.spec', regex: /\b(sig|module|end|kind|type|o)\b/ }
        ],
        '#abella_top_keywords': [
            { token: 'keyword.other.abella',
              regex: /\b(Close|CoDefine|Define|Import|Kind|Query|Quit|Schema|Set|Show|Specification|Theorem|Type)\b/ }
        ],
        '#abella_constants': [
            { token: 'constant.buildin',
              regex: /\b(forall|exists|nabla|true|false)\b/ }
        ],
        '#abella_proof_keywords': [
            { token: 'keyword.other.proof',
              regex: /\b(abbrev|accum|accumulate|all|apply|as|assert|backchain|by|case|clear|coinduction|cut|from|induction|inst|intros|keep|left|monotone|on|permute|pick|rename|right|search|split|to|unabbrev|unfold|with|witness)\b/ }
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
