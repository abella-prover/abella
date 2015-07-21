define("ace/mode/lprolog", ["require", "exports", "module", "ace/lib/oop", "ace/mode/text", "ace/mode/text_highlight_rules", "ace/mode/behaviour"], function(require, exports, module){

"use strict";

var oop = require("../lib/oop");
var TextMode = require("./text").Mode;
var TextHighlightRules = require("./text_highlight_rules").TextHighlightRules;
var Behaviour = require("./behaviour").Behaviour;

var LPrologHighlightRules = function(){
    this.$rules = {
        start: [ { include: '#comment' },
                 { include: '#keywords' },
                 { include: '#operators' } ],
        '#comment': [ { token: 'comment.line',
                        regex: /%.*$/ } ],
        '#operators': [ { token: 'keyword.operator',
                          regex: /->|=>|:-|<=|\\/ } ],
        '#keywords': [ { token: 'keyword.other',
                         regex: /\b(sig|module|end|kind|type|o)\b/ } ],
    };

    this.normalizeRules();
};

oop.inherits(LPrologHighlightRules, TextHighlightRules);

var Mode = function(){
    this.HighlightRules = LPrologHighlightRules;
    this.$behaviour = new Behaviour();
};

oop.inherits(Mode, TextMode);

(function(){
    this.type = "lprolog";
    this.getNextLineIndent = function(state, line, tab){
        return '';
    };
    this.$id = "ace/mode/lprolog";
}).call(Mode.prototype);

exports.Mode = Mode;

});
