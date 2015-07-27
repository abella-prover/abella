(function(){
    var app = angular.module('main', ['ngCookies', 'ngSanitize']);

    var TokenIterator = ace.require('ace/token_iterator').TokenIterator;
    var Range = ace.require('ace/range').Range;

    var showPos = function(pos){ return pos.row + ':' + pos.column; };

    var follows = function(a, b){
        return a.row > b.row || (a.row == b.row && a.column >= b.column);
    };

    var strictlyFollows = function(a, b){
        return a.row > b.row || (a.row == b.row && a.column > b.column);
    };

    var clonePos = function(pos){
        if (pos)
            return { row: pos.row, column: pos.column };
        return { row: 0, column: 0 };
    };

    app.controller('AbellaController', ['$scope', function($scope){
        var __self = this;

        var aceTheme = 'ace/theme/eclipse';
        var makeEditor = function(key,mode,minLines,maxLines,id){
            var ed = ace.edit(id);
            ed.setTheme(aceTheme);
            ed.setOptions({autoScrollEditorIntoView: true, minLines: minLines, maxLines: maxLines});
            ed.getSession().setMode(mode);
            if(typeof(Storage) !== undefined){
                ed.$blockScrolling = Infinity;
                var cached = localStorage.getItem(key);
                if(cached !== null) ed.setValue(cached, -1);
                ed.on('change', function(){
                    // console.log(key + ' content saved');
                    localStorage.setItem(key, ed.getValue());
                });
            }
            ed.setHighlightActiveLine(false);
            ed.setShowPrintMargin(false);
            return ed;
        };
        var windowHeight = $(window).height();
        var maxLines = windowHeight > 1080 ? 60 : windowHeight > 800 ? 40 : 30;
        var sigEd = makeEditor('specSigEd','ace/mode/lprolog',5,maxLines,'spec-sig');
        var modEd = makeEditor('specModEd','ace/mode/lprolog',5,maxLines,'spec-mod');
        var thmEd = makeEditor('reasoningEd','ace/mode/abella',30,maxLines,'reasoning');
        $scope.refreshEditors = function(){
            [sigEd, modEd, thmEd].forEach(function(ed){
                ed.resize();
                ed.renderer.updateFull();
            });
        };

        $scope.devs = [
            { name: "--- λ-calculus Meta-Theory ---", disable: true },
            { name: "Type Uniqueness for STLC",
              sig: "examples/stlc.sig",
              mod: "examples/stlc.mod",
              thm: "examples/stlc-uniq.thm" },
            { name: "Evaluation",
              sig: "examples/eval.sig",
              mod: "examples/eval.mod",
              thm: "examples/eval.thm" },
            { name: "--- Proof Theory ---", disable: true },
            { name: "Cut-Admissibility",
              sig: "examples/cut.sig",
              mod: "examples/cut.mod",
              thm: "examples/cut.thm" },
            { name: "Meta-Theory of HH-ω",
              sig: "examples/empty.sig",
              mod: "examples/empty.mod",
              thm: "examples/hh_meta.thm" },
            { name: "--- POPLMark ---", disable: true },
            { name: "Part 1(a)",
              sig: "examples/poplmark-1a.sig",
              mod: "examples/poplmark-1a.mod",
              thm: "examples/poplmark-1a.thm" },
            { name: "Part 2(a)",
              sig: "examples/poplmark-2a.sig",
              mod: "examples/poplmark-2a.mod",
              thm: "examples/poplmark-2a.thm" },
            { name: "--- Process Calculus Meta-Theory ---", disable: true },
            { name: "Bisimulation for CCS",
              sig: "examples/ccs.sig",
              mod: "examples/ccs.mod",
              thm: "examples/ccs.thm" },
            { name: "Bisimulation for the π-Calculus",
              sig: "examples/pic.sig",
              mod: "examples/pic.mod",
              thm: "examples/pic.thm" },
        ];

        $scope.output = '';     // good

        var status;
        var resetStatus = function(){
            status = 'unknown';
        };
        resetStatus();

        var appendOutput = function(res, pristine){
            var output = pristine ? res.output :
                res.output.replace(/^([^\s]+ <)/gm,
                                   '<span class="prompt">$1</span>')
                .replace(/#back\./g, '&lt;undo&gt;');
            $scope.output += output; // good
            status = res.status;
        };

        var posAfter = function(pos){
            var doc = thmEd.getSession().getDocument();
            var row = doc.getLine(pos.row);
            return row.length === pos.column ?
                { row: pos.row + 1, column: 0 } :
            { row: pos.row, column: pos.column + 1 };
        };

        function History(pos){
            this.tip = clonePos(pos);
            this.past = [];
            this.marker = -1;
        }
        (function(){
            this.updateMarker = function(){
                if (this.marker != -1)
                    thmEd.getSession().removeMarker(this.marker);
                if (this.tip.row > 0 || this.tip.column > 0)
                    this.marker = thmEd.getSession().addMarker(
                        new Range(0, 0, this.tip.row, this.tip.column),
                        "processed", "text");
                else this.marker = -1;
            };
            this.showTip = function(){
                thmEd.moveCursorToPosition(this.tip);
                thmEd.getSelection().clearSelection();
                $scope.$digest();
            };
            this.reset = function(pos){
                this.tip = clonePos(pos);
                this.past = [];
                this.updateMarker();
            };
            this.push = function(pos){
                this.past.push(this.tip);
                this.tip = posAfter(pos);
                this.updateMarker();
            };
            this.pushCurrent = function(){
                this.push(thmEd.getCursorPosition());
            };
            this.pop = function(){
                if (this.past.length == 0) return undefined;
                var oldTip = clonePos(this.tip);
                this.tip = this.past.pop();
                this.updateMarker();
                return oldTip;
            };
            this.popTo = function(here){
                var backs = 0
                while(strictlyFollows(this.tip, here)){
                    this.pop();
                    backs ++;
                }
                return backs;
            };
        }).call(History.prototype);

        var hist = new History();

        this.resetOutput = function(){
            $scope.output = ''; // good
            resetStatus();
            hist.reset();
        };

        this.hasOutput = function(){
          return !($scope.output === ''); // good
        };

        this.getBackgroundClass = function(){
            switch(status){
            case 'unknown': return 'trace-unknown';
            case 'good':    return 'trace-success';
            default:        return 'trace-failure';
            }
        };

        this.select = function(dev){
            if (dev == null) return;
            // console.log('Loading: ' + dev.name);
            try {
                $.get(dev.sig, function(sigData){
                    $.get(dev.mod, function(modData){
                        $.get(dev.thm, function(thmData){
                            sigEd.setValue(sigData, -1);
                            modEd.setValue(modData, -1);
                            thmEd.setValue(thmData, -1);
                            $scope.refreshEditors();
                            __self.resetOutput();
                        });
                    });
                });
            } catch(err){
                console.log('Error loading ' + dev.name);
            }
        };

        this.clear = function(){
            sigEd.setValue('sig empty.', -1);
            modEd.setValue('module empty.', -1);
            thmEd.setValue('', -1);
            $scope.refreshEditors();
            __self.resetOutput();
        };

        var endOfDocument = function(){
            var doc = thmEd.getSession().getDocument();
            var row = doc.getLength() - 1;
            var column = doc.getLine(row).length;
            return { row: row, column: column };
        };

        var maybeResetAbella = function(){
            if(hist.tip.row == 0 && hist.tip.column == 0) {
                $scope.output = '';
                appendOutput(abella.reset(sigEd.getValue(), modEd.getValue()));
                $scope.$digest();
            }
        };

        this.batch = function(){
            this.resetOutput();

            var spec_sig = sigEd.getValue();
            var spec_mod = modEd.getValue();
            var thm = thmEd.getValue();

            appendOutput(abella.batch(spec_sig, spec_mod, thm), true);
        };

        var stepBackTo = function(here){
            var backs = hist.popTo(here);
            while (backs --> 0)
                appendOutput(abella.process1('#back.'));
        };

        thmEd.getSession().getDocument().on('change', function(obj){
            if(strictlyFollows(hist.tip, obj.start)){
                stepBackTo(obj.start);
                $scope.$digest();
            }
        });

        var stepForward = function(barrier){
            var text = '';
            var endPos = clonePos(hist.tip);
            var nextPos = posAfter(hist.tip);
            var tokIter = new TokenIterator(thmEd.getSession(), nextPos.row, nextPos.column);
            if (tokIter.getCurrentToken() === undefined)
                tokIter.stepForward();
            do {
                if (barrier !== null && strictlyFollows(endPos, barrier)) return null;
                var tok = tokIter.getCurrentToken();
                if (tok === undefined) return false;
                // console.log('Read: ' + JSON.stringify(tok));
                endPos = tokIter.getCurrentTokenPosition();
                if (!tok.type.match(/comment/)) text += ' ' + tok.value;
                if (tok.type === 'punctuation.dot') break;
            } while(tokIter.stepForward() !== null);
            text = text.replace(/\s+/g, ' ').replace(/\s+\./, '.').replace(/^\s+/, '');
            appendOutput(abella.process1(text));
            if (status === 'good')
                hist.push(endPos);
            return status === 'good';
        };

        var processUptoHere = function(block){
            maybeResetAbella();
            var here = thmEd.getCursorPosition();
            if (strictlyFollows(hist.tip, here))
                stepBackTo(here);
            else
                while (follows(here, hist.tip))
                    if(!stepForward (block ? here : null))
                        break;
            hist.showTip();
            $scope.$digest();
        };

        thmEd.commands.addCommands([
            { name: "processUptoHere",
              bindKey: { win: "Ctrl-Return", mac: "Command-Return" },
              exec: function(_ed){ processUptoHere(false) },
              readOnly: true,
              scrollIntoView: "animate",
            },
            { name: "processUptoHereBlocking",
              bindKey: { win: "Ctrl-Shift-Return", mac: "Command-Shift-Return" },
              exec: function(_ed){ processUptoHere(true) },
              readOnly: true,
              scrollIntoView: "animate",
            },
        ]);
    }]);

    app.controller('TabController', ['$cookies', '$document', '$scope', function($cookies, $document, $scope){
        this.active = parseInt($cookies.get('currentTab')) || 1;
        this.isSet = function(t){
            return this.active === t;
        };
        this.set = function(t){
            this.active = t;
            $cookies.put('currentTab', '' + this.active);
            $scope.refreshEditors();
        };
    }]);

    app.directive('scroll', function($timeout) {
        return {
            restrict: 'A',
            link: function(scope, element, attr) {
                scope.$watchCollection(attr.scroll, function(newVal) {
                    $timeout(function() {
                        element[0].scrollTop = element[0].scrollHeight;
                    });
                });
            }
        }
    });
})();
