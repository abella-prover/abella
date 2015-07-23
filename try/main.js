(function(){
    var app = angular.module('main', ['ngCookies']);

    var TokenIterator = ace.require('ace/token_iterator').TokenIterator;
    var Range = ace.require('ace/range').Range;

    var clonePos = function(pos){
        return { row: pos.row, column: pos.column };
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
        var refreshEditors = function(){
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

        $scope.output = '';

        var status;
        var resetStatus = function(){
            status = 'unknown';
        };
        resetStatus();

        var processedTo;
        var resetProcessedTo = function(){
            processedTo = { row: 0, column: 0 };
        };
        resetProcessedTo();

        var markers;
        var resetMarkers = function(){
            markers = { current: -1 };
        };
        resetMarkers();

        var clearMarkers = function(){
            if (markers.current > 0)
                thmEd.getSession().removeMarker(markers.current);
            resetMarkers();
        }

        this.resetOutput = function(){
            $scope.output = '';
            resetStatus();
            resetProcessedTo();
            clearMarkers();
        };

        this.hasOutput = function(){
          return !($scope.output === '');
        };

        this.getBackground = function(){
            switch(status){
            case 'unknown': return 'text-muted';
            case 'good':    return 'text-success';
            default:        return 'text-danger';
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
                            refreshEditors();
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
            refreshEditors();
            __self.resetOutput();
        };

        var endOfDocument = function(){
            var doc = thmEd.getSession().getDocument();
            var row = doc.getLength() - 1;
            var column = doc.getLine(row).length;
            return { row: row, column: column };
        };

        var showPos = function(pos){ return pos.row + ':' + pos.column; };

        var updateProcessDisplay = function(){
            // console.log('Creating mark from 0:0 to ' + showPos(processedTo));
            clearMarkers();
            markers.current =
                thmEd.getSession().addMarker(
                    new Range(0, 0, processedTo.row, processedTo.column + 1),
                    "processed", "text");

            thmEd.moveCursorToPosition(processedTo);
            thmEd.getSelection().clearSelection();
            if (processedTo.row > thmEd.renderer.getScrollBottomRow())
                thmEd.renderer.scrollCursorIntoView();

            $scope.$digest();
        };

        this.batch = function(){
            resetStatus();
            resetProcessedTo();
            clearMarkers();

            var spec_sig = sigEd.getValue();
            var spec_mod = modEd.getValue();
            var thm = thmEd.getValue();

            var res = abella.batch(spec_sig, spec_mod, thm);

            $scope.output = res.output ;
            status = res.status;
            processedTo = endOfDocument();
            updateProcessDisplay();
        };

        var enableProcessing = function(){
            if(processedTo.row == 0 && processedTo.column == 0) {
                $scope.output = abella.reset(sigEd.getValue(), modEd.getValue()).output ;
            }
        };

        var follows = function(a, b){
            return a.row > b.row || (a.row == b.row && a.column >= b.column);
        };

        var strictlyFollows = function(a, b){
            return a.row > b.row || (a.row == b.row && a.column > b.column);
        };

        thmEd.getSession().getDocument().on('change', function(obj){
            if(strictlyFollows(processedTo, obj.start)){
                console.log('Change at ' + showPos(obj.start) + ' conflicts with ' + showPos(processedTo));
                processedTo = { row: 0, column: 0 };
                clearMarkers();
            } else {
                console.log('Change at ' + showPos(obj.start) + ' does not conflict with ' + showPos(processedTo));
            }
        });

        var stepForward = function(){
            enableProcessing();
            // console.log('Starting from: ' + processedTo.row + ':' + processedTo.column);
            var text = '';
            var endPos = clonePos(processedTo);
            var tokIter = new TokenIterator(thmEd.getSession(), processedTo.row, processedTo.column + 1);
            while(true){
                if (tokIter.getCurrentToken() === undefined) {
                    console.log('Cannot read current token. This probably means we are at the EOF.');
                    return false;
                }
                var tok = tokIter.getCurrentToken();
                // console.log('Read: [' + tok.type + '] "' + tok.value + '"');
                if (!tok.type.match(/comment/)) text += ' ' + tok.value;
                if (tokIter.stepForward() != null)
                    endPos = clonePos(tokIter.getCurrentTokenPosition());
                else endPos = endOfDocument();
                if (tok.type === 'punctuation.dot') break;
            }
            text = text.replace(/\s+/g, ' ');
            // console.log('Trying to execute: ' + text);
            var res = abella.process1(text);
            // console.log('Got: "' + res.output + '" @ ' + res.status);
            $scope.output += res.output;
            status = res.status;
            if (status === 'good')
                processedTo = clonePos(endPos);
            updateProcessDisplay();
            return status === 'good';
        };

        var processUptoHere = function(_editor){
            enableProcessing();
            var here = thmEd.getCursorPosition();
            if (strictlyFollows(processedTo, here)){
                __self.resetOutput();
                enableProcessing();
            }
            while (follows(here, processedTo))
                if(!stepForward ()) break;
        };

        thmEd.commands.addCommand({
            name: "processUptoHere",
            bindKey: { win: "Ctrl-Return", mac: "Command-Return" },
            exec: processUptoHere,
        });
    }]);

    app.controller('TabController', ['$cookies', '$document', '$scope', function($cookies, $document, $scope){
        this.active = parseInt($cookies.get('currentTab')) || 1;
        this.isSet = function(t){
            return this.active === t;
        };
        this.set = function(t){
            this.active = t;
            $cookies.put('currentTab', '' + this.active);
            refreshEditors();
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
