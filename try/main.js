(function(){
    var app = angular.module('main', ['ngCookies']);

    var TokenIterator = ace.require('ace/token_iterator').TokenIterator;

    var clonePos = function(pos){
        return { row: pos.row, column: pos.column };
    };

    app.controller('AbellaController', ['$scope', function($scope){
        var __save = this;

        var aceTheme = 'ace/theme/eclipse';
        ace.config.set("modePath", "ace/");
        var makeEditor = function(key,mode,minLines,maxLines,id){
            var ed = ace.edit(id);
            ed.setTheme(aceTheme);
            ed.setOptions({autoScrollEditorIntoView: true, minLines: minLines, maxLines: maxLines});
            ed.getSession().setMode(mode);
            if(typeof(Storage) !== undefined){
                ed.$blockScrolling = Infinity;
                var cached = localStorage.getItem(key);
                if(cached !== null) ed.setValue(cached, -1);
                ed.on('input', function(){
                    localStorage.setItem(key, ed.getValue());
                });
            }
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

        $scope.output = '';
        $scope.status = 'unknown';

        this.resetOutput = function(){
            $scope.output = '';
            $scope.status = 'unknown';
            $scope.processedTo = null;
        };

        this.hasOutput = function(){
          return !($scope.output === '');
        };

        this.getBackground = function(){
            switch($scope.status){
            case 'unknown': return 'text-muted';
            case 'good':    return 'bg-success';
            default:        return 'bg-danger';
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
                            __save.resetOutput();
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
            __save.resetOutput();
        };

        this.batch = function(){
            // console.log('Batch!');

            var spec_sig = sigEd.getValue();
            var spec_mod = modEd.getValue();
            var thm = thmEd.getValue();

            // console.log('Running abella.batch(' + spec_sig + ',' + spec_mod + ',' + thm + ')');

            var res = abella.batch(spec_sig, spec_mod, thm);

            $scope.output = res.output ;
            $scope.status = res.status;
        };

        var enableProcessing = function(){
            if(!$scope.processedTo) {
                $scope.processedTo = { row: 0, column: 0 };
                $scope.ti = new TokenIterator(thmEd.getSession(), 0, 0);
                $scope.output = abella.reset(sigEd.getValue(), modEd.getValue()).output ;
            }
        };

        var updateProcessDisplay = function(){
            thmEd.moveCursorToPosition($scope.processedTo);
            thmEd.getSelection().clearSelection();
            $scope.$digest();
        };

        thmEd.on('change', function(_obj){ $scope.processedTo = null; });

        var endOfDocument = function(){
            var doc = thmEd.getSession().getDocument();
            var row = doc.getLength() - 1;
            var column = doc.getLine(row).length;
            return { row: row, column: column };
        };

        this.step = function(){
            enableProcessing();
            // console.log('Starting from: ' + $scope.processedTo.row + ':' + $scope.processedTo.column);
            var text = '';
            while(true){
                if ($scope.ti.getCurrentToken() === undefined) {
                    // console.log('Cannot read current token. This probably means we are at the EOF.');
                    return false;
                }
                var tok = $scope.ti.getCurrentToken();
                // console.log('Read: [' + tok.type + '] "' + tok.value + '"');
                if (!tok.type.match(/comment/)) text += tok.value;
                if ($scope.ti.stepForward() != null)
                    $scope.processedTo = clonePos($scope.ti.getCurrentTokenPosition());
                else $scope.processedTo = endOfDocument();
                if (tok.type === 'punctuation.dot') break;
            }
            text = text.replace(/\s+/g, ' ');
            // console.log('Trying to execute: ' + text);
            var res = abella.process1(text);
            $scope.output += res.output;
            $scope.status = res.status;
            updateProcessDisplay();
            return true;
        };

        var follows = function(a, b){
            return a.row > b.row || (a.row == b.row && a.column >= b.column);
        };

        var strictlyFollows = function(a, b){
            return a.row > b.row || (a.row == b.row && a.column > b.column);
        };

        var showPos = function(pos){ return pos.row + ':' + pos.column; };

        var processUptoHere = function(_editor){
            enableProcessing();
            var here = thmEd.getCursorPosition();
            if (strictlyFollows($scope.processedTo, here)){
                console.log('Rewinding because: ' + showPos($scope.processedTo) + ' is strictly after ' + showPos(here));
                __save.resetOutput();
                enableProcessing();
            }
            while (follows(here, $scope.processedTo))
                if(!__save.step ()) break;
        };

        thmEd.commands.addCommand({
            name: "processUptoHere",
            bindKey: { win: "Ctrl-Enter", mac: "Command-Enter" },
            exec: processUptoHere,
        });

        thmEd.commands.addCommand({
            name: "processNext",
            bindKey: { win: "Ctrl-Shift-N", mac: "Command-Shift-N" },
            exec: __save.step,
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
