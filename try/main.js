(function(){
    var app = angular.module('main', ['ngCookies']);

    var TokenIterator = ace.require('ace/token_iterator').TokenIterator;

    var clonePos = function(pos){
        return { row: pos.row, column: pos.column };
    };

    app.controller('AbellaController', ['$scope', '$document', function($scope, $document){
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

        var reset = function(){
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
                            $document[0].setEditorContents(sigData,modData,thmData);
                            $document[0].refreshEditors();
                            reset();
                        });
                    });
                });
            } catch(err){
                console.log('Error loading ' + dev.name);
            }
        };

        this.clear = function(){
            $document[0].setEditorContents('sig empty.', 'module empty.', '');
            $document[0].refreshEditors();
            $document[0].getElementById('load-list').selectedIndex = 0;
            reset();
        };

        this.batch = function(){
            console.log('Batch!');

            var spec_sig = $document[0].specSigEd.getValue();
            var spec_mod = $document[0].specModEd.getValue();
            var thm = $document[0].reasoningEd.getValue();

            console.log('Running abella.batch(' + spec_sig + ',' + spec_mod + ',' + thm + ')');

            var res = abella.batch(spec_sig, spec_mod, thm);

            $scope.output = res.output ;
            $scope.status = res.status;
        };

        this.step = function(){
            if(!$scope.processedTo) {
                $scope.processedTo = { row: 0, column: 0 };
                $scope.ti = new TokenIterator($document[0].reasoningEd.getSession(), 0, 0);
                $scope.output = abella.reset($document[0].specSigEd.getValue(),
                                             $document[0].specModEd.getValue()).output ;
            }
            console.log('Starting from: ' + $scope.processedTo.row + ':' + $scope.processedTo.column);
            var text = '';
            while(true){
                if ($scope.ti.getCurrentToken() === undefined) {
                    console.log('Cannot read current token!');
                    return;
                }
                var tok = $scope.ti.getCurrentToken();
                console.log('Read: [' + tok.type + '] "' + tok.value + '"');
                if (!tok.type.match(/comment/)) text += tok.value;
                if ($scope.ti.stepForward() != null)
                    $scope.processedTo = clonePos($scope.ti.getCurrentTokenPosition());
                if (tok.type === 'punctuation.dot') break;
            }
            text = text.replace(/\s+/g, ' ');
            console.log('Trying to execute: ' + text);
            var res = abella.process1(text);
            $scope.output += res.output;
            $scope.status = res.status;
        };
    }]);

    app.controller('TabController', ['$cookies', '$document', '$scope', function($cookies, $document, $scope){
        this.active = parseInt($cookies.get('currentTab')) || 1;
        this.isSet = function(t){
            return this.active === t;
        };
        this.set = function(t){
            this.active = t;
            $cookies.put('currentTab', '' + this.active);
            $document[0].refreshEditors();
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
