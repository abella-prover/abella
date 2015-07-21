(function(){
    var app = angular.module('main', ['ngCookies']);

    app.controller('LoadController', ['$scope', '$document', function($scope, $document){
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
        this.select = function(dev){
            if (dev == null) return;
            // console.log('Loading: ' + dev.name);
            try {
                $.get(dev.sig, function(sigData){
                    $.get(dev.mod, function(modData){
                        $.get(dev.thm, function(thmData){
                            $document[0].setValues(sigData,modData,thmData);
                            $document[0].refreshEditors();
                        });
                    });
                });
            } catch(err){
                console.log('Error loading ' + dev.name);
            }
        };
    }]);

    app.controller('TabController', ['$cookies', '$document', function($cookies, $document){
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

    app.controller('TraceController', ['$scope', '$document', function($scope, $document){
        this.output = '';
        this.status = 'unknown';
        $scope.output = this.output;
        this.redo = function(){
            var spec_sig = $document[0].specSigEd.getValue();
            var spec_mod = $document[0].specModEd.getValue();
            var thm = $document[0].reasoningEd.getValue();
            var res = abella.batch(spec_sig, spec_mod, thm);
            this.status = res.status;
            this.output = res.output;
            $scope.output = this.output;
        };
        this.goOn = function(){
            var res = abella.process1('Type pee,quu prop.');
            this.output += res.output ;
            res = abella.process1('Theorem foo : pee /\\ quu -> quu /\\ pee.');
            this.output += res.output ;
            res = abella.process1('intros.');
            this.output += res.output ;
            res = abella.process1('case H1.');
            this.output += res.output ;
            res = abella.process1('search.');
            this.output += res.output ;
            $scope.output = this.output ;
        }
        this.hasOutput = function(){
          return !(this.output === '');
        };
        this.getBackground = function(){
            switch(this.status){
            case 'unknown': return 'text-muted';
            case 'good':    return 'bg-success';
            default:        return 'bg-danger';
            }
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
