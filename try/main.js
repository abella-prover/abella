(function(){
    var app = angular.module('main', [ ]);

    app.controller('TabController', function(){
        this.active = 3;
        this.isSet = function(t){ return this.active === t; };
        this.set = function(t){ this.active = t; };
    });

    app.controller('TraceController', ['$scope', '$document', function($scope, $document){
        this.output = '';
        this.redo = function(){
            var spec_sig = $document[0].specSigEd.getValue();
            var spec_mod = $document[0].specModEd.getValue();
            var thm = $document[0].reasoningEd.getValue();
            this.output = $document[0].run_abella(spec_sig, spec_mod, thm);
        };
        this.hasOutput = function(){
          return !(this.output === '');
        };
    }]);
})();
