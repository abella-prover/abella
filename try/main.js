(function(){
    var app = angular.module('main', ['ngCookies']);

    app.controller('TabController', ['$cookies', '$document', function($cookies, $document){
        this.active = parseInt($cookies.get('currentTab')) || 1;
        this.isSet = function(t){
            return this.active === t;
        };
        this.set = function(t){
            this.active = t;
            $cookies.put('currentTab', '' + this.active);
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
            var res = $document[0].run_abella(spec_sig, spec_mod, thm);
            this.status = res.status;
            this.output = res.output;
            $scope.output = this.output;
        };
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
