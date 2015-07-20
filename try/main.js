(function(){
    var app = angular.module('main', [ ]);

    app.controller('TabController', function(){
        this.active = 2;
        this.isSet = function(t){ return this.active === t; };
        this.set = function(t){ this.active = t; }
    });
})();
