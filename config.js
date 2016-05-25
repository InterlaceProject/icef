var Config = {
    socket : {
        port : 3000
    },
    httpServer : {
        port : 9090,
        host : '192.168.1.100',
        path : '/'
    },

    scheduler : {
        port : 9091,
        host : 'localhost',
        jar : '../coreASM/org.coreasm.biomics.wrapper/target/brapper.jar'
    }
};

module.exports = Config;
