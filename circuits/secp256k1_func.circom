pragma circom 2.0.2;

// from https://github.com/ethereum/py_ecc/blob/master/py_ecc/secp256k1/secp256k1.py
function get_gx(n, k) {
    assert(n == 86 && k == 3);
    var ret[100];
    if (n == 86 && k == 3) {
        ret[0] = 52227620040540588600771222;
        ret[1] = 33347259622618539004134583;
        ret[2] = 8091721874918813684698062;
    }
    return ret;
}

function get_gy(n, k) {
    assert(n == 86 && k == 3);
    var ret[100];
    if (n == 86 && k == 3) {
        ret[0] = 59685082318776612195095029;
        ret[1] = 54599710628478995760242092;
        ret[2] = 6036146923926000695307902;
    }
    return ret;
}

function get_secp256k1_prime(n, k) {
     assert((n == 86 && k == 3) || (n == 64 && k == 4));
     var ret[100];
     if (n == 86 && k == 3) {
         ret[0] = 77371252455336267181195263;
         ret[1] = 1023;
         ret[2] = 19342813109330467168976896;
     }
     if (n == 64 && k == 4) {
         ret[0] = 18446744073709551615;
         ret[1] = 4294967295;
         ret[2] = 0;
         ret[3] = 18446744069414584321;
     }
     return ret;
}

function get_secp256k1_order(n, k) {
    assert((n == 86 && k == 3) || (n == 64 && k == 4));
    var ret[100];
    if (n == 86 && k == 3) {
        ret[0] = 28553880287938765337601361;
        ret[1] = 77371252455335114450843292;
        ret[2] = 19342813109330467168976895;
    }
    if (n == 64 && k == 4) {
        ret[0] = 17562291160714782033;
        ret[1] = 13611842547513532036;
        ret[2] = 18446744073709551615;
        ret[3] = 18446744069414584320;
    }
    return ret;
}

// returns G * 2 ** 255
// TODO check that this is correct...
function get_dummy_point(n, k) {
    assert(n == 86 && k == 3 || n == 64 && k == 4);
    var ret[2][100]; // should be [2][k]
    if (k == 3) {
        ret[0][0] = 49732730225977125179960148;
        ret[0][1] = 43852565336912664664048527;
        ret[0][2] = 9043934293559324284618350;
        ret[1][0] = 20405083474242608521046015;
        ret[1][1] = 57969189420107975911442337;
        ret[1][2] = 12380911704996683387468560;
    } else {
        ret[0][0] = 13055350994670398292;
        ret[0][1] = 5692045669299725136;
        ret[0][2] = 5793574232182301884;
        ret[0][3] = 8624967855033230099;
        ret[1][0] = 14602923977195939839;
        ret[1][1] = 16096495783772217585;
        ret[1][2] = 17848059978913647218;
        ret[1][3] = 11807357506748851191;
    }
    return ret;
}

// a[0], a[1] = x1, y1
// b[0], b[1] = x2, y2
// lamb = (b[1] - a[1]) / (b[0] - a[0]) % p
// out[0] = lamb ** 2 - a[0] - b[0] % p
// out[1] = lamb * (a[0] - out[0]) - a[1] % p
function secp256k1_addunequal_func(n, k, x1, y1, x2, y2){
    var a[2][100];
    var b[2][100];

    for(var i = 0; i < k; i++){
        a[0][i] = x1[i];
        a[1][i] = y1[i];
        b[0][i] = x2[i];
        b[1][i] = y2[i];
    }

    var out[2][100];

    var p[100] = get_secp256k1_prime(n, k);

    // b[1] - a[1]
    var sub1_out[100] = long_sub_mod_p(n, k, b[1], a[1], p);

    // b[0] - a[0]
    var sub0_out[100]= long_sub_mod_p(n, k, b[0], a[0], p);

    // lambda = (b[1] - a[1]) * inv(b[0] - a[0])
    var sub0inv[100] = mod_inv(n, k, sub0_out, p);
    var lambda[100] = prod_mod_p(n, k, sub1_out, sub0inv, p);

    // out[0] = lambda ** 2 - a[0] - b[0]
    var lambdasq_out[100] = prod_mod_p(n, k, lambda, lambda, p);
    var out0_pre_out[100] = long_sub_mod_p(n, k, lambdasq_out, a[0], p);
    var out0_out[100] = long_sub_mod_p(n, k, out0_pre_out, b[0], p);
    for (var i = 0; i < k; i++) {
        out[0][i] = out0_out[i];
    }

    // out[1] = lambda * (a[0] - out[0]) - a[1]
    var out1_0_out[100] = long_sub_mod_p(n, k, a[0], out[0], p);
    var out1_1_out[100] = prod_mod_p(n, k, lambda, out1_0_out, p);
    var out1_out[100] = long_sub_mod_p(n, k, out1_1_out, a[1], p);
    for (var i = 0; i < k; i++) {
        out[1][i] = out1_out[i];
    }

    return out;
}

// a[0], a[1] = x1, y1
// lamb = (3 * a[0] ** 2) / (2 * a[1]) % p
// out[0] = lamb ** 2 - (2 * a[0]) % p
// out[1] = lamb * (a[0] - out[0]) - a[1] % p
function secp256k1_double_func(n, k, x1, y1){
    var a[2][100];
    var b[2][100];

    for(var i = 0; i < k; i++){
        a[0][i] = x1[i];
        a[1][i] = y1[i];
    }

    var out[2][100];

    var p[100] = get_secp256k1_prime(n, k);

    // lamb_numer = 3 * a[0] ** 2
    var x1_sq[100] = prod_mod_p(n, k, a[0], a[0], p);
    var three[100];
    for (var i = 0; i < 100; i++) three[i] = i == 0 ? 3 : 0;
    var lamb_numer[100] = prod_mod_p(n, k, x1_sq, three, p);

    // lamb_denom = 2 * a[1]
    var two[100];
    for (var i = 0; i < 100; i++) two[i] = i == 0 ? 2 : 0;
    var lamb_denom[100] = prod_mod_p(n, k, a[1], two, p);

    // lambda = lamb_numer * inv(lamb_denom)
    var lamb_denom_inv[100] = mod_inv(n, k, lamb_denom, p);
    var lambda[100] = prod_mod_p(n, k, lamb_numer, lamb_denom_inv, p);

    // out[0] = lambda ** 2 - 2 * a[0]
    var lambdasq_out[100] = prod_mod_p(n, k, lambda, lambda, p);
    var out0_pre_out[100] = long_sub_mod_p(n, k, lambdasq_out, a[0], p);
    var out0_out[100] = long_sub_mod_p(n, k, out0_pre_out, a[0], p);
    for (var i = 0; i < k; i++) {
        out[0][i] = out0_out[i];
    }

    // out[1] = lambda * (a[0] - out[0]) - a[1]
    var out1_0_out[100] = long_sub_mod_p(n, k, a[0], out[0], p);
    var out1_1_out[100] = prod_mod_p(n, k, lambda, out1_0_out, p);
    var out1_out[100] = long_sub_mod_p(n, k, out1_1_out, a[1], p);
    for (var i = 0; i < k; i++) {
        out[1][i] = out1_out[i];
    }

    return out;
}
