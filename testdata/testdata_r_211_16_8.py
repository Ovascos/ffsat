# testdata_211_16_8
# fs = 211
# vc = 16
# f = 0.0
# pc = 8
# tc = 25
def setting():
    return 211, 16


def data(R):
    x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15,  = R.gens()
    return [
        [
            x7*x8**3*x9 - 47*x7*x8**3 + 9*x7*x8**2*x9 - 55*x8**3*x9 - x7*x8**2 + 53*x8**3 - 42*x7*x8*x9 - 73*x8**2*x9 + 75*x7*x8 + 55*x8**2 + 39*x7*x9 - 11*x8*x9 + 66*x7 + 95*x8 - 35*x9 - 43,
            x11**3*x14**2 + 54*x11**3*x14 - 21*x11**2*x14**2 + 16*x11**3 - 79*x11**2*x14 - 74*x11*x14**2 + 86*x11**2 + 13*x11*x14 - 17*x14**2 + 82*x11 - 74*x14 - 61,
            x4**2*x10**2 - 48*x4**2*x10 - 39*x4*x10**2 + 89*x4**2 - 27*x4*x10 - 47*x10**2 - 95*x4 - 65*x10 + 37,
            x0**2*x2*x11**2 + 64*x0**2*x2*x11 + 34*x0**2*x11**2 - 69*x0*x2*x11**2 - 37*x0**2*x2 + 66*x0**2*x11 + 15*x0*x2*x11 - 25*x0*x11**2 - 77*x2*x11**2 + 8*x0**2 + 21*x0*x2 + 88*x0*x11 - 75*x2*x11 - 86*x11**2 + 81*x0 - 105*x2 - 18*x11 + 17,
            x7**3 - 52*x7**2 + 79*x7 - 54,
            x5*x7 + 6*x5 + 84*x7 + 82,
            x5**2*x6**2*x13 - 74*x5**2*x6**2 + 64*x5**2*x6*x13 + 85*x5*x6**2*x13 - 94*x5**2*x6 + 40*x5*x6**2 + 96*x5**2*x13 - 46*x5*x6*x13 - 61*x6**2*x13 + 70*x5**2 + 28*x5*x6 + 83*x6**2 - 69*x5*x13 + 105*x6*x13 + 42*x5 + 37*x6 + 52*x13 - 50,
            x1**3 + 79*x1**2 - 42*x1 + 75,
        ],
        [
            x0**2*x5**2 + 25*x0**2*x5 + 97*x0*x5**2 + 30*x0**2 + 104*x0*x5 + 71*x5**2 - 44*x0 + 87*x5 + 20,
            x2 - 98,
            x1**3*x10**2*x11**3 + 74*x1**3*x10**2*x11**2 - 87*x1**3*x10*x11**3 - 64*x1**2*x10**2*x11**3 + 58*x1**3*x10**2*x11 + 103*x1**3*x10*x11**2 - 94*x1**2*x10**2*x11**2 - 75*x1**3*x11**3 + 82*x1**2*x10*x11**3 + 75*x1*x10**2*x11**3 - 71*x1**3*x10**2 + 18*x1**3*x10*x11 + 86*x1**2*x10**2*x11 - 64*x1**3*x11**2 - 51*x1**2*x10*x11**2 + 64*x1*x10**2*x11**2 - 53*x1**2*x11**3 + 16*x1*x10*x11**3 + 57*x10**2*x11**3 + 58*x1**3*x10 - 98*x1**2*x10**2 + 81*x1**3*x11 - 97*x1**2*x10*x11 - 81*x1*x10**2*x11 + 87*x1**2*x11**2 - 82*x1*x10*x11**2 - 2*x10**2*x11**2 + 72*x1*x11**3 + 105*x10*x11**3 + 50*x1**3 + 86*x1**2*x10 - 50*x1*x10**2 + 91*x1**2*x11 + 84*x1*x10*x11 - 70*x10**2*x11 + 53*x1*x11**2 - 37*x10*x11**2 - 55*x11**3 - 35*x1**2 - 81*x1*x10 - 38*x10**2 - 44*x1*x11 - 29*x10*x11 - 61*x11**2 - 48*x1 - 70*x10 - 25*x11 - 104,
            x8**2*x15**3 + 105*x8**2*x15**2 + 20*x8*x15**3 + 105*x8**2*x15 - 10*x8*x15**2 - 51*x15**3 - 75*x8**2 - 10*x8*x15 - 80*x15**2 - 23*x8 - 80*x15 + 27,
            x2*x9*x12 - 101*x2*x9 + 19*x2*x12 - 103*x9*x12 - 20*x2 + 64*x9 - 58*x12 - 50,
            x2**3 + 80*x2**2 - 36*x2 + 102,
            x3**2*x6 - 33*x3**2 + 55*x3*x6 + 84*x3 + 28*x6 - 80,
            x6*x11**3 - 31*x6*x11**2 + 21*x11**3 + x6*x11 - 18*x11**2 - x6 + 21*x11 - 21,
        ],
        [
            x15**2 + 34*x15 + 32,
            x3**2 + 103*x3 + 19,
            x2**2 + 96*x2 + 74,
            x10**2 + 48*x10 + 53,
            x2**2 - 37*x2 - 47,
            x0**3*x4**2*x8 - 25*x0**3*x4**2 - 28*x0**3*x4*x8 + 9*x0**2*x4**2*x8 + 67*x0**3*x4 - 14*x0**2*x4**2 - 51*x0**3*x8 - 41*x0**2*x4*x8 - 74*x0*x4**2*x8 + 9*x0**3 - 30*x0**2*x4 - 49*x0*x4**2 - 37*x0**2*x8 - 38*x0*x4*x8 + 62*x4**2*x8 + 81*x0**2 - 105*x0*x4 - 73*x4**2 - 24*x0*x8 - 48*x4*x8 - 33*x0 - 66*x4 + 3*x8 - 75,
            x3*x4**2*x13**3 - 62*x3*x4**2*x13**2 + 36*x3*x4*x13**3 + 56*x4**2*x13**3 - 34*x3*x4**2*x13 + 89*x3*x4*x13**2 - 96*x4**2*x13**2 + 32*x3*x13**3 - 94*x4*x13**3 - 28*x3*x4**2 + 42*x3*x4*x13 - 5*x4**2*x13 - 85*x3*x13**2 - 80*x4*x13**2 + 104*x13**3 + 47*x3*x4 - 91*x4**2 - 33*x3*x13 + 31*x4*x13 + 93*x13**2 - 52*x3 + 100*x4 + 51*x13 + 42,
            x7**3*x13*x14 - 49*x7**3*x13 + 27*x7**3*x14 + 66*x7**2*x13*x14 - 57*x7**3 - 69*x7**2*x13 + 94*x7**2*x14 + 4*x7*x13*x14 + 36*x7**2 + 15*x7*x13 - 103*x7*x14 + 44*x13*x14 - 17*x7 - 46*x13 - 78*x14 + 24,
        ],
        [
            x4 - 32,
            x12**2 + 46*x12 - 44,
            x7**2 - 69*x7 - 102,
            x2**2*x10*x11 - 25*x2**2*x10 + 66*x2**2*x11 + 18*x2*x10*x11 + 38*x2**2 - 28*x2*x10 - 78*x2*x11 - x10*x11 + 51*x2 + 25*x10 - 66*x11 - 38,
            x14**2 + 66*x14 + 76,
            x3**3*x9**3*x10**2 + 39*x3**3*x9**3*x10 + 105*x3**3*x9**2*x10**2 + 7*x3**2*x9**3*x10**2 - 102*x3**3*x9**3 + 86*x3**3*x9**2*x10 + 62*x3**2*x9**3*x10 - 36*x3**3*x9*x10**2 + 102*x3**2*x9**2*x10**2 + 34*x3*x9**3*x10**2 + 51*x3**3*x9**2 - 81*x3**2*x9**3 + 73*x3**3*x9*x10 - 31*x3**2*x9**2*x10 + 60*x3*x9**3*x10 - 76*x3**3*x10**2 - 41*x3**2*x9*x10**2 - 17*x3*x9**2*x10**2 - 86*x9**3*x10**2 + 85*x3**3*x9 - 65*x3**2*x9**2 - 92*x3*x9**3 - 10*x3**3*x10 + 89*x3**2*x9*x10 - 30*x3*x9**2*x10 + 22*x9**3*x10 + 101*x3**2*x10**2 + 42*x3*x9*x10**2 + 43*x9**2*x10**2 - 55*x3**3 - 38*x3**2*x9 + 46*x3*x9**2 - 90*x9**3 - 70*x3**2*x10 - 50*x3*x9*x10 - 11*x9**2*x10 - 52*x3*x10**2 - 69*x9*x10**2 + 37*x3**2 - 64*x3*x9 + 45*x9**2 + 82*x3*x10 + 52*x9*x10 - 5*x10**2 + 29*x3 + 75*x9 + 16*x10 + 88,
            x7 - 32,
            x2**2 + 4*x2 + 19,
        ],
        [
            x0*x13 + 82*x0 + 49*x13 + 9,
            x13**3 + 82*x13**2 + 100*x13 + 68,
            x0**2*x13**3*x15**2 - 4*x0**2*x13**3*x15 - 3*x0**2*x13**2*x15**2 + 93*x0*x13**3*x15**2 - 96*x0**2*x13**3 + 12*x0**2*x13**2*x15 + 50*x0*x13**3*x15 + 59*x0**2*x13*x15**2 - 68*x0*x13**2*x15**2 - 29*x13**3*x15**2 + 77*x0**2*x13**2 - 66*x0*x13**3 - 25*x0**2*x13*x15 + 61*x0*x13**2*x15 - 95*x13**3*x15 + 45*x0**2*x15**2 + x0*x13*x15**2 + 87*x13**2*x15**2 + 33*x0**2*x13 - 13*x0*x13**2 + 41*x13**3 + 31*x0**2*x15 - 4*x0*x13*x15 + 74*x13**2*x15 - 35*x0*x15**2 - 23*x13*x15**2 - 100*x0**2 - 96*x0*x13 + 88*x13**2 - 71*x0*x15 + 92*x13*x15 - 39*x15**2 - 16*x0 + 98*x13 - 55*x15 - 54,
            x9**2*x11**2*x15**2 + 24*x9**2*x11**2*x15 + 8*x9**2*x11*x15**2 - 76*x9*x11**2*x15**2 + 24*x9**2*x11**2 - 19*x9**2*x11*x15 + 75*x9*x11**2*x15 - 27*x9**2*x15**2 + 25*x9*x11*x15**2 + 79*x11**2*x15**2 - 19*x9**2*x11 + 75*x9*x11**2 - 15*x9**2*x15 - 33*x9*x11*x15 - 3*x11**2*x15 - 58*x9*x15**2 - x11*x15**2 - 15*x9**2 - 33*x9*x11 - 3*x11**2 + 85*x9*x15 - 24*x11*x15 - 23*x15**2 + 85*x9 - 24*x11 + 81*x15 + 81,
            x4**2 - 61*x4 - 57,
            x13 - 28,
            x6**2*x11**2*x13 - 23*x6**2*x11**2 - 45*x6**2*x11*x13 - 45*x6*x11**2*x13 - 20*x6**2*x11 - 20*x6*x11**2 - 46*x6**2*x13 - 85*x6*x11*x13 - 11*x11**2*x13 + 3*x6**2 + 56*x6*x11 + 42*x11**2 - 40*x6*x13 + 73*x11*x13 + 76*x6 + 9*x11 + 84*x13 - 33,
            x2**3*x14*x15 - 6*x2**3*x14 - 32*x2**3*x15 - 92*x2**2*x14*x15 - 19*x2**3 - 81*x2**2*x14 - 10*x2**2*x15 - 4*x2*x14*x15 + 60*x2**2 + 24*x2*x14 - 83*x2*x15 - 72*x14*x15 + 76*x2 + 10*x14 - 17*x15 + 102,
        ],
        [
            x14**2 - 14*x14 + 40,
            x2**3*x5**2*x11**3 + 27*x2**3*x5**2*x11**2 + 101*x2**3*x5*x11**3 + 65*x2**2*x5**2*x11**3 + 27*x2**3*x5**2*x11 - 16*x2**3*x5*x11**2 + 67*x2**2*x5**2*x11**2 - 54*x2**3*x11**3 + 24*x2**2*x5*x11**3 + 74*x2*x5**2*x11**3 + 63*x2**3*x5**2 - 16*x2**3*x5*x11 + 67*x2**2*x5**2*x11 + 19*x2**3*x11**2 + 15*x2**2*x5*x11**2 + 99*x2*x5**2*x11**2 + 77*x2**2*x11**3 + 89*x2*x5*x11**3 + 77*x5**2*x11**3 + 33*x2**3*x5 + 86*x2**2*x5**2 + 19*x2**3*x11 + 15*x2**2*x5*x11 + 99*x2*x5**2*x11 - 31*x2**2*x11**2 + 82*x2*x5*x11**2 - 31*x5**2*x11**2 + 13*x2*x11**3 - 30*x5*x11**3 - 26*x2**3 + 35*x2**2*x5 + 20*x2*x5**2 - 31*x2**2*x11 + 82*x2*x5*x11 - 31*x5**2*x11 - 71*x2*x11**2 + 34*x5*x11**2 + 62*x11**3 - 2*x2**2 - 90*x2*x5 - 2*x5**2 - 71*x2*x11 + 34*x5*x11 - 14*x11**2 - 25*x2 + 9*x5 - 14*x11 - 103,
            x0*x3**2 + 5*x0*x3 + 97*x3**2 - 36*x0 + 63*x3 + 95,
            x3**3*x8*x13**3 + 54*x3**3*x8*x13**2 + 88*x3**3*x13**3 - 49*x3**2*x8*x13**3 - 94*x3**3*x8*x13 - 101*x3**3*x13**2 + 97*x3**2*x8*x13**2 - 92*x3**2*x13**3 - 99*x3*x8*x13**3 + 15*x3**3*x8 - 43*x3**3*x13 - 36*x3**2*x8*x13 + 96*x3**2*x13**2 - 71*x3*x8*x13**2 - 61*x3*x13**3 + 58*x8*x13**3 + 54*x3**3 - 102*x3**2*x8 - 3*x3**2*x13 + 22*x3*x8*x13 + 82*x3*x13**2 - 33*x8*x13**2 + 40*x13**3 + 97*x3**2 - 8*x3*x8 + 37*x3*x13 + 34*x8*x13 + 50*x13**2 - 71*x3 + 26*x8 + 38*x13 - 33,
            x2**3*x5*x9**3 - 64*x2**3*x5*x9**2 + 50*x2**3*x9**3 - 60*x2**2*x5*x9**3 + 21*x2**3*x5*x9 - 35*x2**3*x9**2 + 42*x2**2*x5*x9**2 - 46*x2**2*x9**3 + 42*x2*x5*x9**3 - 51*x2**3*x5 - 5*x2**3*x9 + 6*x2**2*x5*x9 - 10*x2**2*x9**2 + 55*x2*x5*x9**2 - 10*x2*x9**3 - 52*x5*x9**3 - 18*x2**3 - 105*x2**2*x5 + 89*x2**2*x9 + 38*x2*x5*x9 + 7*x2*x9**2 - 48*x5*x9**2 - 68*x9**3 + 25*x2**2 - 32*x2*x5 + x2*x9 - 37*x5*x9 - 79*x9**2 + 88*x2 - 91*x5 + 49*x9 + 92,
            x1*x11**3*x13**2 + 11*x1*x11**3*x13 + 75*x1*x11**2*x13**2 + 18*x11**3*x13**2 + x1*x11**3 - 19*x1*x11**2*x13 - 13*x11**3*x13 + 62*x1*x11*x13**2 + 84*x11**2*x13**2 + 75*x1*x11**2 + 18*x11**3 + 49*x1*x11*x13 + 80*x11**2*x13 + 35*x1*x13**2 + 61*x11*x13**2 + 62*x1*x11 + 84*x11**2 - 37*x1*x13 + 38*x11*x13 - 3*x13**2 + 35*x1 + 61*x11 - 33*x13 - 3,
            x11**3 - 22*x11**2 + 71*x11 + 18,
            x0**2*x3*x10**3 - 47*x0**2*x3*x10**2 + 102*x0**2*x10**3 + 27*x0*x3*x10**3 - 64*x0**2*x3*x10 + 59*x0**2*x10**2 - 3*x0*x3*x10**2 + 11*x0*x10**3 + 66*x3*x10**3 - 75*x0**2*x3 + 13*x0**2*x10 - 40*x0*x3*x10 - 95*x0*x10**2 + 63*x3*x10**2 - 20*x10**3 - 54*x0**2 + 85*x0*x3 - 71*x0*x10 - 4*x3*x10 + 96*x10**2 + 19*x0 - 97*x3 + 14*x10 + 23,
        ],
        [
            x6**3*x7*x9**3 - 16*x6**3*x7*x9**2 + x6**3*x9**3 + 4*x6**2*x7*x9**3 - 33*x6**3*x7*x9 - 16*x6**3*x9**2 - 64*x6**2*x7*x9**2 + 4*x6**2*x9**3 - 105*x6*x7*x9**3 + 87*x6**3*x7 - 33*x6**3*x9 + 79*x6**2*x7*x9 - 64*x6**2*x9**2 - 8*x6*x7*x9**2 - 105*x6*x9**3 - 23*x7*x9**3 + 87*x6**3 - 74*x6**2*x7 + 79*x6**2*x9 + 89*x6*x7*x9 - 8*x6*x9**2 - 54*x7*x9**2 - 23*x9**3 - 74*x6**2 - 62*x6*x7 + 89*x6*x9 - 85*x7*x9 - 54*x9**2 - 62*x6 - 102*x7 - 85*x9 - 102,
            x1**2*x11**3 + 34*x1**2*x11**2 - 92*x1*x11**3 + 87*x1**2*x11 + 37*x1*x11**2 + 28*x11**3 - 81*x1**2 + 14*x1*x11 - 103*x11**2 + 67*x1 - 96*x11 + 53,
            x0**3*x11**3 + 7*x0**3*x11**2 - 31*x0**2*x11**3 - 65*x0**3*x11 - 6*x0**2*x11**2 - 3*x0*x11**3 + 52*x0**3 - 95*x0**2*x11 - 21*x0*x11**2 - 84*x11**3 + 76*x0**2 - 16*x0*x11 + 45*x11**2 + 55*x0 - 26*x11 + 63,
            x0**2 + 88*x0 + 64,
            x4**3*x12*x13 + 9*x4**3*x12 - 21*x4**3*x13 - 37*x4**2*x12*x13 + 22*x4**3 + 89*x4**2*x12 - 67*x4**2*x13 - 10*x4*x12*x13 + 30*x4**2 - 90*x4*x12 - x4*x13 + 50*x12*x13 - 9*x4 + 28*x12 + 5*x13 + 45,
            x14**2 + 25*x14 - 15,
            x9*x13 + 73*x9 - 32*x13 - 15,
            x9,
        ],
        [
            x6*x8**3*x11**3 + 44*x6*x8**3*x11**2 + 16*x6*x8**2*x11**3 - 15*x8**3*x11**3 + 77*x6*x8**3*x11 + 71*x6*x8**2*x11**2 - 27*x8**3*x11**2 - 28*x6*x8*x11**3 - 29*x8**2*x11**3 + 3*x6*x8**3 - 34*x6*x8**2*x11 - 100*x8**3*x11 + 34*x6*x8*x11**2 - 10*x8**2*x11**2 - 16*x6*x11**3 - 2*x8*x11**3 + 48*x6*x8**2 - 45*x8**3 - 46*x6*x8*x11 + 88*x8**2*x11 - 71*x6*x11**2 - 88*x8*x11**2 + 29*x11**3 - 84*x6*x8 - 87*x8**2 + 34*x6*x11 + 57*x8*x11 + 10*x11**2 - 48*x6 - 6*x8 - 88*x11 + 87,
            x12**3*x13**2 - 5*x12**3*x13 - 33*x12**2*x13**2 - 95*x12**3 - 46*x12**2*x13 - 59*x12*x13**2 - 30*x12**2 + 84*x12*x13 - 66*x13**2 - 92*x12 - 92*x13 - 60,
            x1**3*x10 + 91*x1**3 - 4*x1**2*x10 + 58*x1**2 - 78*x1*x10 + 76*x1 - 92*x10 + 68,
            x3 - 57,
            x5*x14**3 + 87*x5*x14**2 + 38*x14**3 + 11*x5*x14 - 70*x14**2 - 44*x5 - 4*x14 + 16,
            x5*x6**3 - 14*x5*x6**2 + 32*x6**3 - 14*x5*x6 - 26*x6**2 - 93*x5 - 26*x6 - 22,
            x0**2*x9*x15**2 + 52*x0**2*x9*x15 - 10*x0**2*x15**2 + 86*x0*x9*x15**2 + 32*x0**2*x9 - 98*x0**2*x15 + 41*x0*x9*x15 - 16*x0*x15**2 + 35*x9*x15**2 + 102*x0**2 + 9*x0*x9 + 12*x0*x15 - 79*x9*x15 + 72*x15**2 - 90*x0 + 65*x9 - 54*x15 - 17,
            x2**2*x3**3*x11 + 35*x2**2*x3**3 - 100*x2**2*x3**2*x11 - 97*x2*x3**3*x11 + 87*x2**2*x3**2 - 19*x2*x3**3 - 99*x2**2*x3*x11 - 6*x2*x3**2*x11 + 26*x3**3*x11 - 89*x2**2*x3 + x2*x3**2 + 66*x3**3 + 69*x2**2*x11 - 103*x2*x3*x11 - 68*x3**2*x11 + 94*x2**2 - 18*x2*x3 - 59*x3**2 + 59*x2*x11 - 42*x3*x11 - 45*x2 + 7*x3 - 105*x11 - 88,
        ],
        [
            x5**3*x6**2*x10**3 - 94*x5**3*x6**2*x10**2 + 104*x5**3*x6*x10**3 + 73*x5**2*x6**2*x10**3 - 55*x5**3*x6**2*x10 - 70*x5**3*x6*x10**2 + 101*x5**2*x6**2*x10**2 + 38*x5**3*x10**3 - 4*x5**2*x6*x10**3 + 81*x5*x6**2*x10**3 + 97*x5**3*x6**2 - 23*x5**3*x6*x10 - 6*x5**2*x6**2*x10 + 15*x5**3*x10**2 - 46*x5**2*x6*x10**2 - 18*x5*x6**2*x10**2 + 31*x5**2*x10**3 - 16*x5*x6*x10**3 - 9*x6**2*x10**3 - 40*x5**3*x6 - 93*x5**2*x6**2 + 20*x5**3*x10 + 9*x5**2*x6*x10 - 24*x5*x6**2*x10 + 40*x5**2*x10**2 + 27*x5*x6*x10**2 + 2*x6**2*x10**2 - 87*x5*x10**3 - 92*x6*x10**3 + 99*x5**3 + 34*x5**2*x6 + 50*x5*x6**2 - 17*x5**2*x10 + 36*x5*x6*x10 + 73*x6**2*x10 - 51*x5*x10**2 - 3*x6*x10**2 + 80*x10**3 + 53*x5**2 - 75*x5*x6 - 29*x6**2 - 68*x5*x10 - 4*x6*x10 + 76*x10**2 + x5 - 62*x6 + 31*x10 - 47,
            x0**2*x8**3 + 76*x0**2*x8**2 + 21*x0*x8**3 - 60*x0**2*x8 - 92*x0*x8**2 + 2*x8**3 - 83*x0**2 + 6*x0*x8 - 59*x8**2 - 55*x0 + 91*x8 + 45,
            x11*x13**2 - 44*x11*x13 - 80*x13**2 + 26*x11 - 67*x13 + 30,
            x12**2 + 60*x12 + 11,
            x0**2 - 15*x0 - 90,
            x1*x8*x9**3 + 30*x1*x8*x9**2 + 31*x1*x9**3 + 59*x8*x9**3 + 101*x1*x8*x9 + 86*x1*x9**2 + 82*x8*x9**2 - 70*x9**3 + 30*x1*x8 - 34*x1*x9 + 51*x8*x9 + 10*x9**2 + 86*x1 + 82*x8 + 104*x9 + 10,
            x10**2 + 98*x10 + 25,
            x1**3 - 50*x1**2 + 28*x1 - 9,
        ],
        [
            x0**2*x15**3 - 83*x0**2*x15**2 + 83*x0*x15**3 + 14*x0**2*x15 + 74*x0*x15**2 - 38*x15**3 + 48*x0**2 - 104*x0*x15 - 11*x15**2 - 25*x0 + 101*x15 + 75,
            x2*x8*x12**3 - 85*x2*x8*x12**2 + 87*x2*x12**3 + 35*x8*x12**3 + 82*x2*x8*x12 - 10*x2*x12**2 - 21*x8*x12**2 + 91*x12**3 - 13*x2*x8 - 40*x2*x12 - 84*x8*x12 + 72*x12**2 - 76*x2 - 33*x8 + 77*x12 + 83,
            x4**2*x7**3 - 30*x4**2*x7**2 - 71*x4*x7**3 - 44*x4**2*x7 + 20*x4*x7**2 - 56*x7**3 + 73*x4**2 - 41*x4*x7 - 8*x7**2 + 92*x4 - 68*x7 - 79,
            x5*x7**3*x10**2 + 63*x5*x7**3*x10 - 28*x5*x7**2*x10**2 + 38*x7**3*x10**2 + 47*x5*x7**3 - 76*x5*x7**2*x10 + 73*x7**3*x10 + 81*x5*x7*x10**2 - 9*x7**2*x10**2 - 50*x5*x7**2 + 98*x7**3 + 39*x5*x7*x10 + 66*x7**2*x10 - 100*x5*x10**2 - 87*x7*x10**2 + 9*x5*x7 - x7**2 + 30*x5*x10 + 5*x7*x10 - 2*x10**2 - 58*x5 - 80*x7 + 85*x10 - 94,
            x2**2*x9**2*x15**2 - 3*x2**2*x9**2*x15 + 33*x2**2*x9*x15**2 + 62*x2*x9**2*x15**2 - 27*x2**2*x9**2 - 99*x2**2*x9*x15 + 25*x2*x9**2*x15 + 103*x2**2*x15**2 - 64*x2*x9*x15**2 - 5*x9**2*x15**2 - 47*x2**2*x9 + 14*x2*x9**2 - 98*x2**2*x15 - 19*x2*x9*x15 + 15*x9**2*x15 + 56*x2*x15**2 + 46*x9*x15**2 - 38*x2**2 + 40*x2*x9 - 76*x9**2 + 43*x2*x15 + 73*x9*x15 - 93*x15**2 - 35*x2 + 24*x9 + 68*x15 - 21,
            x10**2 + 101*x10 - 36,
            x0**3*x7**2 - 10*x0**3*x7 + 49*x0**2*x7**2 - 92*x0**3 - 68*x0**2*x7 + 98*x0*x7**2 - 77*x0**2 + 75*x0*x7 - 8*x7**2 + 57*x0 + 80*x7 + 103,
            x4**2*x7**2*x14**2 - 14*x4**2*x7**2*x14 + 85*x4**2*x7*x14**2 + 7*x4*x7**2*x14**2 + 4*x4**2*x7**2 + 76*x4**2*x7*x14 - 98*x4*x7**2*x14 - 70*x4**2*x14**2 - 38*x4*x7*x14**2 + 13*x7**2*x14**2 - 82*x4**2*x7 + 28*x4*x7**2 - 75*x4**2*x14 - 101*x4*x7*x14 + 29*x7**2*x14 - 68*x4*x14**2 + 50*x7*x14**2 - 69*x4**2 + 59*x4*x7 + 52*x7**2 - 103*x4*x14 - 67*x7*x14 - 66*x14**2 - 61*x4 - 11*x7 + 80*x14 - 53,
        ],
        [
            x8**2 - 15*x8 - 28,
            x4*x6**2*x12 - 61*x4*x6**2 - 41*x4*x6*x12 + 64*x6**2*x12 - 31*x4*x6 + 105*x6**2 + 38*x4*x12 - 92*x6*x12 + 3*x4 - 85*x6 - 100*x12 - 19,
            x1*x5**3 - 45*x1*x5**2 - 65*x5**3 - 87*x1*x5 - 29*x5**2 + 67*x1 - 42*x5 + 76,
            x1*x2*x15**3 + 40*x1*x2*x15**2 - 82*x1*x15**3 + 58*x2*x15**3 + 96*x1*x15**2 - x2*x15**2 + 97*x15**3 + 46*x1*x2 + 82*x15**2 + 26*x1 - 75*x2 + 31,
            x2**2 + 70*x2 + 83,
            x13**2 + 96*x13 - 99,
            x1 + 66,
            x14 - 97,
        ],
        [
            x3*x4**2 + 8*x3*x4 - 101*x4**2 - 35*x3 + 36*x4 - 52,
            x3**3 + 77*x3**2 + 58*x3 - 33,
            x12**3*x15**2 - 72*x12**3*x15 + 98*x12**2*x15**2 + 70*x12**3 - 93*x12**2*x15 - 85*x12*x15**2 - 103*x12**2 + x12*x15 - 38*x15**2 - 42*x12 - 7*x15 + 83,
            x9**2 - 95*x9 + 103,
            x13 + 102,
            x2**3*x7**3*x10**3 + 93*x2**3*x7**3*x10**2 + 50*x2**3*x7**2*x10**3 + 48*x2**2*x7**3*x10**3 - 71*x2**3*x7**3*x10 + 8*x2**3*x7**2*x10**2 + 33*x2**2*x7**3*x10**2 + 70*x2**3*x7*x10**3 + 79*x2**2*x7**2*x10**3 + 17*x2*x7**3*x10**3 - 75*x2**3*x7**3 + 37*x2**3*x7**2*x10 - 32*x2**2*x7**3*x10 - 31*x2**3*x7*x10**2 - 38*x2**2*x7**2*x10**2 + 104*x2*x7**3*x10**2 - 82*x2**3*x10**3 - 16*x2**2*x7*x10**3 + 6*x2*x7**2*x10**3 - 90*x7**3*x10**3 + 48*x2**3*x7**2 - 13*x2**2*x7**3 + 94*x2**3*x7*x10 + 88*x2**2*x7**2*x10 + 59*x2*x7**3*x10 - 30*x2**3*x10**2 - 11*x2**2*x7*x10**2 - 75*x2*x7**2*x10**2 + 70*x7**3*x10**2 + 73*x2**2*x10**3 - 76*x2*x7*x10**3 - 69*x7**2*x10**3 + 25*x2**3*x7 - 17*x2**2*x7**2 - 9*x2*x7**3 - 86*x2**3*x10 + 81*x2**2*x7*x10 - 4*x2*x7**2*x10 + 60*x7**3*x10 + 37*x2**2*x10**2 - 105*x2*x7*x10**2 - 87*x7**2*x10**2 + 83*x2*x10**3 + 30*x7*x10**3 + 31*x2**3 - 66*x2**2*x7 - 28*x2*x7**2 - 2*x7**3 + 92*x2**2*x10 - 90*x2*x7*x10 + 46*x7**2*x10 - 88*x2*x10**2 + 47*x7*x10**2 - 5*x10**3 + 11*x2**2 + 3*x2*x7 - 100*x7**2 + 15*x2*x10 - 20*x7*x10 - 43*x10**2 + 105*x2 + 71*x7 - 67*x10 - 47,
            x8**3 - 25*x8**2 - 11*x8 - 101,
            x14**2 + 95*x14 + 45,
        ],
        [
            x12 + 62,
            x1*x3*x7 - 18*x1*x3 + 2*x1*x7 + 2*x3*x7 - 36*x1 - 36*x3 + 4*x7 - 72,
            x2*x12**3 + 83*x2*x12**2 - 24*x12**3 + 28*x2*x12 - 93*x12**2 - 26*x2 - 39*x12 - 9,
            x4**3*x9**3 + 35*x4**3*x9**2 - 26*x4**2*x9**3 + 65*x4**3*x9 - 66*x4**2*x9**2 - 26*x4*x9**3 - 81*x4**3 - 2*x4**2*x9 - 66*x4*x9**2 - 31*x9**3 - 4*x4**2 - 2*x4*x9 - 30*x9**2 - 4*x4 + 95*x9 - 21,
            x2*x6 + 30*x2 - 87*x6 - 78,
            x1**3 - 91*x1**2 + 31*x1 + 32,
            x1**2*x5**2*x6**3 - 8*x1**2*x5**2*x6**2 - 87*x1**2*x5*x6**3 - 16*x1*x5**2*x6**3 + 2*x1**2*x5**2*x6 + 63*x1**2*x5*x6**2 - 83*x1*x5**2*x6**2 - 77*x1**2*x6**3 - 85*x1*x5*x6**3 - 70*x5**2*x6**3 - 62*x1**2*x5**2 + 37*x1**2*x5*x6 - 32*x1*x5**2*x6 - 17*x1**2*x6**2 + 47*x1*x5*x6**2 - 73*x5**2*x6**2 - 34*x1*x6**3 - 29*x5*x6**3 - 92*x1**2*x5 - 63*x1*x5**2 + 57*x1**2*x6 + 41*x1*x5*x6 + 71*x5**2*x6 + 61*x1*x6**2 + 21*x5*x6**2 - 96*x6**3 - 79*x1**2 - 5*x1*x5 - 91*x5**2 - 68*x1*x6 - 58*x5*x6 - 76*x6**2 - 2*x1 - 101*x5 + 19*x6 + 44,
            x9 + 36,
        ],
        [
            x9 - 85,
            x14**2*x15**3 + 65*x14**2*x15**2 - 82*x14*x15**3 - 15*x14**2*x15 - 55*x14*x15**2 + 54*x15**3 + 13*x14**2 - 36*x14*x15 - 77*x15**2 - 11*x14 + 34*x15 + 69,
            x0*x6*x8**2 + 24*x0*x6*x8 + 95*x0*x8**2 - 46*x6*x8**2 + 63*x0*x6 - 41*x0*x8 - 49*x6*x8 + 61*x8**2 + 77*x0 + 56*x6 - 13*x8 + 45,
            x5**2*x8**2*x12**2 - 56*x5**2*x8**2*x12 - 63*x5**2*x8*x12**2 - 54*x5*x8**2*x12**2 - 90*x5**2*x8**2 - 59*x5**2*x8*x12 + 70*x5*x8**2*x12 + 78*x5**2*x12**2 + 26*x5*x8*x12**2 + 14*x8**2*x12**2 - 27*x5**2*x8 + 7*x5*x8**2 + 63*x5**2*x12 + 21*x5*x8*x12 + 60*x8**2*x12 + 8*x5*x12**2 - 38*x8*x12**2 - 57*x5**2 - 19*x5*x8 + 6*x8**2 - 26*x5*x12 + 18*x8*x12 + 37*x12**2 - 87*x5 + 44*x8 + 38*x12 + 46,
            x1**2*x7**2*x14**3 + 87*x1**2*x7**2*x14**2 - 97*x1**2*x7*x14**3 + 42*x1*x7**2*x14**3 + 56*x1**2*x7**2*x14 + x1**2*x7*x14**2 + 67*x1*x7**2*x14**2 + 35*x1**2*x14**3 - 65*x1*x7*x14**3 + 59*x7**2*x14**3 - 48*x1**2*x7**2 + 54*x1**2*x7*x14 + 31*x1*x7**2*x14 + 91*x1**2*x14**2 + 42*x1*x7*x14**2 + 69*x7**2*x14**2 - 7*x1*x14**3 - 26*x7*x14**3 + 14*x1**2*x7 + 94*x1*x7**2 + 61*x1**2*x14 - 53*x1*x7*x14 - 72*x7**2*x14 + 24*x1*x14**2 + 59*x7*x14**2 - 45*x14**3 + 8*x1**2 - 45*x1*x7 - 89*x7**2 + 30*x1*x14 + 21*x7*x14 + 94*x14**2 - 86*x1 - 18*x7 + 12*x14 + 50,
            x12**3 + 8*x12**2 + 36*x12 + 4,
            x3**2*x11**3*x14**2 - 34*x3**2*x11**3*x14 + 13*x3**2*x11**2*x14**2 - 44*x3*x11**3*x14**2 + 93*x3**2*x11**3 - 20*x3**2*x11**2*x14 + 19*x3*x11**3*x14 - 101*x3**2*x11*x14**2 + 61*x3*x11**2*x14**2 - 11*x11**3*x14**2 - 57*x3**2*x11**2 - 83*x3*x11**3 + 58*x3**2*x11*x14 + 36*x3*x11**2*x14 - 48*x11**3*x14 + 56*x3**2*x14**2 + 13*x3*x11*x14**2 + 68*x11**2*x14**2 + 102*x3**2*x11 - 24*x3*x11**2 + 32*x11**3 - 5*x3**2*x14 - 20*x3*x11*x14 + 9*x11**2*x14 + 68*x3*x14**2 + 56*x11*x14**2 - 67*x3**2 - 57*x3*x11 - 6*x11**2 + 9*x3*x14 - 5*x11*x14 + 17*x14**2 - 6*x3 - 67*x11 + 55*x14 + 104,
            x13 + 41,
        ],
        [
            x0*x15**3 - 86*x0*x15**2 - 57*x15**3 + 39*x0*x15 + 49*x15**2 + 66*x0 + 98*x15 + 36,
            x0**2*x9**3*x15 + 83*x0**2*x9**3 + 58*x0**2*x9**2*x15 - 26*x0*x9**3*x15 - 39*x0**2*x9**2 - 48*x0*x9**3 - 90*x0**2*x9*x15 - 31*x0*x9**2*x15 + 15*x9**3*x15 - 85*x0**2*x9 - 41*x0*x9**2 - 21*x9**3 + 87*x0**2*x15 + 19*x0*x9*x15 + 26*x9**2*x15 + 47*x0**2 + 100*x0*x9 + 48*x9**2 + 59*x0*x15 - 84*x9*x15 + 44*x0 - 9*x9 + 39*x15 + 72,
            x3*x6*x7**2 - 16*x3*x6*x7 + 67*x3*x7**2 + 53*x6*x7**2 + 17*x3*x6 - 17*x3*x7 - 4*x6*x7 - 36*x7**2 + 84*x3 + 57*x6 - 57*x7 + 21,
            x14**3 - 67*x14**2 - 34*x14 + 103,
            x8 - 73,
            x9**2*x10**2*x13**2 + 35*x9**2*x10**2*x13 - 88*x9**2*x10*x13**2 - 78*x9*x10**2*x13**2 - 97*x9**2*x10**2 + 85*x9**2*x10*x13 + 13*x9*x10**2*x13 + 69*x9**2*x13**2 - 99*x9*x10*x13**2 + 92*x10**2*x13**2 + 96*x9**2*x10 - 30*x9*x10**2 + 94*x9**2*x13 - 89*x9*x10*x13 + 55*x10**2*x13 + 104*x9*x13**2 - 78*x10*x13**2 + 59*x9**2 - 103*x9*x10 - 62*x10**2 + 53*x9*x13 + 13*x10*x13 + 18*x13**2 + 40*x9 - 30*x10 - 3*x13 - 58,
            x0**2*x3**3 + 27*x0**2*x3**2 - 35*x0*x3**3 - 64*x0**2*x3 - 101*x0*x3**2 + 70*x3**3 - 65*x0**2 - 81*x0*x3 - 9*x3**2 - 46*x0 - 49*x3 + 92,
            x2**2*x3**2*x12**2 - 39*x2**2*x3**2*x12 - 101*x2**2*x3*x12**2 + 71*x2*x3**2*x12**2 - 42*x2**2*x3**2 - 70*x2**2*x3*x12 - 26*x2*x3**2*x12 + 15*x2**2*x12**2 + 3*x2*x3*x12**2 - 67*x3**2*x12**2 + 22*x2**2*x3 - 28*x2*x3**2 + 48*x2**2*x12 + 94*x2*x3*x12 + 81*x3**2*x12 + 10*x2*x12**2 + 15*x3*x12**2 + 3*x2**2 + 85*x2*x3 + 71*x3**2 + 32*x2*x12 + 48*x3*x12 + 50*x12**2 + 2*x2 + 3*x3 - 51*x12 + 10,
        ],
        [
            x4**3*x9**3*x13 + 105*x4**3*x9**3 - 53*x4**3*x9**2*x13 - 10*x4**2*x9**3*x13 - 79*x4**3*x9**2 + 5*x4**2*x9**3 + 83*x4**3*x9*x13 - 103*x4**2*x9**2*x13 - 48*x4*x9**3*x13 + 64*x4**3*x9 - 54*x4**2*x9**2 + 24*x4*x9**3 - 11*x4**3*x13 + 14*x4**2*x9*x13 + 12*x4*x9**2*x13 + 52*x9**3*x13 - 100*x4**3 - 7*x4**2*x9 - 6*x4*x9**2 - 26*x9**3 - 101*x4**2*x13 + 25*x4*x9*x13 - 13*x9**2*x13 - 55*x4**2 + 93*x4*x9 - 99*x9**2 - 105*x4*x13 + 96*x9*x13 - 53*x4 - 48*x9 + 61*x13 + 75,
            x7*x15**2 + 73*x7*x15 - 14*x15**2 + 63*x7 + 33*x15 - 38,
            x0**3*x13**2*x15 - 35*x0**3*x13**2 + 13*x0**3*x13*x15 + 50*x0**2*x13**2*x15 - 33*x0**3*x13 - 62*x0**2*x13**2 - 87*x0**3*x15 + 17*x0**2*x13*x15 - 61*x0*x13**2*x15 + 91*x0**3 + 38*x0**2*x13 + 25*x0*x13**2 + 81*x0**2*x15 + 51*x0*x13*x15 - 59*x13**2*x15 - 92*x0**2 - 97*x0*x13 - 45*x13**2 + 32*x0*x15 + 77*x13*x15 - 65*x0 + 48*x13 + 69*x15 - 94,
            x6 + 8,
            x0**2*x1**3*x14 - 20*x0**2*x1**3 - 60*x0**2*x1**2*x14 - 62*x0*x1**3*x14 - 66*x0**2*x1**2 - 26*x0*x1**3 - 52*x0**2*x1*x14 - 78*x0*x1**2*x14 - 95*x1**3*x14 - 15*x0**2*x1 + 83*x0*x1**2 + x1**3 - 35*x0**2*x14 + 59*x0*x1*x14 + 3*x1**2*x14 + 67*x0**2 + 86*x0*x1 - 60*x1**2 + 60*x0*x14 + 87*x1*x14 + 66*x0 - 52*x1 - 51*x14 - 35,
            x9**2*x10**2*x13**2 - 51*x9**2*x10**2*x13 + 45*x9**2*x10*x13**2 - 15*x9*x10**2*x13**2 - 25*x9**2*x10**2 + 26*x9**2*x10*x13 - 79*x9*x10**2*x13 + 81*x9**2*x13**2 - 42*x9*x10*x13**2 + 103*x10**2*x13**2 - 70*x9**2*x10 - 47*x9*x10**2 + 89*x9**2*x13 + 32*x9*x10*x13 + 22*x10**2*x13 + 51*x9*x13**2 - 7*x10*x13**2 + 85*x9**2 - 5*x9*x10 - 43*x10**2 - 69*x9*x13 - 65*x10*x13 - 97*x13**2 - 9*x9 - 36*x10 + 94*x13 + 104,
            x5 + 30,
            x4 + 15,
        ],
        [
            x10 - 11,
            x5**2 + 98*x5 + 14,
            x5*x6**3*x15**2 - 25*x5*x6**3*x15 - 35*x5*x6**2*x15**2 + 105*x6**3*x15**2 + 65*x5*x6**3 + 31*x5*x6**2*x15 - 93*x6**3*x15 - 84*x5*x6*x15**2 - 88*x6**2*x15**2 + 46*x5*x6**2 + 73*x6**3 - 10*x5*x6*x15 + 90*x6**2*x15 + 33*x5*x15**2 + 42*x6*x15**2 + 26*x5*x6 - 23*x6**2 + 19*x5*x15 + 5*x6*x15 + 89*x15**2 + 35*x5 - 13*x6 + 96*x15 + 88,
            x1**3*x14**3 + 46*x1**3*x14**2 + 54*x1**2*x14**3 + 58*x1**3*x14 - 48*x1**2*x14**2 + 63*x1*x14**3 + 57*x1**3 - 33*x1**2*x14 - 56*x1*x14**2 + 9*x14**3 - 87*x1**2 + 67*x1*x14 - 8*x14**2 + 4*x1 + 100*x14 + 91,
            x1**2*x3**3*x12**3 - 104*x1**2*x3**3*x12**2 - 58*x1**2*x3**2*x12**3 - 79*x1*x3**3*x12**3 - 12*x1**2*x3**3*x12 - 87*x1**2*x3**2*x12**2 - 13*x1*x3**3*x12**2 - 72*x1**2*x3*x12**3 - 60*x1*x3**2*x12**3 - 84*x3**3*x12**3 + 13*x1**2*x3**3 + 63*x1**2*x3**2*x12 + 104*x1*x3**3*x12 + 103*x1**2*x3*x12**2 - 90*x1*x3**2*x12**2 + 85*x3**3*x12**2 - 77*x1**2*x12**3 - 9*x1*x3*x12**3 + 19*x3**2*x12**3 + 90*x1**2*x3**2 + 28*x1*x3**3 + 20*x1**2*x3*x12 + 87*x1*x3**2*x12 - 47*x3**3*x12 - 10*x1**2*x12**2 + 92*x1*x3*x12**2 - 77*x3**2*x12**2 - 36*x1*x12**3 - 71*x3*x12**3 - 92*x1**2*x3 + 64*x1*x3**2 - 37*x3**3 + 80*x1**2*x12 - 103*x1*x3*x12 - 17*x3**2*x12 - 54*x1*x12**2 - x3*x12**2 - 73*x12**3 + 54*x1**2 + 94*x1*x3 + 36*x3**2 + 10*x1*x12 + 8*x3*x12 - 4*x12**2 - 46*x1 - 79*x3 + 32*x12 - 105,
            x0**3 + 19*x0**2 + 37*x0 - 35,
            x3**2*x12**3*x14**2 - 35*x3**2*x12**3*x14 - 67*x3**2*x12**2*x14**2 - 25*x3*x12**3*x14**2 + 43*x3**2*x12**3 + 24*x3**2*x12**2*x14 + 31*x3*x12**3*x14 + 68*x3**2*x12*x14**2 - 13*x3*x12**2*x14**2 + 55*x12**3*x14**2 + 73*x3**2*x12**2 - 20*x3*x12**3 - 59*x3**2*x12*x14 + 33*x3*x12**2*x14 - 26*x12**3*x14 - 7*x3**2*x14**2 - 12*x3*x12*x14**2 - 98*x12**2*x14**2 - 30*x3**2*x12 + 74*x3*x12**2 + 44*x12**3 + 34*x3**2*x14 - 2*x3*x12*x14 + 54*x12**2*x14 - 36*x3*x14**2 - 58*x12*x14**2 - 90*x3**2 - 94*x3*x12 + 6*x12**2 - 6*x3*x14 - 80*x12*x14 + 37*x14**2 - 71*x3 + 38*x12 - 29*x14 - 97,
            x3**2*x8**2*x13**3 - 50*x3**2*x8**2*x13**2 - 33*x3**2*x8*x13**3 + 4*x3*x8**2*x13**3 - 90*x3**2*x8**2*x13 - 38*x3**2*x8*x13**2 + 11*x3*x8**2*x13**2 + 69*x3**2*x13**3 + 79*x3*x8*x13**3 - 60*x8**2*x13**3 + 36*x3**2*x8**2 + 16*x3**2*x8*x13 + 62*x3*x8**2*x13 - 74*x3**2*x13**2 + 59*x3*x8*x13**2 + 46*x8**2*x13**2 + 65*x3*x13**3 + 81*x8*x13**3 + 78*x3**2*x8 - 67*x3*x8**2 - 91*x3**2*x13 + 64*x3*x8*x13 - 86*x8**2*x13 - 85*x3*x13**2 - 41*x8*x13**2 + 80*x13**3 - 48*x3**2 + 101*x3*x8 - 50*x8**2 + 58*x3*x13 + 95*x8*x13 + 9*x13**2 + 19*x3 - 38*x8 - 26*x13 - 74,
        ],
        [
            x4*x6**3*x11 + 15*x4*x6**3 + 11*x4*x6**2*x11 - 84*x6**3*x11 - 46*x4*x6**2 + 6*x6**3 - 59*x4*x6*x11 - 80*x6**2*x11 - 41*x4*x6 + 66*x6**2 + 67*x4*x11 + 103*x6*x11 - 50*x4 + 68*x6 + 69*x11 - 20,
            x9*x12**3*x15**3 + 61*x9*x12**3*x15**2 + 67*x9*x12**2*x15**3 - 96*x12**3*x15**3 - 57*x9*x12**3*x15 + 78*x9*x12**2*x15**2 + 52*x12**3*x15**2 + 56*x9*x12*x15**3 - 102*x12**2*x15**3 + 26*x9*x12**3 - 21*x9*x12**2*x15 - 14*x12**3*x15 + 40*x9*x12*x15**2 - 103*x12**2*x15**2 - 89*x9*x15**3 - 101*x12*x15**3 + 54*x9*x12**2 + 36*x12**3 - 27*x9*x12*x15 - 94*x12**2*x15 + 57*x9*x15**2 - 42*x12*x15**2 + 104*x15**3 - 21*x9*x12 + 91*x12**2 + 9*x9*x15 + 60*x12*x15 + 14*x15**2 + 7*x9 - 94*x12 - 20*x15 - 39,
            x6*x7**2 + 70*x6*x7 + 48*x7**2 - 62*x6 - 16*x7 - 22,
            x3**3*x12**3 + 17*x3**3*x12**2 + 79*x3**2*x12**3 + 38*x3**3*x12 + 77*x3**2*x12**2 - 100*x3*x12**3 + 91*x3**3 + 48*x3**2*x12 - 12*x3*x12**2 - 28*x12**3 + 15*x3**2 - 2*x3*x12 - 54*x12**2 - 27*x3 - 9*x12 - 16,
            x3**3*x7**3 - 105*x3**3*x7**2 + 98*x3**2*x7**3 - 29*x3**3*x7 + 49*x3**2*x7**2 - 27*x3*x7**3 - 99*x3**2*x7 + 92*x3*x7**2 - 44*x7**3 - 61*x3*x7 - 22*x7**2 + 10*x7,
            x12**3 + 103*x12**2 + 24*x12 + 102,
            x0*x14**3 + 74*x0*x14**2 - 55*x14**3 + 64*x0*x14 - 61*x14**2 + 18*x0 + 67*x14 + 65,
            x2**2*x8 - 48*x2**2 + 34*x2*x8 + 56*x2 + 67*x8 - 51,
        ],
        [
            x5**3*x10*x15**2 + 29*x5**3*x10*x15 + 95*x5**3*x15**2 - 25*x5**2*x10*x15**2 + 5*x5**3*x10 + 12*x5**3*x15 - 92*x5**2*x10*x15 - 54*x5**2*x15**2 + 96*x5*x10*x15**2 + 53*x5**3 + 86*x5**2*x10 - 89*x5**2*x15 + 41*x5*x10*x15 + 47*x5*x15**2 - 73*x10*x15**2 - 59*x5**2 + 58*x5*x10 + 97*x5*x15 - 7*x10*x15 + 28*x15**2 + 24*x5 + 57*x10 - 32*x15 - 71,
            x3**2*x4**2*x15**3 - 15*x3**2*x4**2*x15**2 - 21*x3**2*x4*x15**3 + 47*x3*x4**2*x15**3 - 52*x3**2*x4**2*x15 + 104*x3**2*x4*x15**2 - 72*x3*x4**2*x15**2 + 93*x3**2*x15**3 + 68*x3*x4*x15**3 + 35*x4**2*x15**3 + 60*x3**2*x4**2 + 37*x3**2*x4*x15 + 88*x3*x4**2*x15 + 82*x3**2*x15**2 + 35*x3*x4*x15**2 - 103*x4**2*x15**2 - 60*x3*x15**3 - 102*x4*x15**3 + 6*x3**2*x4 + 77*x3*x4**2 + 17*x3**2*x15 + 51*x3*x4*x15 + 79*x4**2*x15 + 56*x3*x15**2 + 53*x4*x15**2 + 90*x15**3 + 94*x3**2 + 71*x3*x4 - 10*x4**2 - 45*x3*x15 + 29*x4*x15 - 84*x15**2 - 13*x3 - x4 - 38*x15 - 86,
            x2 + 75,
            x6*x14**2 + 78*x6*x14 - 65*x14**2 - 14*x6 - 6*x14 + 66,
            x8**3*x13**2 + 28*x8**3*x13 - 4*x8**2*x13**2 - 51*x8**3 + 99*x8**2*x13 + 87*x8*x13**2 - 7*x8**2 - 96*x8*x13 - 80*x13**2 - 6*x8 + 81*x13 + 71,
            x2*x4**3 + 62*x2*x4**2 + 57*x4**3 - 47*x2*x4 - 53*x4**2 + 87*x2 + 64*x4 - 105,
            x2**2*x5**3 + 22*x2**2*x5**2 + 95*x2*x5**3 + 50*x2**2*x5 - 20*x2*x5**2 + 104*x5**3 + 69*x2**2 - 103*x2*x5 - 33*x5**2 + 14*x2 - 75*x5 + 2,
            x2**2*x10**2*x14 - 93*x2**2*x10**2 - 58*x2**2*x10*x14 - 92*x2**2*x10 + 7*x2**2*x14 + 40*x10**2*x14 - 18*x2**2 + 78*x10**2 + x10*x14 - 93*x10 + 69*x14 - 87,
        ],
        [
            x9**3 - 36*x9**2 + 85*x9 - 103,
            x5**3*x7*x10 + 70*x5**3*x7 + 63*x5**3*x10 + 6*x5**2*x7*x10 - 21*x5**3 - 2*x5**2*x7 - 44*x5**2*x10 + 17*x5*x7*x10 + 85*x5**2 - 76*x5*x7 + 16*x5*x10 + 15*x7*x10 + 65*x5 - 5*x7 + 101*x10 - 104,
            x10**2 - 29*x10 - 31,
            x10*x11**3*x12**2 + 41*x10*x11**3*x12 + 85*x10*x11**2*x12**2 + 50*x11**3*x12**2 + 58*x10*x11**3 - 102*x10*x11**2*x12 - 60*x11**3*x12 - 87*x10*x11*x12**2 + 30*x11**2*x12**2 + 77*x10*x11**2 - 54*x11**3 + 20*x10*x11*x12 - 36*x11**2*x12 + 19*x10*x12**2 + 81*x11*x12**2 + 18*x10*x11 + 52*x11**2 - 65*x10*x12 - 55*x11*x12 - 105*x12**2 + 47*x10 + 56*x11 - 85*x12 + 29,
            x5*x8 - 15*x5 - 9*x8 - 76,
            x7*x11**3 - 74*x7*x11**2 + 25*x11**3 - x7*x11 + 49*x11**2 - 80*x7 - 25*x11 - 101,
            x15**2 - 88*x15 + 79,
            x2**2*x5**2*x9**2 - 9*x2**2*x5**2*x9 + 64*x2**2*x5*x9**2 + 88*x2*x5**2*x9**2 - 14*x2**2*x5**2 + 57*x2**2*x5*x9 + 52*x2*x5**2*x9 - 24*x2**2*x9**2 - 65*x2*x5*x9**2 + 7*x5**2*x9**2 - 52*x2**2*x5 + 34*x2*x5**2 + 5*x2**2*x9 - 48*x2*x5*x9 - 63*x5**2*x9 - 2*x2*x9**2 + 26*x5*x9**2 - 86*x2**2 + 66*x2*x5 - 98*x5**2 + 18*x2*x9 - 23*x5*x9 + 43*x9**2 + 28*x2 + 58*x5 + 35*x9 + 31,
        ],
        [
            x5**3 - 100*x5**2 + 10*x5 - 52,
            x4**3 - 94*x4**2 + 101*x4 + 83,
            x4**2*x14 - 83*x4**2 + 99*x4*x14 + 12*x4 - 65*x14 - 91,
            x9**2*x11**2*x12**2 - 46*x9**2*x11**2*x12 + 39*x9**2*x11*x12**2 - 32*x9*x11**2*x12**2 + 105*x9**2*x11*x12 - 5*x9*x11**2*x12 - 5*x9**2*x12**2 + 18*x9*x11*x12**2 - 60*x11**2*x12**2 + 19*x9**2*x12 + 16*x9*x11*x12 + 17*x11**2*x12 - 51*x9*x12**2 - 19*x11*x12**2 + 25*x9*x12 + 30*x11*x12 + 89*x12**2 - 85*x12,
            x7**2 - 41*x7 + 89,
            x10**3 + 64*x10**2 + 50*x10 + 78,
            x3*x6**2*x11 - 94*x3*x6**2 - 12*x3*x6*x11 - 30*x6**2*x11 + 73*x3*x6 + 77*x6**2 + 68*x3*x11 - 62*x6*x11 - 62*x3 - 80*x6 + 70*x11 - 39,
            x4*x12**2 + 103*x4*x12 + 62*x12**2 - 7*x4 + 56*x12 - 12,
        ],
        [
            x8**2*x13 + 93*x8**2 - 38*x8*x13 + 53*x8 + 36*x13 - 28,
            x8**2*x10 + 52*x8**2 - 70*x8*x10 - 53*x8 - 47*x10 + 88,
            x3*x14**3 - 86*x3*x14**2 - 8*x14**3 + 32*x3*x14 + 55*x14**2 - 4*x3 - 45*x14 + 32,
            x3**2 + 88*x3 - 10,
            x10*x14**3 - 104*x10*x14**2 - 39*x14**3 - 65*x10*x14 + 47*x14**2 - 83*x10 + 3*x14 + 72,
            x0**3*x6**2*x9**2 - 57*x0**3*x6**2*x9 + 96*x0**3*x6*x9**2 + 16*x0**2*x6**2*x9**2 - 78*x0**3*x6**2 + 14*x0**3*x6*x9 - 68*x0**2*x6**2*x9 + 23*x0**3*x9**2 + 59*x0**2*x6*x9**2 + 21*x0*x6**2*x9**2 - 103*x0**3*x6 + 18*x0**2*x6**2 - 45*x0**3*x9 + 13*x0**2*x6*x9 + 69*x0*x6**2*x9 - 54*x0**2*x9**2 - 94*x0*x6*x9**2 - 31*x6**2*x9**2 + 105*x0**3 + 40*x0**2*x6 + 50*x0*x6**2 - 87*x0**2*x9 + 83*x0*x6*x9 + 79*x6**2*x9 + 61*x0*x9**2 - 22*x6*x9**2 - 8*x0**2 - 53*x0*x6 + 97*x6**2 - 101*x0*x9 - 12*x6*x9 - 80*x9**2 + 95*x0 + 28*x6 - 82*x9 - 90,
            x7**3 + 98*x7**2 + 72*x7 + 44,
            x9**3 + 69*x9**2 - 31*x9 + 65,
        ],
        [
            x4**2*x10*x15 - 68*x4**2*x10 - 21*x4**2*x15 + 19*x4*x10*x15 - 49*x4**2 - 26*x4*x10 + 23*x4*x15 - 69*x10*x15 - 87*x4 + 50*x10 - 28*x15 + 5,
            x2**2*x6**2 - 86*x2**2*x6 - 102*x2*x6**2 + 74*x2**2 - 90*x2*x6 + 3*x6**2 + 48*x2 - 47*x6 + 11,
            x1**2*x4 - 28*x1**2 + 97*x1*x4 + 27*x1 + 59*x4 + 36,
            x10**2*x11**2 - 87*x10**2*x11 - 68*x10*x11**2 + 53*x10**2 + 8*x10*x11 + 55*x11**2 - 17*x10 + 68*x11 - 39,
            x1*x5**2 + 79*x1*x5 - 58*x5**2 + 72*x1 + 60*x5 + 44,
            x2**2*x9**3*x13**3 + 101*x2**2*x9**3*x13**2 - 24*x2**2*x9**2*x13**3 + 23*x2*x9**3*x13**3 - 26*x2**2*x9**3*x13 - 103*x2**2*x9**2*x13**2 + 2*x2*x9**3*x13**2 - 88*x2**2*x9*x13**3 + 81*x2*x9**2*x13**3 + 63*x9**3*x13**3 - 77*x2**2*x9**3 - 9*x2**2*x9**2*x13 + 35*x2*x9**3*x13 - 26*x2**2*x9*x13**2 - 48*x2*x9**2*x13**2 + 33*x9**3*x13**2 + 51*x2**2*x13**3 + 86*x2*x9*x13**3 - 35*x9**2*x13**3 - 51*x2**2*x9**2 - 83*x2*x9**3 - 33*x2**2*x9*x13 + 4*x2*x9**2*x13 + 50*x9**3*x13 + 87*x2**2*x13**2 + 35*x2*x9*x13**2 + 52*x9**2*x13**2 - 93*x2*x13**3 - 58*x9*x13**3 + 24*x2**2*x9 + 93*x2*x9**2 + 2*x9**3 - 60*x2**2*x13 + 85*x2*x9*x13 + 66*x9**2*x13 + 102*x2*x13**2 + 50*x9*x13**2 + 48*x13**3 + 82*x2**2 - 81*x2*x9 - 48*x9**2 + 97*x2*x13 + 31*x9*x13 - 5*x13**2 - 13*x2 + 35*x9 + 18*x13 + 102,
            x0*x10**2*x15**3 - 100*x0*x10**2*x15**2 - 14*x0*x10*x15**3 + 89*x10**2*x15**3 + 72*x0*x10**2*x15 - 77*x0*x10*x15**2 - 38*x10**2*x15**2 + 13*x0*x15**3 + 20*x10*x15**3 + 44*x0*x10**2 + 47*x0*x10*x15 + 78*x10**2*x15 - 34*x0*x15**2 - 101*x10*x15**2 + 102*x15**3 + 17*x0*x10 - 93*x10**2 + 92*x0*x15 - 37*x10*x15 - 72*x15**2 - 61*x0 + 36*x10 - 41*x15 + 57,
            x5**2*x15**3 + 32*x5**2*x15**2 + 71*x5*x15**3 + 11*x5**2*x15 - 49*x5*x15**2 + 82*x15**3 - 99*x5**2 - 63*x5*x15 + 92*x15**2 - 66*x5 + 58*x15 - 100,
        ],
        [
            x5*x13 - 89*x5 + 69*x13 - 22,
            x2**3*x6*x14**3 - x2**3*x6*x14**2 - 86*x2**3*x14**3 - 94*x2**2*x6*x14**3 + 73*x2**3*x6*x14 + 86*x2**3*x14**2 + 94*x2**2*x6*x14**2 + 66*x2**2*x14**3 + 60*x2*x6*x14**3 + 97*x2**3*x6 + 52*x2**3*x14 + 101*x2**2*x6*x14 - 66*x2**2*x14**2 - 60*x2*x6*x14**2 - 96*x2*x14**3 + 94*x6*x14**3 + 98*x2**3 - 45*x2**2*x6 - 35*x2**2*x14 - 51*x2*x6*x14 + 96*x2*x14**2 - 94*x6*x14**2 - 66*x14**3 + 72*x2**2 - 88*x2*x6 - 45*x2*x14 - 101*x6*x14 + 66*x14**2 - 28*x2 + 45*x6 + 35*x14 - 72,
            x5*x6 + 24*x5 + 64*x6 + 59,
            x3**3*x13 - 55*x3**3 + 28*x3**2*x13 - 63*x3**2 + 28*x3*x13 - 63*x3 + 32*x13 - 72,
            x0**3*x1**3*x12 + 38*x0**3*x1**3 + 18*x0**3*x1**2*x12 + 45*x0**2*x1**3*x12 + 51*x0**3*x1**2 + 22*x0**2*x1**3 - 90*x0**3*x1*x12 - 34*x0**2*x1**2*x12 - 43*x0*x1**3*x12 - 44*x0**3*x1 - 26*x0**2*x1**2 + 54*x0*x1**3 + 84*x0**3*x12 - 41*x0**2*x1*x12 + 70*x0*x1**2*x12 - 99*x1**3*x12 + 27*x0**3 - 81*x0**2*x1 - 83*x0*x1**2 + 36*x1**3 - 18*x0**2*x12 + 72*x0*x1*x12 - 94*x1**2*x12 - 51*x0**2 - 7*x0*x1 + 15*x1**2 - 25*x0*x12 + 48*x1*x12 + 105*x0 - 75*x1 - 87*x12 + 70,
            x8 + 27,
            x2**3*x4**3 + 97*x2**3*x4**2 - 51*x2**2*x4**3 + 58*x2**3*x4 - 94*x2**2*x4**2 - 81*x2*x4**3 - 43*x2**3 - 4*x2**2*x4 - 50*x2*x4**2 + 101*x4**3 + 83*x2**2 - 56*x2*x4 + 91*x4**2 - 104*x2 - 50*x4 + 88,
            x9**2*x15 - 22*x9**2 - 93*x9*x15 - 64*x9 + 29*x15 - 5,
        ],
        [
            x1**3*x5**3*x8**3 - 19*x1**3*x5**3*x8**2 - 99*x1**3*x5**2*x8**3 + 87*x1**2*x5**3*x8**3 + 15*x1**3*x5**3*x8 - 18*x1**3*x5**2*x8**2 + 35*x1**2*x5**3*x8**2 - 40*x1**3*x5*x8**3 + 38*x1**2*x5**2*x8**3 - 23*x1*x5**3*x8**3 + 19*x1**3*x5**3 - 8*x1**3*x5**2*x8 + 39*x1**2*x5**3*x8 - 84*x1**3*x5*x8**2 - 89*x1**2*x5**2*x8**2 + 15*x1*x5**3*x8**2 + 79*x1**3*x8**3 - 104*x1**2*x5*x8**3 - 44*x1*x5**2*x8**3 - 91*x5**3*x8**3 + 18*x1**3*x5**2 - 35*x1**2*x5**3 + 33*x1**3*x5*x8 - 63*x1**2*x5**2*x8 + 77*x1*x5**3*x8 - 24*x1**3*x8**2 + 77*x1**2*x5*x8**2 - 8*x1*x5**2*x8**2 + 41*x5**3*x8**2 - 90*x1**2*x8**3 + 76*x1*x5*x8**3 - 64*x5**2*x8**3 + 84*x1**3*x5 + 89*x1**2*x5**2 - 15*x1*x5**3 - 81*x1**3*x8 - 83*x1**2*x5*x8 - 27*x1*x5**2*x8 - 99*x5**3*x8 + 22*x1**2*x8**2 + 33*x1*x5*x8**2 - 50*x5**2*x8**2 + 82*x1*x8**3 + 53*x5*x8**3 + 24*x1**3 - 77*x1**2*x5 + 8*x1*x5**2 - 41*x5**3 - 84*x1**2*x8 + 85*x1*x5*x8 + 95*x5**2*x8 - 81*x1*x8**2 + 48*x5*x8**2 - 15*x8**3 - 22*x1**2 - 33*x1*x5 + 50*x5**2 - 36*x1*x8 - 49*x5*x8 + 74*x8**2 + 81*x1 - 48*x5 - 14*x8 - 74,
            x2 + 27,
            x9*x15**2 + 53*x9*x15 - 68*x15**2 - 51*x9 - 17*x15 + 92,
            x12 - 8,
            x8*x9**2*x12**2 + 27*x8*x9**2*x12 + 59*x8*x9*x12**2 - 58*x9**2*x12**2 - 56*x8*x9**2 - 95*x8*x9*x12 - 89*x9**2*x12 - 47*x8*x12**2 - 46*x9*x12**2 + 72*x8*x9 + 83*x9**2 - 3*x8*x12 + 24*x9*x12 - 17*x12**2 + 100*x8 + 44*x9 - 37*x12 - 103,
            x7**3*x9 + 31*x7**3 - 81*x7**2*x9 + 21*x7**2 - 84*x7*x9 - 72*x7 - 88*x9 + 15,
            x8*x11**3 + 60*x8*x11**2 + 12*x11**3 - 22*x8*x11 + 87*x11**2 - 39*x8 - 53*x11 - 46,
            x12**2*x15 + 59*x12**2 + 82*x12*x15 - 15*x12 - 52*x15 + 97,
        ],
    ]
