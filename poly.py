from curve import Scalar
from enum import Enum


class Basis(Enum):
    LAGRANGE = 1
    MONOMIAL = 2


class Polynomial:
    values: list[Scalar]
    basis: Basis

    def __init__(self, values: list[Scalar], basis: Basis):
        assert all(isinstance(x, Scalar) for x in values)
        assert isinstance(basis, Basis)
        self.values = values
        self.basis = basis

    def __eq__(self, other):
        return (self.basis == other.basis) and (self.values == other.values)

    def __add__(self, other):
        if isinstance(other, Polynomial):
            assert len(self.values) == len(other.values)
            assert self.basis == other.basis

            return Polynomial(
                [x + y for x, y in zip(self.values, other.values)],
                self.basis,
            )
        else:
            assert isinstance(other, Scalar)
            if self.basis == Basis.LAGRANGE:
                return Polynomial(
                    [x + other for x in self.values],
                    self.basis,
                )
            else:
                return Polynomial(
                    [self.values[0] + other] + self.values[1:],
                    self.basis
                )

    def __sub__(self, other):
        if isinstance(other, Polynomial):
            assert len(self.values) == len(other.values)
            assert self.basis == other.basis

            return Polynomial(
                [x - y for x, y in zip(self.values, other.values)],
                self.basis,
            )
        else:
            assert isinstance(other, Scalar)
            if self.basis == Basis.LAGRANGE:
                return Polynomial(
                    [x - other for x in self.values],
                    self.basis,
                )
            else:
                return Polynomial(
                    [self.values[0] - other] + self.values[1:],
                    self.basis
                )


    def __mul__(self, other):
        if isinstance(other, Polynomial):
            assert self.basis == Basis.LAGRANGE
            assert self.basis == other.basis
            assert len(self.values) == len(other.values)

            return Polynomial(
                [x * y for x, y in zip(self.values, other.values)],
                self.basis,
            )
        else:
            assert isinstance(other, Scalar)
            return Polynomial(
                [x * other for x in self.values],
                self.basis,
            )

    def __truediv__(self, other):
        if isinstance(other, Polynomial):
            assert self.basis == Basis.LAGRANGE
            assert self.basis == other.basis
            assert len(self.values) == len(other.values)

            return Polynomial(
                [x / y for x, y in zip(self.values, other.values)],
                self.basis,
            )
        else:
            assert isinstance(other, Scalar)
            return Polynomial(
                [x / other for x in self.values],
                self.basis,
            )

    def shift(self, shift: int):
        assert self.basis == Basis.LAGRANGE
        assert shift < len(self.values)

        return Polynomial(
            self.values[shift:] + self.values[:shift],
            self.basis,
        )

    # Convenience method to do FFTs specifically over the subgroup over which
    # all of the proofs are operating
    def fft(self, inv=False):
        # Fast Fourier transform, used to convert between polynomial coefficients
        # and a list of evaluations at the roots of unity
        # See https://vitalik.ca/general/2019/05/12/fft.html
        def _fft(vals, modulus, roots_of_unity):
            if len(vals) == 1:
                return vals
            L = _fft(vals[::2], modulus, roots_of_unity[::2])  # 偶数次，
            R = _fft(vals[1::2], modulus, roots_of_unity[::2]) # 奇数次
            o = [0] * len(vals)
            for i, (x, y) in enumerate(zip(L, R)):
                y_times_root = y * roots_of_unity[i]
                o[i] = (x + y_times_root) % modulus
                o[i + len(L)] = (x - y_times_root) % modulus
            return o

        # roots = Scalar.roots_of_unity(len(self.values))
        # print(f"roots:{roots}")

        roots = [x.n for x in Scalar.roots_of_unity(len(self.values))] #x是scalar,取x.n 赋值给roots
        # print(f"roots:{roots}")
        o, nvals = Scalar.field_modulus, [x.n for x in self.values]
        if inv:
            assert self.basis == Basis.LAGRANGE
            # Inverse FFT， 使用IFFT将多项式从 点值表示变成系数表示。
            invlen = Scalar(1) / len(self.values)
            reversed_roots = [roots[0]] + roots[1:][::-1]  # [1, w, w^2, w^7] =>[1, w^-1, w^-2,..... ], w^-1 = w^7
            # print(f"roots:{reversed_roots}")
            return Polynomial(
                [Scalar(x) * invlen for x in _fft(nvals, o, reversed_roots)],
                Basis.MONOMIAL,
            )
        else:
            assert self.basis == Basis.MONOMIAL
            # Regular FFT
            return Polynomial(
                [Scalar(x) for x in _fft(nvals, o, roots)], Basis.LAGRANGE
            )

    def ifft(self):
        return self.fft(True)

    # 将在[1, w, w^2... w^(n-1)]的一系列点值形式转换成[offset, offset*q]
    # Converts a list of evaluations at [1, w, w**2... w**(n-1)] to
    # a list of evaluations at
    # [offset, offset * q, offset * q**2 ... offset * q**(4n-1)] where q = w**(1/4)
    # This lets us work with higher-degree polynomials, and the offset lets us
    # avoid the 0/0 problem when computing a division (as long as the offset is
    # chosen randomly)
    # TODO(keep)，将f(x) 从order=N，扩展到 4N.
    def to_coset_extended_lagrange(self, offset):
        assert self.basis == Basis.LAGRANGE
        group_order = len(self.values)
        x_powers = self.ifft().values  # step1: 将多项式的点值形式通过ifft 转换成系数形式(f(x) = a_0+ a_1*x + a_2*x^2 + a_3*x^3 + ...+a_[order-1]*x^(order-1)
        x_powers = [(offset**i * x) for i, x in enumerate(x_powers)] + [Scalar(0)] * (
            group_order * 3
        ) # step2: 将多项式表示为f'(x) = a_0 + a_1*(offset *x) + a_2*(offsset*x)^2 + a_3*(offsset*x)^3 + ... +a_[order-1] * (offset *x)^(order-1) + 0*x^(order) +....+ 0*x^(4*order-1)
        return Polynomial(x_powers, Basis.MONOMIAL).fft()  # 返回的结果用点值形式表示


    def to_coset_extended_lagrange1(self, offset):
        assert self.basis == Basis.LAGRANGE
        group_order = len(self.values)
        x_powers = self.ifft().values


        new_x_powers = []
        for i, x in enumerate(x_powers):
            new_x_powers.append((offset ** i) * x)  # x * offset^i

        new_x_powers += [Scalar(0)] * (group_order * 3)
        print(f"new_x_powers:{new_x_powers}")
        return Polynomial(new_x_powers, Basis.MONOMIAL).fft()

    # 将
    # Convert from offset form into coefficients
    # Note that we can't make a full inverse function of to_coset_extended_lagrange
    # because the output of this might be a deg >= n polynomial, which cannot
    # be expressed via evaluations at n roots of unity
    def coset_extended_lagrange_to_coeffs(self, offset):
        assert self.basis == Basis.LAGRANGE

        shifted_coeffs = self.ifft().values
        inv_offset = 1 / offset   # inv_offset 是offset的逆元。
        return Polynomial(
            [v * inv_offset**i for (i, v) in enumerate(shifted_coeffs)],
            Basis.MONOMIAL,
        )

    # Given a polynomial expressed as a list of evaluations at roots of unity,
    # evaluate it at x directly, without using an FFT to covert to coeffs first
    # 用重心插值法求出多项式的值，
    def barycentric_eval(self, x: Scalar):
        assert self.basis == Basis.LAGRANGE
        order = len(self.values)
        roots_of_unity = Scalar.roots_of_unity(order)
        return (
            (Scalar(x) ** order - 1)
            / order
            * sum(
                [
                    value * root / (x - root)
                    for value, root in zip(self.values, roots_of_unity)
                ]
            )
        )


def coset_extended_lagrange_test():
    lagrange_poly = Polynomial(
        # TODO(keep), 采用点值法表示，w =19540430494807482326159819597004422086093766032135589407132600596362845576832, 多项式点的坐标分别为 (w^0,1)，(w^1,2),(w^2,3),....(w^7,8)
        list(map(Scalar, [1, 2, 3, 4, 5, 6, 7, 8])), Basis.LAGRANGE
         )
    #原始多项式的点值表示:[1, 2, 3, 4, 5, 6, 7, 8]
    print(f"original lagrange poly:{lagrange_poly.values}")

    #原始多项式的系数表示:[10944121435919637611123202872628637544274182200208017171849102093287904247813, 16407567355707715082381689537916387329395994555403796510305004205827931381005, 21888242871839275220042445260109153167277707414472061641729655619866599103259, 16407567355707715086789610508212631171937308527291741914242101339246350165720, 10944121435919637611123202872628637544274182200208017171849102093287904247808, 5480675516131560135456795237044643916611055873124292429456102847329458329896, 2203960485148121921270656985943972701968548566709209392357, 5480675516131560139864716207340887759152369845012237833393199980747877114611]
    print(f"original coeff poly:{lagrange_poly.ifft().values}")

    #offset=1, 4倍扩展后的多项式的点值表示，注意在 1/4/8/..的位置上值分别为1/2/3... :[1, 10720100502214316017824502944044954065324060999235831025903844423091840349399, 9455244345631016631523862383826656817909262240618707851288319855253023724499, 2154739387933033111708037291544134707206872172371185076448386251812704236397, 2, 16557012320615716805371654510058109663243542056334255754346494402848129196434, 10961351032263120273117550959237409754492768732192557560880754261368126052155, 18363557546045068101357792595864568178482043948267994234220586583038506555553, 3, 6786126665617168635281695348901695604305505508243066572076512701156119512476, 12432998526208258595130464331726862113180416131685271896346981464741203555842, 17583891563112296716989958068669721717716064856305856073868243673723776631415, 4, 15235092695697612903221424418341788996225933052563558331936298540020231085964, 8526477789819225339470181130720054257555649678225561659213114114555273578202, 5748412396315429947679827564037304002141735973269128964907214524925412184424, 5, 8063712871896466710084708497040886506504371635794542014797783122244927830807, 12432998526208258595130464331726862113180416131685271896346981464741203555842, 6384725622872180445960462185068028976157210952995327774999033041321834967027, 6, 7423125919204651450688116196486815080908642277508115891487414498838949167610, 10961351032263120273117550959237409754492768732192557560880754261368126052155, 9959267747632339428749389803973233433288807182891237168523575569690515042210, 7, 1013927586174909651228671251775444917323622993703484604051271120508846640523, 9455244345631016631523862383826656817909262240618707851288319855253023724499, 12991963608384419706057798792240747034085871118455836070949939695446237712242, 8, 21753872925936258715284849814379405520357779078281283180193197937594190199291, 13327305889333084549971686500727188725472913714445501098547591469023253739310, 14366413615062333430482356679631362305114851397107572010875837406344246653236]
    lagrange_coset_poly= lagrange_poly.to_coset_extended_lagrange(Scalar(1))
    print(f"lagrange_coset_poly, offset=1:{lagrange_coset_poly.values}")

    #offset=3, 4倍扩展后的多项式的点值表示，:[20675515612179202962216070186424682162618199731614332091699429061672282694725, 12176233492423905554052088791734959941094267405154917767703273057334496166085, 5917415089377289121590408955785178409647352913589873293489444488775637989917, 2752516302388842277837843623414582965521620079164918619152523122629779608930, 4169562684247585045898683445974163076520306259872602444382940816087435294801, 405974129629722533167980246725276196790448647122578773059926554710976033469, 16015793353021219580113202927438566307249046400631465629394870428808273269385, 10229243472545473685325496616621056338434159122035619201636505490363604037700, 4169562684247576371110213902966280955214409584396047496175782248639266976338, 5253968865549839538799666481628166409324748755474067887542850034795390306731, 5448982845895345419151791205795466600592293409442070602404591982746410109803, 6744796520889898167112801401869255476407161332739834968662727069566758151892, 1212727259660075433733434172128159555676224428122393086708711186165050793241, 322967646151623184877638486520441134119498412968113624552408193959018243483, 18024183386365665400514884144185330956959959158139700997404651630096754818232, 19482052846986908588806741073994758113640633859705256434234817575288965077623, 1212727259660075433733434172128159555676224428122393086708711186165050794882, 15659316895809636090874968052002070000216252850695980391535423378600348077893, 18315716487236118541742198333943662698829243458507744564312431379090458965882, 10510595262562575074793025571744230189431857025973620441791605645111860961441, 17718680187591687002644623685987545382281998381222741064605327309226848205368, 20159325449435371029217238441388109380740194409091738508163099259089186272494, 18587891620308261463443330180410826574514602508103652153546608225475836828557, 394344664035779568888350307535643007895240871168234908270745822756040235999, 17718680187591695677433093228995427503587895056699296012812485876675016525145, 18932442747777939648604146512737863718784200643866598521373172345132630858224, 14094371321169798076091610182981744959720702465139535664999676136322953049480, 18314296007598656137037071170514820954670799413013319519063761129019823716627, 20675515612179202962216070186424682162618199731614332091699429061672282698004, 14642742260579063309391895968292213573123846477290141900862663922681188024125, 13036860255822678508584602795745598935228621688526128812938746661562717446865, 19125126410348967389184293215334753308191985897863333281980130891566402192292]
    lagrange_coset_poly= lagrange_poly.to_coset_extended_lagrange(Scalar(3))
    print(f"lagrange_coset_poly, offset =3 :{lagrange_coset_poly.values}")

    #offset =3, 消除4倍扩展后，多项式的系数表示，前8项系数不为0，剩余部分的系数均为0:[10944121435919637611123202872628637544274182200208017171849102093287904247813, 16407567355707715082381689537916387329395994555403796510305004205827931381005, 21888242871839275220042445260109153167277707414472061641729655619866599103259, 16407567355707715086789610508212631171937308527291741914242101339246350165720, 10944121435919637611123202872628637544274182200208017171849102093287904247808, 5480675516131560135456795237044643916611055873124292429456102847329458329896, 2203960485148121921270656985943972701968548566709209392357, 5480675516131560139864716207340887759152369845012237833393199980747877114611, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    # 前8项系数与原始多项式的系数相同。
    coeff_coset_poly1 = lagrange_coset_poly.coset_extended_lagrange_to_coeffs(Scalar(3))
    print(f"coeff_coset_poly, offset =3:{coeff_coset_poly1.values}")

def poly_sub_test():
    # f(x)= x^2+1, g(x)= x^2
    F = Polynomial(list(map(Scalar, [1,0,1])),Basis.MONOMIAL)
    G = Polynomial(list(map(Scalar, [0,0,1])),Basis.MONOMIAL)

    FMinusOne = F- Scalar(1)  ## 系数形式，直接f(x)-1
    assert G == FMinusOne

def poly_mul_test():
    # order 至少为f(x)*g(x)的最高次+1 向上取最近的2^k,例如f(x)*g(x)= x^4+x^2, order就至少=8， 当然等于16也是可以的。
    # 如果order != 2^k, 得到的结果不正确，怀疑和FFT要是2^k有关。
    # f(x)= x^2+1, g(x)= x^2
    F = Polynomial(list(map(Scalar, [1,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0])),Basis.MONOMIAL)
    G = Polynomial(list(map(Scalar, [0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,0])),Basis.MONOMIAL)

    # 先转换为点值形式
    F_eval = F.fft()
    G_eval = G.fft()

    # 点值相乘
    FG_eval = F_eval * G_eval
    FG= FG_eval.ifft()

    #FG:[0, 0, 1, 0, 1, 0, 0, 0]
    print(f"FG:{FG.values}")


def lagrange_poly_eval_test():
    # f(x)= x^2+1
    F = Polynomial(list(map(Scalar, [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])), Basis.MONOMIAL)
    F_eval = F.fft()

    y_2 = F_eval.barycentric_eval(2)
    print(f"y_2:{y_2}")

def fast_linear_combination_test():
    numbers = [5,11,6,15,12]
    factors = [1,2,4,8,16]
    print(f"numbers:{numbers}")
    bitlens = [len(bin(f)) - 2 for f in factors]  # bin(31) = 0b1111,所以要-2
    maxbitlen = max(bitlens)
    print(f"maxbitlen:{maxbitlen}")

    subsets = []
    for j in range(maxbitlen + 1):
        subset = set()
        for i in range(len(numbers)):
            if numbers[i] & (1 << j):
                subset.add(i)
        subsets.append(subset)
    print(f"subsets:{subsets}")

    subsets1 = [
        {i for i in range(len(numbers)) if numbers[i] & (1 << j)}
        for j in range(maxbitlen + 1)
    ]
    print(f"subsets1:{subsets1}")


if __name__ == "__main__":
    #coset_extended_lagrange_test()
    #poly_sub_test()
    # poly_mul_test()
    # lagrange_poly_eval_test()
    fast_linear_combination_test()
