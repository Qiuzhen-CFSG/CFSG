module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Words
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products00
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products01
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products02
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products03
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products04
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products05
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products06
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products07
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products08
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products09
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products10
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products11
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products12
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products13
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products14
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products15
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products16
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Threes.FusionCertificates.Products17

/-!
# Certified evaluations of the ambient J4 fusion words

Each group operation is transported through the faithful matrix inclusion.
Inverse steps use a checked right inverse, and powers use repeated squaring.
No simplicity, order, or conjugacy-class information about J4 is needed.
-/

@[expose] public section
namespace Janko4.Simplicity.ThreeFusion
open Janko4.GeneratorCertificates

private theorem mul_check {x y : Model} {xs ys zs : Vector ℕ 112}
    (hx : toMatrix x = decodeRows xs) (hy : toMatrix y = decodeRows ys)
    (h : packedMul xs ys = zs) : toMatrix (x * y) = decodeRows zs := by
  rw [map_mul, hx, hy, ← decode_packedMul, h]

private theorem inv_check {x : Model} {xs ys : Vector ℕ 112}
    (hx : toMatrix x = decodeRows xs)
    (h : packedMul xs ys = packedOne) : toMatrix x⁻¹ = decodeRows ys := by
  have hm : toMatrix x * decodeRows ys = 1 := by
    rw [hx, ← decode_packedMul, h, decode_packedOne]
  have he := congrArg (toMatrix x⁻¹ * ·) hm
  simpa only [← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, mul_one]
    using he.symm

variable (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)

theorem eval0 : toMatrix (w0 (a hA) (b hB)) = decodeRows r0 := by
  rfl

theorem eval1 : toMatrix (w1 (a hA) (b hB)) = decodeRows r1 := by
  rfl

theorem eval2 : toMatrix (w2 (a hA) (b hB)) = decodeRows r2 := by
  unfold w2
  exact mul_check (eval0 hA hB) (eval1 hA hB) p0

theorem eval3 : toMatrix (w3 (a hA) (b hB)) = decodeRows r3 := by
  unfold w3
  exact mul_check (eval1 hA hB) (eval0 hA hB) p1

theorem eval4 : toMatrix (w4 (a hA) (b hB)) = decodeRows r4 := by
  unfold w4
  have h1 : toMatrix ((w2 (a hA) (b hB)) ^ 1) = decodeRows r2 := by
    simpa only [pow_one] using (eval2 hA hB)
  have h2 : toMatrix ((w2 (a hA) (b hB)) ^ 2) = decodeRows q4_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p2
  have h4 : toMatrix ((w2 (a hA) (b hB)) ^ 4) = decodeRows q4_4 := by
    simpa only [← pow_add] using mul_check h2 h2 p3
  have h8 : toMatrix ((w2 (a hA) (b hB)) ^ 8) = decodeRows q4_8 := by
    simpa only [← pow_add] using mul_check h4 h4 p4
  have h16 : toMatrix ((w2 (a hA) (b hB)) ^ 16) = decodeRows r4 := by
    simpa only [← pow_add] using mul_check h8 h8 p5
  exact h16

theorem eval5 : toMatrix (w5 (a hA) (b hB)) = decodeRows r5 := by
  unfold w5
  exact inv_check (eval4 hA hB) p6

theorem eval6 : toMatrix (w6 (a hA) (b hB)) = decodeRows r6 := by
  unfold w6
  have h1 : toMatrix ((w3 (a hA) (b hB)) ^ 1) = decodeRows r3 := by
    simpa only [pow_one] using (eval3 hA hB)
  have h2 : toMatrix ((w3 (a hA) (b hB)) ^ 2) = decodeRows q6_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p7
  have h3 : toMatrix ((w3 (a hA) (b hB)) ^ 3) = decodeRows q6_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p8
  have h6 : toMatrix ((w3 (a hA) (b hB)) ^ 6) = decodeRows q6_6 := by
    simpa only [← pow_add] using mul_check h3 h3 p9
  have h12 : toMatrix ((w3 (a hA) (b hB)) ^ 12) = decodeRows q6_12 := by
    simpa only [← pow_add] using mul_check h6 h6 p10
  have h24 : toMatrix ((w3 (a hA) (b hB)) ^ 24) = decodeRows r6 := by
    simpa only [← pow_add] using mul_check h12 h12 p11
  exact h24

theorem eval7 : toMatrix (w7 (a hA) (b hB)) = decodeRows r7 := by
  unfold w7
  exact mul_check (eval5 hA hB) (eval6 hA hB) p12

theorem eval8 : toMatrix (w8 (a hA) (b hB)) = decodeRows r8 := by
  unfold w8
  have h1 : toMatrix ((w2 (a hA) (b hB)) ^ 1) = decodeRows r2 := by
    simpa only [pow_one] using (eval2 hA hB)
  have h2 : toMatrix ((w2 (a hA) (b hB)) ^ 2) = decodeRows q8_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p13
  have h3 : toMatrix ((w2 (a hA) (b hB)) ^ 3) = decodeRows r8 := by
    simpa only [← pow_add] using mul_check h1 h2 p14
  exact h3

theorem eval9 : toMatrix (w9 (a hA) (b hB)) = decodeRows r9 := by
  unfold w9
  exact mul_check (eval8 hA hB) (eval1 hA hB) p15

theorem eval10 : toMatrix (w10 (a hA) (b hB)) = decodeRows r10 := by
  unfold w10
  have h1 : toMatrix ((w9 (a hA) (b hB)) ^ 1) = decodeRows r9 := by
    simpa only [pow_one] using (eval9 hA hB)
  have h2 : toMatrix ((w9 (a hA) (b hB)) ^ 2) = decodeRows q10_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p16
  have h4 : toMatrix ((w9 (a hA) (b hB)) ^ 4) = decodeRows r10 := by
    simpa only [← pow_add] using mul_check h2 h2 p17
  exact h4

theorem eval11 : toMatrix (w11 (a hA) (b hB)) = decodeRows r11 := by
  unfold w11
  exact inv_check (eval7 hA hB) p18

theorem eval12 : toMatrix (w12 (a hA) (b hB)) = decodeRows r12 := by
  unfold w12
  exact mul_check (eval11 hA hB) (eval10 hA hB) p19

theorem eval13 : toMatrix (w13 (a hA) (b hB)) = decodeRows r13 := by
  unfold w13
  exact mul_check (eval12 hA hB) (eval7 hA hB) p20

theorem eval14 : toMatrix (w14 (a hA) (b hB)) = decodeRows r14 := by
  unfold w14
  have h1 : toMatrix ((w3 (a hA) (b hB)) ^ 1) = decodeRows r3 := by
    simpa only [pow_one] using (eval3 hA hB)
  have h2 : toMatrix ((w3 (a hA) (b hB)) ^ 2) = decodeRows q14_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p21
  have h4 : toMatrix ((w3 (a hA) (b hB)) ^ 4) = decodeRows q14_4 := by
    simpa only [← pow_add] using mul_check h2 h2 p22
  have h8 : toMatrix ((w3 (a hA) (b hB)) ^ 8) = decodeRows r14 := by
    simpa only [← pow_add] using mul_check h4 h4 p23
  exact h8

theorem eval15 : toMatrix (w15 (a hA) (b hB)) = decodeRows r15 := by
  unfold w15
  exact mul_check (eval2 hA hB) (eval14 hA hB) p24

theorem eval16 : toMatrix (w16 (a hA) (b hB)) = decodeRows r16 := by
  unfold w16
  have h1 : toMatrix ((w2 (a hA) (b hB)) ^ 1) = decodeRows r2 := by
    simpa only [pow_one] using (eval2 hA hB)
  have h2 : toMatrix ((w2 (a hA) (b hB)) ^ 2) = decodeRows q16_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p25
  have h4 : toMatrix ((w2 (a hA) (b hB)) ^ 4) = decodeRows q16_4 := by
    simpa only [← pow_add] using mul_check h2 h2 p26
  have h3 : toMatrix ((w2 (a hA) (b hB)) ^ 3) = decodeRows q16_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p27
  have h5 : toMatrix ((w2 (a hA) (b hB)) ^ 5) = decodeRows q16_5 := by
    simpa only [← pow_add] using mul_check h2 h3 p28
  have h9 : toMatrix ((w2 (a hA) (b hB)) ^ 9) = decodeRows q16_9 := by
    simpa only [← pow_add] using mul_check h4 h5 p29
  have h18 : toMatrix ((w2 (a hA) (b hB)) ^ 18) = decodeRows r16 := by
    simpa only [← pow_add] using mul_check h9 h9 p30
  exact h18

theorem eval17 : toMatrix (w17 (a hA) (b hB)) = decodeRows r17 := by
  unfold w17
  exact mul_check (eval15 hA hB) (eval16 hA hB) p31

theorem eval18 : toMatrix (w18 (a hA) (b hB)) = decodeRows r18 := by
  unfold w18
  exact inv_check (eval17 hA hB) p32

theorem eval19 : toMatrix (w19 (a hA) (b hB)) = decodeRows r19 := by
  unfold w19
  exact mul_check (eval18 hA hB) (eval0 hA hB) p33

theorem eval20 : toMatrix (w20 (a hA) (b hB)) = decodeRows r20 := by
  unfold w20
  exact mul_check (eval19 hA hB) (eval17 hA hB) p34

theorem eval21 : toMatrix (w21 (a hA) (b hB)) = decodeRows r21 := by
  unfold w21
  exact mul_check (eval20 hA hB) (eval13 hA hB) p35

theorem eval22 : toMatrix (w22 (a hA) (b hB)) = decodeRows r22 := by
  unfold w22
  exact mul_check (eval21 hA hB) (eval20 hA hB) p36

theorem eval23 : toMatrix (w23 (a hA) (b hB)) = decodeRows r23 := by
  unfold w23
  exact mul_check (eval22 hA hB) (eval13 hA hB) p37

theorem eval24 : toMatrix (w24 (a hA) (b hB)) = decodeRows r24 := by
  unfold w24
  exact mul_check (eval23 hA hB) (eval13 hA hB) p38

theorem eval25 : toMatrix (w25 (a hA) (b hB)) = decodeRows r25 := by
  unfold w25
  exact mul_check (eval24 hA hB) (eval13 hA hB) p39

theorem eval26 : toMatrix (w26 (a hA) (b hB)) = decodeRows r26 := by
  unfold w26
  exact mul_check (eval25 hA hB) (eval13 hA hB) p40

theorem eval27 : toMatrix (w27 (a hA) (b hB)) = decodeRows r27 := by
  unfold w27
  exact mul_check (eval26 hA hB) (eval13 hA hB) p41

theorem eval28 : toMatrix (w28 (a hA) (b hB)) = decodeRows r28 := by
  unfold w28
  exact mul_check (eval21 hA hB) (eval13 hA hB) p42

theorem eval29 : toMatrix (w29 (a hA) (b hB)) = decodeRows r29 := by
  unfold w29
  exact mul_check (eval28 hA hB) (eval20 hA hB) p43

theorem eval30 : toMatrix (w30 (a hA) (b hB)) = decodeRows r30 := by
  unfold w30
  exact mul_check (eval29 hA hB) (eval13 hA hB) p44

theorem eval31 : toMatrix (w31 (a hA) (b hB)) = decodeRows r31 := by
  unfold w31
  exact mul_check (eval30 hA hB) (eval13 hA hB) p45

theorem eval32 : toMatrix (w32 (a hA) (b hB)) = decodeRows r32 := by
  unfold w32
  exact mul_check (eval31 hA hB) (eval13 hA hB) p46

theorem eval33 : toMatrix (w33 (a hA) (b hB)) = decodeRows r33 := by
  unfold w33
  exact mul_check (eval32 hA hB) (eval20 hA hB) p47

theorem eval34 : toMatrix (w34 (a hA) (b hB)) = decodeRows r34 := by
  unfold w34
  exact mul_check (eval33 hA hB) (eval13 hA hB) p48

theorem eval35 : toMatrix (w35 (a hA) (b hB)) = decodeRows r35 := by
  unfold w35
  exact mul_check (eval34 hA hB) (eval13 hA hB) p49

theorem eval36 : toMatrix (w36 (a hA) (b hB)) = decodeRows r36 := by
  unfold w36
  exact mul_check (eval35 hA hB) (eval13 hA hB) p50

theorem eval37 : toMatrix (w37 (a hA) (b hB)) = decodeRows r37 := by
  unfold w37
  exact mul_check (eval36 hA hB) (eval13 hA hB) p51

theorem eval38 : toMatrix (w38 (a hA) (b hB)) = decodeRows r38 := by
  unfold w38
  exact inv_check (eval27 hA hB) p52

theorem eval39 : toMatrix (w39 (a hA) (b hB)) = decodeRows r39 := by
  unfold w39
  exact inv_check (eval37 hA hB) p53

theorem eval40 : toMatrix (w40 (a hA) (b hB)) = decodeRows r40 := by
  unfold w40
  exact mul_check (eval38 hA hB) (eval39 hA hB) p54

theorem eval41 : toMatrix (w41 (a hA) (b hB)) = decodeRows r41 := by
  unfold w41
  exact mul_check (eval40 hA hB) (eval27 hA hB) p55

theorem eval42 : toMatrix (w42 (a hA) (b hB)) = decodeRows r42 := by
  unfold w42
  exact mul_check (eval41 hA hB) (eval37 hA hB) p56

theorem eval43 : toMatrix (w43 (a hA) (b hB)) = decodeRows r43 := by
  unfold w43
  exact mul_check (eval2 hA hB) (eval1 hA hB) p57

theorem eval44 : toMatrix (w44 (a hA) (b hB)) = decodeRows r44 := by
  unfold w44
  exact mul_check (eval43 hA hB) (eval0 hA hB) p58

theorem eval45 : toMatrix (w45 (a hA) (b hB)) = decodeRows r45 := by
  unfold w45
  exact mul_check (eval44 hA hB) (eval1 hA hB) p59

theorem eval46 : toMatrix (w46 (a hA) (b hB)) = decodeRows r46 := by
  unfold w46
  exact mul_check (eval45 hA hB) (eval0 hA hB) p60

theorem eval47 : toMatrix (w47 (a hA) (b hB)) = decodeRows r47 := by
  unfold w47
  exact mul_check (eval46 hA hB) (eval1 hA hB) p61

theorem eval48 : toMatrix (w48 (a hA) (b hB)) = decodeRows r48 := by
  unfold w48
  exact mul_check (eval47 hA hB) (eval0 hA hB) p62

theorem eval49 : toMatrix (w49 (a hA) (b hB)) = decodeRows r49 := by
  unfold w49
  exact mul_check (eval48 hA hB) (eval1 hA hB) p63

theorem eval50 : toMatrix (w50 (a hA) (b hB)) = decodeRows r50 := by
  unfold w50
  exact mul_check (eval49 hA hB) (eval1 hA hB) p64

theorem eval51 : toMatrix (w51 (a hA) (b hB)) = decodeRows r51 := by
  unfold w51
  have h1 : toMatrix ((w50 (a hA) (b hB)) ^ 1) = decodeRows r50 := by
    simpa only [pow_one] using (eval50 hA hB)
  have h2 : toMatrix ((w50 (a hA) (b hB)) ^ 2) = decodeRows q51_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p65
  have h3 : toMatrix ((w50 (a hA) (b hB)) ^ 3) = decodeRows q51_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p66
  have h5 : toMatrix ((w50 (a hA) (b hB)) ^ 5) = decodeRows q51_5 := by
    simpa only [← pow_add] using mul_check h2 h3 p67
  have h6 : toMatrix ((w50 (a hA) (b hB)) ^ 6) = decodeRows q51_6 := by
    simpa only [← pow_add] using mul_check h3 h3 p68
  have h11 : toMatrix ((w50 (a hA) (b hB)) ^ 11) = decodeRows q51_11 := by
    simpa only [← pow_add] using mul_check h5 h6 p69
  have h22 : toMatrix ((w50 (a hA) (b hB)) ^ 22) = decodeRows r51 := by
    simpa only [← pow_add] using mul_check h11 h11 p70
  exact h22

theorem eval52 : toMatrix (w52 (a hA) (b hB)) = decodeRows r52 := by
  unfold w52
  have h1 : toMatrix ((w50 (a hA) (b hB)) ^ 1) = decodeRows r50 := by
    simpa only [pow_one] using (eval50 hA hB)
  have h2 : toMatrix ((w50 (a hA) (b hB)) ^ 2) = decodeRows q52_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p71
  have h4 : toMatrix ((w50 (a hA) (b hB)) ^ 4) = decodeRows q52_4 := by
    simpa only [← pow_add] using mul_check h2 h2 p72
  have h8 : toMatrix ((w50 (a hA) (b hB)) ^ 8) = decodeRows q52_8 := by
    simpa only [← pow_add] using mul_check h4 h4 p73
  have h16 : toMatrix ((w50 (a hA) (b hB)) ^ 16) = decodeRows q52_16 := by
    simpa only [← pow_add] using mul_check h8 h8 p74
  have h3 : toMatrix ((w50 (a hA) (b hB)) ^ 3) = decodeRows q52_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p75
  have h5 : toMatrix ((w50 (a hA) (b hB)) ^ 5) = decodeRows q52_5 := by
    simpa only [← pow_add] using mul_check h2 h3 p76
  have h9 : toMatrix ((w50 (a hA) (b hB)) ^ 9) = decodeRows q52_9 := by
    simpa only [← pow_add] using mul_check h4 h5 p77
  have h17 : toMatrix ((w50 (a hA) (b hB)) ^ 17) = decodeRows q52_17 := by
    simpa only [← pow_add] using mul_check h8 h9 p78
  have h33 : toMatrix ((w50 (a hA) (b hB)) ^ 33) = decodeRows r52 := by
    simpa only [← pow_add] using mul_check h16 h17 p79
  exact h33

theorem eval53 : toMatrix (w53 (a hA) (b hB)) = decodeRows r53 := by
  unfold w53
  have h1 : toMatrix ((w1 (a hA) (b hB)) ^ 1) = decodeRows r1 := by
    simpa only [pow_one] using (eval1 hA hB)
  have h2 : toMatrix ((w1 (a hA) (b hB)) ^ 2) = decodeRows r53 := by
    simpa only [← pow_add] using mul_check h1 h1 p80
  exact h2

theorem eval54 : toMatrix (w54 (a hA) (b hB)) = decodeRows r54 := by
  unfold w54
  have h1 : toMatrix ((w1 (a hA) (b hB)) ^ 1) = decodeRows r1 := by
    simpa only [pow_one] using (eval1 hA hB)
  have h2 : toMatrix ((w1 (a hA) (b hB)) ^ 2) = decodeRows q54_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p81
  have h3 : toMatrix ((w1 (a hA) (b hB)) ^ 3) = decodeRows r54 := by
    simpa only [← pow_add] using mul_check h1 h2 p82
  exact h3

theorem eval55 : toMatrix (w55 (a hA) (b hB)) = decodeRows r55 := by
  unfold w55
  exact mul_check (eval0 hA hB) (eval54 hA hB) p83

theorem eval56 : toMatrix (w56 (a hA) (b hB)) = decodeRows r56 := by
  unfold w56
  exact mul_check (eval2 hA hB) (eval0 hA hB) p84

theorem eval57 : toMatrix (w57 (a hA) (b hB)) = decodeRows r57 := by
  unfold w57
  exact mul_check (eval53 hA hB) (eval55 hA hB) p85

theorem eval58 : toMatrix (w58 (a hA) (b hB)) = decodeRows r58 := by
  unfold w58
  exact mul_check (eval57 hA hB) (eval43 hA hB) p86

theorem eval59 : toMatrix (w59 (a hA) (b hB)) = decodeRows r59 := by
  unfold w59
  exact mul_check (eval58 hA hB) (eval1 hA hB) p87

theorem eval60 : toMatrix (w60 (a hA) (b hB)) = decodeRows r60 := by
  unfold w60
  exact mul_check (eval59 hA hB) (eval55 hA hB) p88

theorem eval61 : toMatrix (w61 (a hA) (b hB)) = decodeRows r61 := by
  unfold w61
  exact mul_check (eval60 hA hB) (eval1 hA hB) p89

theorem eval62 : toMatrix (w62 (a hA) (b hB)) = decodeRows r62 := by
  unfold w62
  exact mul_check (eval61 hA hB) (eval1 hA hB) p90

theorem eval63 : toMatrix (w63 (a hA) (b hB)) = decodeRows r63 := by
  unfold w63
  exact mul_check (eval62 hA hB) (eval55 hA hB) p91

theorem eval64 : toMatrix (w64 (a hA) (b hB)) = decodeRows r64 := by
  unfold w64
  exact mul_check (eval63 hA hB) (eval2 hA hB) p92

theorem eval65 : toMatrix (w65 (a hA) (b hB)) = decodeRows r65 := by
  unfold w65
  exact mul_check (eval64 hA hB) (eval55 hA hB) p93

theorem eval66 : toMatrix (w66 (a hA) (b hB)) = decodeRows r66 := by
  unfold w66
  exact mul_check (eval65 hA hB) (eval55 hA hB) p94

theorem eval67 : toMatrix (w67 (a hA) (b hB)) = decodeRows r67 := by
  unfold w67
  exact mul_check (eval66 hA hB) (eval43 hA hB) p95

theorem eval68 : toMatrix (w68 (a hA) (b hB)) = decodeRows r68 := by
  unfold w68
  exact inv_check (eval67 hA hB) p96

theorem eval69 : toMatrix (w69 (a hA) (b hB)) = decodeRows r69 := by
  unfold w69
  exact mul_check (eval68 hA hB) (eval20 hA hB) p97

theorem eval70 : toMatrix (w70 (a hA) (b hB)) = decodeRows r70 := by
  unfold w70
  exact mul_check (eval69 hA hB) (eval67 hA hB) p98

theorem eval71 : toMatrix (w71 (a hA) (b hB)) = decodeRows r71 := by
  unfold w71
  exact mul_check (eval20 hA hB) (eval70 hA hB) p99

theorem eval72 : toMatrix (w72 (a hA) (b hB)) = decodeRows r72 := by
  unfold w72
  have h1 : toMatrix ((w71 (a hA) (b hB)) ^ 1) = decodeRows r71 := by
    simpa only [pow_one] using (eval71 hA hB)
  have h2 : toMatrix ((w71 (a hA) (b hB)) ^ 2) = decodeRows q72_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p100
  have h3 : toMatrix ((w71 (a hA) (b hB)) ^ 3) = decodeRows q72_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p101
  have h6 : toMatrix ((w71 (a hA) (b hB)) ^ 6) = decodeRows r72 := by
    simpa only [← pow_add] using mul_check h3 h3 p102
  exact h6

theorem eval73 : toMatrix (w73 (a hA) (b hB)) = decodeRows r73 := by
  unfold w73
  exact mul_check (eval55 hA hB) (eval55 hA hB) p103

theorem eval74 : toMatrix (w74 (a hA) (b hB)) = decodeRows r74 := by
  unfold w74
  exact mul_check (eval73 hA hB) (eval2 hA hB) p104

theorem eval75 : toMatrix (w75 (a hA) (b hB)) = decodeRows r75 := by
  unfold w75
  exact mul_check (eval74 hA hB) (eval55 hA hB) p105

theorem eval76 : toMatrix (w76 (a hA) (b hB)) = decodeRows r76 := by
  unfold w76
  exact mul_check (eval75 hA hB) (eval0 hA hB) p106

theorem eval77 : toMatrix (w77 (a hA) (b hB)) = decodeRows r77 := by
  unfold w77
  exact mul_check (eval76 hA hB) (eval55 hA hB) p107

theorem eval78 : toMatrix (w78 (a hA) (b hB)) = decodeRows r78 := by
  unfold w78
  exact mul_check (eval77 hA hB) (eval55 hA hB) p108

theorem eval79 : toMatrix (w79 (a hA) (b hB)) = decodeRows r79 := by
  unfold w79
  exact mul_check (eval78 hA hB) (eval43 hA hB) p109

theorem eval80 : toMatrix (w80 (a hA) (b hB)) = decodeRows r80 := by
  unfold w80
  exact mul_check (eval79 hA hB) (eval1 hA hB) p110

theorem eval81 : toMatrix (w81 (a hA) (b hB)) = decodeRows r81 := by
  unfold w81
  exact mul_check (eval80 hA hB) (eval55 hA hB) p111

theorem eval82 : toMatrix (w82 (a hA) (b hB)) = decodeRows r82 := by
  unfold w82
  exact mul_check (eval81 hA hB) (eval2 hA hB) p112

theorem eval83 : toMatrix (w83 (a hA) (b hB)) = decodeRows r83 := by
  unfold w83
  exact mul_check (eval82 hA hB) (eval1 hA hB) p113

theorem eval84 : toMatrix (w84 (a hA) (b hB)) = decodeRows r84 := by
  unfold w84
  exact mul_check (eval83 hA hB) (eval43 hA hB) p114

theorem eval85 : toMatrix (w85 (a hA) (b hB)) = decodeRows r85 := by
  unfold w85
  exact mul_check (eval84 hA hB) (eval1 hA hB) p115

theorem eval86 : toMatrix (w86 (a hA) (b hB)) = decodeRows r86 := by
  unfold w86
  exact mul_check (eval85 hA hB) (eval43 hA hB) p116

theorem eval87 : toMatrix (w87 (a hA) (b hB)) = decodeRows r87 := by
  unfold w87
  exact inv_check (eval86 hA hB) p117

theorem eval88 : toMatrix (w88 (a hA) (b hB)) = decodeRows r88 := by
  unfold w88
  exact mul_check (eval87 hA hB) (eval20 hA hB) p118

theorem eval89 : toMatrix (w89 (a hA) (b hB)) = decodeRows r89 := by
  unfold w89
  exact mul_check (eval88 hA hB) (eval86 hA hB) p119

theorem eval90 : toMatrix (w90 (a hA) (b hB)) = decodeRows r90 := by
  unfold w90
  exact mul_check (eval20 hA hB) (eval89 hA hB) p120

theorem eval91 : toMatrix (w91 (a hA) (b hB)) = decodeRows r91 := by
  unfold w91
  have h1 : toMatrix ((w90 (a hA) (b hB)) ^ 1) = decodeRows r90 := by
    simpa only [pow_one] using (eval90 hA hB)
  have h2 : toMatrix ((w90 (a hA) (b hB)) ^ 2) = decodeRows q91_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p121
  have h3 : toMatrix ((w90 (a hA) (b hB)) ^ 3) = decodeRows q91_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p122
  have h6 : toMatrix ((w90 (a hA) (b hB)) ^ 6) = decodeRows r91 := by
    simpa only [← pow_add] using mul_check h3 h3 p123
  exact h6

theorem eval92 : toMatrix (w92 (a hA) (b hB)) = decodeRows r92 := by
  unfold w92
  exact mul_check (eval2 hA hB) (eval43 hA hB) p124

theorem eval93 : toMatrix (w93 (a hA) (b hB)) = decodeRows r93 := by
  unfold w93
  exact mul_check (eval92 hA hB) (eval1 hA hB) p125

theorem eval94 : toMatrix (w94 (a hA) (b hB)) = decodeRows r94 := by
  unfold w94
  exact mul_check (eval93 hA hB) (eval43 hA hB) p126

theorem eval95 : toMatrix (w95 (a hA) (b hB)) = decodeRows r95 := by
  unfold w95
  exact mul_check (eval94 hA hB) (eval2 hA hB) p127

theorem eval96 : toMatrix (w96 (a hA) (b hB)) = decodeRows r96 := by
  unfold w96
  exact mul_check (eval95 hA hB) (eval55 hA hB) p128

theorem eval97 : toMatrix (w97 (a hA) (b hB)) = decodeRows r97 := by
  unfold w97
  exact mul_check (eval96 hA hB) (eval55 hA hB) p129

theorem eval98 : toMatrix (w98 (a hA) (b hB)) = decodeRows r98 := by
  unfold w98
  exact mul_check (eval97 hA hB) (eval55 hA hB) p130

theorem eval99 : toMatrix (w99 (a hA) (b hB)) = decodeRows r99 := by
  unfold w99
  exact mul_check (eval98 hA hB) (eval55 hA hB) p131

theorem eval100 : toMatrix (w100 (a hA) (b hB)) = decodeRows r100 := by
  unfold w100
  exact mul_check (eval99 hA hB) (eval43 hA hB) p132

theorem eval101 : toMatrix (w101 (a hA) (b hB)) = decodeRows r101 := by
  unfold w101
  exact inv_check (eval100 hA hB) p133

theorem eval102 : toMatrix (w102 (a hA) (b hB)) = decodeRows r102 := by
  unfold w102
  exact mul_check (eval101 hA hB) (eval20 hA hB) p134

theorem eval103 : toMatrix (w103 (a hA) (b hB)) = decodeRows r103 := by
  unfold w103
  exact mul_check (eval102 hA hB) (eval100 hA hB) p135

theorem eval104 : toMatrix (w104 (a hA) (b hB)) = decodeRows r104 := by
  unfold w104
  exact mul_check (eval20 hA hB) (eval103 hA hB) p136

theorem eval105 : toMatrix (w105 (a hA) (b hB)) = decodeRows r105 := by
  unfold w105
  have h1 : toMatrix ((w104 (a hA) (b hB)) ^ 1) = decodeRows r104 := by
    simpa only [pow_one] using (eval104 hA hB)
  have h2 : toMatrix ((w104 (a hA) (b hB)) ^ 2) = decodeRows q105_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p137
  have h3 : toMatrix ((w104 (a hA) (b hB)) ^ 3) = decodeRows q105_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p138
  have h6 : toMatrix ((w104 (a hA) (b hB)) ^ 6) = decodeRows r105 := by
    simpa only [← pow_add] using mul_check h3 h3 p139
  exact h6

theorem eval106 : toMatrix (w106 (a hA) (b hB)) = decodeRows r106 := by
  unfold w106
  exact mul_check (eval1 hA hB) (eval55 hA hB) p140

theorem eval107 : toMatrix (w107 (a hA) (b hB)) = decodeRows r107 := by
  unfold w107
  exact mul_check (eval106 hA hB) (eval43 hA hB) p141

theorem eval108 : toMatrix (w108 (a hA) (b hB)) = decodeRows r108 := by
  unfold w108
  exact mul_check (eval107 hA hB) (eval1 hA hB) p142

theorem eval109 : toMatrix (w109 (a hA) (b hB)) = decodeRows r109 := by
  unfold w109
  exact mul_check (eval108 hA hB) (eval2 hA hB) p143

theorem eval110 : toMatrix (w110 (a hA) (b hB)) = decodeRows r110 := by
  unfold w110
  exact mul_check (eval109 hA hB) (eval55 hA hB) p144

theorem eval111 : toMatrix (w111 (a hA) (b hB)) = decodeRows r111 := by
  unfold w111
  exact mul_check (eval110 hA hB) (eval0 hA hB) p145

theorem eval112 : toMatrix (w112 (a hA) (b hB)) = decodeRows r112 := by
  unfold w112
  exact mul_check (eval111 hA hB) (eval43 hA hB) p146

theorem eval113 : toMatrix (w113 (a hA) (b hB)) = decodeRows r113 := by
  unfold w113
  exact mul_check (eval112 hA hB) (eval2 hA hB) p147

theorem eval114 : toMatrix (w114 (a hA) (b hB)) = decodeRows r114 := by
  unfold w114
  exact mul_check (eval113 hA hB) (eval0 hA hB) p148

theorem eval115 : toMatrix (w115 (a hA) (b hB)) = decodeRows r115 := by
  unfold w115
  exact mul_check (eval114 hA hB) (eval55 hA hB) p149

theorem eval116 : toMatrix (w116 (a hA) (b hB)) = decodeRows r116 := by
  unfold w116
  exact mul_check (eval115 hA hB) (eval2 hA hB) p150

theorem eval117 : toMatrix (w117 (a hA) (b hB)) = decodeRows r117 := by
  unfold w117
  exact mul_check (eval116 hA hB) (eval2 hA hB) p151

theorem eval118 : toMatrix (w118 (a hA) (b hB)) = decodeRows r118 := by
  unfold w118
  exact mul_check (eval117 hA hB) (eval0 hA hB) p152

theorem eval119 : toMatrix (w119 (a hA) (b hB)) = decodeRows r119 := by
  unfold w119
  exact inv_check (eval118 hA hB) p153

theorem eval120 : toMatrix (w120 (a hA) (b hB)) = decodeRows r120 := by
  unfold w120
  exact mul_check (eval119 hA hB) (eval20 hA hB) p154

theorem eval121 : toMatrix (w121 (a hA) (b hB)) = decodeRows r121 := by
  unfold w121
  exact mul_check (eval120 hA hB) (eval118 hA hB) p155

theorem eval122 : toMatrix (w122 (a hA) (b hB)) = decodeRows r122 := by
  unfold w122
  exact mul_check (eval20 hA hB) (eval121 hA hB) p156

theorem eval123 : toMatrix (w123 (a hA) (b hB)) = decodeRows r123 := by
  unfold w123
  have h1 : toMatrix ((w122 (a hA) (b hB)) ^ 1) = decodeRows r122 := by
    simpa only [pow_one] using (eval122 hA hB)
  have h2 : toMatrix ((w122 (a hA) (b hB)) ^ 2) = decodeRows q123_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p157
  have h3 : toMatrix ((w122 (a hA) (b hB)) ^ 3) = decodeRows r123 := by
    simpa only [← pow_add] using mul_check h1 h2 p158
  exact h3

theorem eval124 : toMatrix (w124 (a hA) (b hB)) = decodeRows r124 := by
  unfold w124
  exact mul_check (eval95 hA hB) (eval0 hA hB) p159

theorem eval125 : toMatrix (w125 (a hA) (b hB)) = decodeRows r125 := by
  unfold w125
  exact mul_check (eval124 hA hB) (eval1 hA hB) p160

theorem eval126 : toMatrix (w126 (a hA) (b hB)) = decodeRows r126 := by
  unfold w126
  exact mul_check (eval125 hA hB) (eval55 hA hB) p161

theorem eval127 : toMatrix (w127 (a hA) (b hB)) = decodeRows r127 := by
  unfold w127
  exact mul_check (eval126 hA hB) (eval55 hA hB) p162

theorem eval128 : toMatrix (w128 (a hA) (b hB)) = decodeRows r128 := by
  unfold w128
  exact mul_check (eval127 hA hB) (eval43 hA hB) p163

theorem eval129 : toMatrix (w129 (a hA) (b hB)) = decodeRows r129 := by
  unfold w129
  exact mul_check (eval128 hA hB) (eval43 hA hB) p164

theorem eval130 : toMatrix (w130 (a hA) (b hB)) = decodeRows r130 := by
  unfold w130
  exact mul_check (eval129 hA hB) (eval2 hA hB) p165

theorem eval131 : toMatrix (w131 (a hA) (b hB)) = decodeRows r131 := by
  unfold w131
  exact mul_check (eval130 hA hB) (eval1 hA hB) p166

theorem eval132 : toMatrix (w132 (a hA) (b hB)) = decodeRows r132 := by
  unfold w132
  exact mul_check (eval131 hA hB) (eval55 hA hB) p167

theorem eval133 : toMatrix (w133 (a hA) (b hB)) = decodeRows r133 := by
  unfold w133
  exact mul_check (eval132 hA hB) (eval55 hA hB) p168

theorem eval134 : toMatrix (w134 (a hA) (b hB)) = decodeRows r134 := by
  unfold w134
  exact mul_check (eval133 hA hB) (eval1 hA hB) p169

theorem eval135 : toMatrix (w135 (a hA) (b hB)) = decodeRows r135 := by
  unfold w135
  exact inv_check (eval134 hA hB) p170

theorem eval136 : toMatrix (w136 (a hA) (b hB)) = decodeRows r136 := by
  unfold w136
  exact mul_check (eval135 hA hB) (eval20 hA hB) p171

theorem eval137 : toMatrix (w137 (a hA) (b hB)) = decodeRows r137 := by
  unfold w137
  exact mul_check (eval136 hA hB) (eval134 hA hB) p172

theorem eval138 : toMatrix (w138 (a hA) (b hB)) = decodeRows r138 := by
  unfold w138
  exact mul_check (eval20 hA hB) (eval137 hA hB) p173

theorem eval139 : toMatrix (w139 (a hA) (b hB)) = decodeRows r139 := by
  unfold w139
  have h1 : toMatrix ((w138 (a hA) (b hB)) ^ 1) = decodeRows r138 := by
    simpa only [pow_one] using (eval138 hA hB)
  have h2 : toMatrix ((w138 (a hA) (b hB)) ^ 2) = decodeRows q139_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p174
  have h3 : toMatrix ((w138 (a hA) (b hB)) ^ 3) = decodeRows q139_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p175
  have h6 : toMatrix ((w138 (a hA) (b hB)) ^ 6) = decodeRows r139 := by
    simpa only [← pow_add] using mul_check h3 h3 p176
  exact h6

theorem eval140 : toMatrix (w140 (a hA) (b hB)) = decodeRows r140 := by
  unfold w140
  exact mul_check (eval55 hA hB) (eval2 hA hB) p177

theorem eval141 : toMatrix (w141 (a hA) (b hB)) = decodeRows r141 := by
  unfold w141
  exact mul_check (eval140 hA hB) (eval1 hA hB) p178

theorem eval142 : toMatrix (w142 (a hA) (b hB)) = decodeRows r142 := by
  unfold w142
  exact mul_check (eval141 hA hB) (eval43 hA hB) p179

theorem eval143 : toMatrix (w143 (a hA) (b hB)) = decodeRows r143 := by
  unfold w143
  exact mul_check (eval142 hA hB) (eval43 hA hB) p180

theorem eval144 : toMatrix (w144 (a hA) (b hB)) = decodeRows r144 := by
  unfold w144
  exact mul_check (eval143 hA hB) (eval43 hA hB) p181

theorem eval145 : toMatrix (w145 (a hA) (b hB)) = decodeRows r145 := by
  unfold w145
  exact mul_check (eval144 hA hB) (eval55 hA hB) p182

theorem eval146 : toMatrix (w146 (a hA) (b hB)) = decodeRows r146 := by
  unfold w146
  exact mul_check (eval145 hA hB) (eval1 hA hB) p183

theorem eval147 : toMatrix (w147 (a hA) (b hB)) = decodeRows r147 := by
  unfold w147
  exact mul_check (eval146 hA hB) (eval43 hA hB) p184

theorem eval148 : toMatrix (w148 (a hA) (b hB)) = decodeRows r148 := by
  unfold w148
  exact mul_check (eval147 hA hB) (eval43 hA hB) p185

theorem eval149 : toMatrix (w149 (a hA) (b hB)) = decodeRows r149 := by
  unfold w149
  exact mul_check (eval148 hA hB) (eval55 hA hB) p186

theorem eval150 : toMatrix (w150 (a hA) (b hB)) = decodeRows r150 := by
  unfold w150
  exact mul_check (eval149 hA hB) (eval2 hA hB) p187

theorem eval151 : toMatrix (w151 (a hA) (b hB)) = decodeRows r151 := by
  unfold w151
  exact mul_check (eval150 hA hB) (eval0 hA hB) p188

theorem eval152 : toMatrix (w152 (a hA) (b hB)) = decodeRows r152 := by
  unfold w152
  exact mul_check (eval151 hA hB) (eval1 hA hB) p189

theorem eval153 : toMatrix (w153 (a hA) (b hB)) = decodeRows r153 := by
  unfold w153
  exact mul_check (eval152 hA hB) (eval55 hA hB) p190

theorem eval154 : toMatrix (w154 (a hA) (b hB)) = decodeRows r154 := by
  unfold w154
  exact inv_check (eval153 hA hB) p191

theorem eval155 : toMatrix (w155 (a hA) (b hB)) = decodeRows r155 := by
  unfold w155
  exact mul_check (eval154 hA hB) (eval20 hA hB) p192

theorem eval156 : toMatrix (w156 (a hA) (b hB)) = decodeRows r156 := by
  unfold w156
  exact mul_check (eval155 hA hB) (eval153 hA hB) p193

theorem eval157 : toMatrix (w157 (a hA) (b hB)) = decodeRows r157 := by
  unfold w157
  exact mul_check (eval20 hA hB) (eval156 hA hB) p194

theorem eval158 : toMatrix (w158 (a hA) (b hB)) = decodeRows r158 := by
  unfold w158
  have h1 : toMatrix ((w157 (a hA) (b hB)) ^ 1) = decodeRows r157 := by
    simpa only [pow_one] using (eval157 hA hB)
  have h2 : toMatrix ((w157 (a hA) (b hB)) ^ 2) = decodeRows q158_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p195
  have h3 : toMatrix ((w157 (a hA) (b hB)) ^ 3) = decodeRows q158_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p196
  have h5 : toMatrix ((w157 (a hA) (b hB)) ^ 5) = decodeRows r158 := by
    simpa only [← pow_add] using mul_check h2 h3 p197
  exact h5

theorem eval159 : toMatrix (w159 (a hA) (b hB)) = decodeRows r159 := by
  unfold w159
  exact mul_check (eval153 hA hB) (eval158 hA hB) p198

theorem eval160 : toMatrix (w160 (a hA) (b hB)) = decodeRows r160 := by
  unfold w160
  exact mul_check (eval53 hA hB) (eval2 hA hB) p199

theorem eval161 : toMatrix (w161 (a hA) (b hB)) = decodeRows r161 := by
  unfold w161
  exact mul_check (eval160 hA hB) (eval2 hA hB) p200

theorem eval162 : toMatrix (w162 (a hA) (b hB)) = decodeRows r162 := by
  unfold w162
  exact mul_check (eval161 hA hB) (eval43 hA hB) p201

theorem eval163 : toMatrix (w163 (a hA) (b hB)) = decodeRows r163 := by
  unfold w163
  exact mul_check (eval162 hA hB) (eval43 hA hB) p202

theorem eval164 : toMatrix (w164 (a hA) (b hB)) = decodeRows r164 := by
  unfold w164
  exact mul_check (eval163 hA hB) (eval0 hA hB) p203

theorem eval165 : toMatrix (w165 (a hA) (b hB)) = decodeRows r165 := by
  unfold w165
  exact mul_check (eval164 hA hB) (eval43 hA hB) p204

theorem eval166 : toMatrix (w166 (a hA) (b hB)) = decodeRows r166 := by
  unfold w166
  exact inv_check (eval165 hA hB) p205

theorem eval167 : toMatrix (w167 (a hA) (b hB)) = decodeRows r167 := by
  unfold w167
  exact mul_check (eval166 hA hB) (eval20 hA hB) p206

theorem eval168 : toMatrix (w168 (a hA) (b hB)) = decodeRows r168 := by
  unfold w168
  exact mul_check (eval167 hA hB) (eval165 hA hB) p207

theorem eval169 : toMatrix (w169 (a hA) (b hB)) = decodeRows r169 := by
  unfold w169
  exact mul_check (eval20 hA hB) (eval168 hA hB) p208

theorem eval170 : toMatrix (w170 (a hA) (b hB)) = decodeRows r170 := by
  unfold w170
  have h1 : toMatrix ((w169 (a hA) (b hB)) ^ 1) = decodeRows r169 := by
    simpa only [pow_one] using (eval169 hA hB)
  have h2 : toMatrix ((w169 (a hA) (b hB)) ^ 2) = decodeRows q170_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p209
  have h3 : toMatrix ((w169 (a hA) (b hB)) ^ 3) = decodeRows q170_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p210
  have h6 : toMatrix ((w169 (a hA) (b hB)) ^ 6) = decodeRows r170 := by
    simpa only [← pow_add] using mul_check h3 h3 p211
  exact h6

theorem eval171 : toMatrix (w171 (a hA) (b hB)) = decodeRows r171 := by
  unfold w171
  exact mul_check (eval45 hA hB) (eval43 hA hB) p212

theorem eval172 : toMatrix (w172 (a hA) (b hB)) = decodeRows r172 := by
  unfold w172
  exact mul_check (eval50 hA hB) (eval1 hA hB) p213

theorem eval173 : toMatrix (w173 (a hA) (b hB)) = decodeRows r173 := by
  unfold w173
  exact mul_check (eval172 hA hB) (eval55 hA hB) p214

theorem eval174 : toMatrix (w174 (a hA) (b hB)) = decodeRows r174 := by
  unfold w174
  exact mul_check (eval173 hA hB) (eval43 hA hB) p215

theorem eval175 : toMatrix (w175 (a hA) (b hB)) = decodeRows r175 := by
  unfold w175
  exact mul_check (eval174 hA hB) (eval0 hA hB) p216

theorem eval176 : toMatrix (w176 (a hA) (b hB)) = decodeRows r176 := by
  unfold w176
  exact mul_check (eval175 hA hB) (eval2 hA hB) p217

theorem eval177 : toMatrix (w177 (a hA) (b hB)) = decodeRows r177 := by
  unfold w177
  exact mul_check (eval176 hA hB) (eval2 hA hB) p218

theorem eval178 : toMatrix (w178 (a hA) (b hB)) = decodeRows r178 := by
  unfold w178
  exact inv_check (eval177 hA hB) p219

theorem eval179 : toMatrix (w179 (a hA) (b hB)) = decodeRows r179 := by
  unfold w179
  exact mul_check (eval178 hA hB) (eval20 hA hB) p220

theorem eval180 : toMatrix (w180 (a hA) (b hB)) = decodeRows r180 := by
  unfold w180
  exact mul_check (eval179 hA hB) (eval177 hA hB) p221

theorem eval181 : toMatrix (w181 (a hA) (b hB)) = decodeRows r181 := by
  unfold w181
  exact mul_check (eval20 hA hB) (eval180 hA hB) p222

theorem eval182 : toMatrix (w182 (a hA) (b hB)) = decodeRows r182 := by
  unfold w182
  have h1 : toMatrix ((w181 (a hA) (b hB)) ^ 1) = decodeRows r181 := by
    simpa only [pow_one] using (eval181 hA hB)
  have h2 : toMatrix ((w181 (a hA) (b hB)) ^ 2) = decodeRows q182_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p223
  have h3 : toMatrix ((w181 (a hA) (b hB)) ^ 3) = decodeRows q182_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p224
  have h5 : toMatrix ((w181 (a hA) (b hB)) ^ 5) = decodeRows r182 := by
    simpa only [← pow_add] using mul_check h2 h3 p225
  exact h5

theorem eval183 : toMatrix (w183 (a hA) (b hB)) = decodeRows r183 := by
  unfold w183
  exact mul_check (eval177 hA hB) (eval182 hA hB) p226

theorem eval184 : toMatrix (w184 (a hA) (b hB)) = decodeRows r184 := by
  unfold w184
  exact mul_check (eval171 hA hB) (eval43 hA hB) p227

theorem eval185 : toMatrix (w185 (a hA) (b hB)) = decodeRows r185 := by
  unfold w185
  exact mul_check (eval184 hA hB) (eval0 hA hB) p228

theorem eval186 : toMatrix (w186 (a hA) (b hB)) = decodeRows r186 := by
  unfold w186
  exact mul_check (eval185 hA hB) (eval1 hA hB) p229

theorem eval187 : toMatrix (w187 (a hA) (b hB)) = decodeRows r187 := by
  unfold w187
  exact mul_check (eval186 hA hB) (eval0 hA hB) p230

theorem eval188 : toMatrix (w188 (a hA) (b hB)) = decodeRows r188 := by
  unfold w188
  exact mul_check (eval187 hA hB) (eval2 hA hB) p231

theorem eval189 : toMatrix (w189 (a hA) (b hB)) = decodeRows r189 := by
  unfold w189
  exact mul_check (eval188 hA hB) (eval55 hA hB) p232

theorem eval190 : toMatrix (w190 (a hA) (b hB)) = decodeRows r190 := by
  unfold w190
  exact mul_check (eval189 hA hB) (eval43 hA hB) p233

theorem eval191 : toMatrix (w191 (a hA) (b hB)) = decodeRows r191 := by
  unfold w191
  exact mul_check (eval190 hA hB) (eval55 hA hB) p234

theorem eval192 : toMatrix (w192 (a hA) (b hB)) = decodeRows r192 := by
  unfold w192
  exact mul_check (eval191 hA hB) (eval2 hA hB) p235

theorem eval193 : toMatrix (w193 (a hA) (b hB)) = decodeRows r193 := by
  unfold w193
  exact mul_check (eval192 hA hB) (eval2 hA hB) p236

theorem eval194 : toMatrix (w194 (a hA) (b hB)) = decodeRows r194 := by
  unfold w194
  exact mul_check (eval193 hA hB) (eval2 hA hB) p237

theorem eval195 : toMatrix (w195 (a hA) (b hB)) = decodeRows r195 := by
  unfold w195
  exact mul_check (eval194 hA hB) (eval0 hA hB) p238

theorem eval196 : toMatrix (w196 (a hA) (b hB)) = decodeRows r196 := by
  unfold w196
  exact inv_check (eval195 hA hB) p239

theorem eval197 : toMatrix (w197 (a hA) (b hB)) = decodeRows r197 := by
  unfold w197
  exact mul_check (eval196 hA hB) (eval20 hA hB) p240

theorem eval198 : toMatrix (w198 (a hA) (b hB)) = decodeRows r198 := by
  unfold w198
  exact mul_check (eval197 hA hB) (eval195 hA hB) p241

theorem eval199 : toMatrix (w199 (a hA) (b hB)) = decodeRows r199 := by
  unfold w199
  exact mul_check (eval20 hA hB) (eval198 hA hB) p242

theorem eval200 : toMatrix (w200 (a hA) (b hB)) = decodeRows r200 := by
  unfold w200
  have h1 : toMatrix ((w199 (a hA) (b hB)) ^ 1) = decodeRows r199 := by
    simpa only [pow_one] using (eval199 hA hB)
  have h2 : toMatrix ((w199 (a hA) (b hB)) ^ 2) = decodeRows q200_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p243
  have h3 : toMatrix ((w199 (a hA) (b hB)) ^ 3) = decodeRows q200_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p244
  have h6 : toMatrix ((w199 (a hA) (b hB)) ^ 6) = decodeRows r200 := by
    simpa only [← pow_add] using mul_check h3 h3 p245
  exact h6

theorem eval201 : toMatrix (w201 (a hA) (b hB)) = decodeRows r201 := by
  unfold w201
  exact mul_check (eval56 hA hB) (eval1 hA hB) p246

theorem eval202 : toMatrix (w202 (a hA) (b hB)) = decodeRows r202 := by
  unfold w202
  exact mul_check (eval201 hA hB) (eval55 hA hB) p247

theorem eval203 : toMatrix (w203 (a hA) (b hB)) = decodeRows r203 := by
  unfold w203
  exact mul_check (eval202 hA hB) (eval0 hA hB) p248

theorem eval204 : toMatrix (w204 (a hA) (b hB)) = decodeRows r204 := by
  unfold w204
  exact mul_check (eval203 hA hB) (eval1 hA hB) p249

theorem eval205 : toMatrix (w205 (a hA) (b hB)) = decodeRows r205 := by
  unfold w205
  exact mul_check (eval204 hA hB) (eval1 hA hB) p250

theorem eval206 : toMatrix (w206 (a hA) (b hB)) = decodeRows r206 := by
  unfold w206
  exact mul_check (eval205 hA hB) (eval43 hA hB) p251

theorem eval207 : toMatrix (w207 (a hA) (b hB)) = decodeRows r207 := by
  unfold w207
  exact mul_check (eval206 hA hB) (eval2 hA hB) p252

theorem eval208 : toMatrix (w208 (a hA) (b hB)) = decodeRows r208 := by
  unfold w208
  exact mul_check (eval207 hA hB) (eval43 hA hB) p253

theorem eval209 : toMatrix (w209 (a hA) (b hB)) = decodeRows r209 := by
  unfold w209
  exact inv_check (eval208 hA hB) p254

theorem eval210 : toMatrix (w210 (a hA) (b hB)) = decodeRows r210 := by
  unfold w210
  exact mul_check (eval209 hA hB) (eval20 hA hB) p255

theorem eval211 : toMatrix (w211 (a hA) (b hB)) = decodeRows r211 := by
  unfold w211
  exact mul_check (eval210 hA hB) (eval208 hA hB) p256

theorem eval212 : toMatrix (w212 (a hA) (b hB)) = decodeRows r212 := by
  unfold w212
  exact mul_check (eval20 hA hB) (eval211 hA hB) p257

theorem eval213 : toMatrix (w213 (a hA) (b hB)) = decodeRows r213 := by
  unfold w213
  have h1 : toMatrix ((w212 (a hA) (b hB)) ^ 1) = decodeRows r212 := by
    simpa only [pow_one] using (eval212 hA hB)
  have h2 : toMatrix ((w212 (a hA) (b hB)) ^ 2) = decodeRows q213_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p258
  have h3 : toMatrix ((w212 (a hA) (b hB)) ^ 3) = decodeRows q213_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p259
  have h6 : toMatrix ((w212 (a hA) (b hB)) ^ 6) = decodeRows r213 := by
    simpa only [← pow_add] using mul_check h3 h3 p260
  exact h6

theorem eval214 : toMatrix (w214 (a hA) (b hB)) = decodeRows r214 := by
  unfold w214
  exact mul_check (eval142 hA hB) (eval55 hA hB) p261

theorem eval215 : toMatrix (w215 (a hA) (b hB)) = decodeRows r215 := by
  unfold w215
  exact mul_check (eval214 hA hB) (eval55 hA hB) p262

theorem eval216 : toMatrix (w216 (a hA) (b hB)) = decodeRows r216 := by
  unfold w216
  exact mul_check (eval215 hA hB) (eval1 hA hB) p263

theorem eval217 : toMatrix (w217 (a hA) (b hB)) = decodeRows r217 := by
  unfold w217
  exact mul_check (eval216 hA hB) (eval43 hA hB) p264

theorem eval218 : toMatrix (w218 (a hA) (b hB)) = decodeRows r218 := by
  unfold w218
  exact mul_check (eval217 hA hB) (eval43 hA hB) p265

theorem eval219 : toMatrix (w219 (a hA) (b hB)) = decodeRows r219 := by
  unfold w219
  exact mul_check (eval218 hA hB) (eval43 hA hB) p266

theorem eval220 : toMatrix (w220 (a hA) (b hB)) = decodeRows r220 := by
  unfold w220
  exact mul_check (eval219 hA hB) (eval1 hA hB) p267

theorem eval221 : toMatrix (w221 (a hA) (b hB)) = decodeRows r221 := by
  unfold w221
  exact mul_check (eval220 hA hB) (eval55 hA hB) p268

theorem eval222 : toMatrix (w222 (a hA) (b hB)) = decodeRows r222 := by
  unfold w222
  exact inv_check (eval221 hA hB) p269

theorem eval223 : toMatrix (w223 (a hA) (b hB)) = decodeRows r223 := by
  unfold w223
  exact mul_check (eval222 hA hB) (eval20 hA hB) p270

theorem eval224 : toMatrix (w224 (a hA) (b hB)) = decodeRows r224 := by
  unfold w224
  exact mul_check (eval223 hA hB) (eval221 hA hB) p271

theorem eval225 : toMatrix (w225 (a hA) (b hB)) = decodeRows r225 := by
  unfold w225
  exact mul_check (eval20 hA hB) (eval224 hA hB) p272

theorem eval226 : toMatrix (w226 (a hA) (b hB)) = decodeRows r226 := by
  unfold w226
  have h1 : toMatrix ((w225 (a hA) (b hB)) ^ 1) = decodeRows r225 := by
    simpa only [pow_one] using (eval225 hA hB)
  have h2 : toMatrix ((w225 (a hA) (b hB)) ^ 2) = decodeRows q226_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p273
  have h3 : toMatrix ((w225 (a hA) (b hB)) ^ 3) = decodeRows q226_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p274
  have h6 : toMatrix ((w225 (a hA) (b hB)) ^ 6) = decodeRows r226 := by
    simpa only [← pow_add] using mul_check h3 h3 p275
  exact h6

theorem eval227 : toMatrix (w227 (a hA) (b hB)) = decodeRows r227 := by
  unfold w227
  exact mul_check (eval92 hA hB) (eval55 hA hB) p276

theorem eval228 : toMatrix (w228 (a hA) (b hB)) = decodeRows r228 := by
  unfold w228
  exact mul_check (eval227 hA hB) (eval2 hA hB) p277

theorem eval229 : toMatrix (w229 (a hA) (b hB)) = decodeRows r229 := by
  unfold w229
  exact mul_check (eval228 hA hB) (eval43 hA hB) p278

theorem eval230 : toMatrix (w230 (a hA) (b hB)) = decodeRows r230 := by
  unfold w230
  exact mul_check (eval229 hA hB) (eval43 hA hB) p279

theorem eval231 : toMatrix (w231 (a hA) (b hB)) = decodeRows r231 := by
  unfold w231
  exact mul_check (eval230 hA hB) (eval2 hA hB) p280

theorem eval232 : toMatrix (w232 (a hA) (b hB)) = decodeRows r232 := by
  unfold w232
  exact mul_check (eval231 hA hB) (eval2 hA hB) p281

theorem eval233 : toMatrix (w233 (a hA) (b hB)) = decodeRows r233 := by
  unfold w233
  exact mul_check (eval232 hA hB) (eval55 hA hB) p282

theorem eval234 : toMatrix (w234 (a hA) (b hB)) = decodeRows r234 := by
  unfold w234
  exact mul_check (eval233 hA hB) (eval55 hA hB) p283

theorem eval235 : toMatrix (w235 (a hA) (b hB)) = decodeRows r235 := by
  unfold w235
  exact mul_check (eval234 hA hB) (eval55 hA hB) p284

theorem eval236 : toMatrix (w236 (a hA) (b hB)) = decodeRows r236 := by
  unfold w236
  exact inv_check (eval235 hA hB) p285

theorem eval237 : toMatrix (w237 (a hA) (b hB)) = decodeRows r237 := by
  unfold w237
  exact mul_check (eval236 hA hB) (eval20 hA hB) p286

theorem eval238 : toMatrix (w238 (a hA) (b hB)) = decodeRows r238 := by
  unfold w238
  exact mul_check (eval237 hA hB) (eval235 hA hB) p287

theorem eval239 : toMatrix (w239 (a hA) (b hB)) = decodeRows r239 := by
  unfold w239
  exact mul_check (eval20 hA hB) (eval238 hA hB) p288

theorem eval240 : toMatrix (w240 (a hA) (b hB)) = decodeRows r240 := by
  unfold w240
  have h1 : toMatrix ((w239 (a hA) (b hB)) ^ 1) = decodeRows r239 := by
    simpa only [pow_one] using (eval239 hA hB)
  have h2 : toMatrix ((w239 (a hA) (b hB)) ^ 2) = decodeRows q240_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p289
  have h4 : toMatrix ((w239 (a hA) (b hB)) ^ 4) = decodeRows r240 := by
    simpa only [← pow_add] using mul_check h2 h2 p290
  exact h4

theorem eval241 : toMatrix (w241 (a hA) (b hB)) = decodeRows r241 := by
  unfold w241
  exact mul_check (eval1 hA hB) (eval43 hA hB) p291

theorem eval242 : toMatrix (w242 (a hA) (b hB)) = decodeRows r242 := by
  unfold w242
  exact mul_check (eval241 hA hB) (eval2 hA hB) p292

theorem eval243 : toMatrix (w243 (a hA) (b hB)) = decodeRows r243 := by
  unfold w243
  exact mul_check (eval242 hA hB) (eval43 hA hB) p293

theorem eval244 : toMatrix (w244 (a hA) (b hB)) = decodeRows r244 := by
  unfold w244
  exact mul_check (eval243 hA hB) (eval0 hA hB) p294

theorem eval245 : toMatrix (w245 (a hA) (b hB)) = decodeRows r245 := by
  unfold w245
  exact mul_check (eval244 hA hB) (eval2 hA hB) p295

theorem eval246 : toMatrix (w246 (a hA) (b hB)) = decodeRows r246 := by
  unfold w246
  exact mul_check (eval245 hA hB) (eval2 hA hB) p296

theorem eval247 : toMatrix (w247 (a hA) (b hB)) = decodeRows r247 := by
  unfold w247
  exact mul_check (eval246 hA hB) (eval0 hA hB) p297

theorem eval248 : toMatrix (w248 (a hA) (b hB)) = decodeRows r248 := by
  unfold w248
  exact mul_check (eval247 hA hB) (eval55 hA hB) p298

theorem eval249 : toMatrix (w249 (a hA) (b hB)) = decodeRows r249 := by
  unfold w249
  exact inv_check (eval248 hA hB) p299

theorem eval250 : toMatrix (w250 (a hA) (b hB)) = decodeRows r250 := by
  unfold w250
  exact mul_check (eval249 hA hB) (eval20 hA hB) p300

theorem eval251 : toMatrix (w251 (a hA) (b hB)) = decodeRows r251 := by
  unfold w251
  exact mul_check (eval250 hA hB) (eval248 hA hB) p301

theorem eval252 : toMatrix (w252 (a hA) (b hB)) = decodeRows r252 := by
  unfold w252
  exact mul_check (eval20 hA hB) (eval251 hA hB) p302

theorem eval253 : toMatrix (w253 (a hA) (b hB)) = decodeRows r253 := by
  unfold w253
  have h1 : toMatrix ((w252 (a hA) (b hB)) ^ 1) = decodeRows r252 := by
    simpa only [pow_one] using (eval252 hA hB)
  have h2 : toMatrix ((w252 (a hA) (b hB)) ^ 2) = decodeRows q253_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p303
  have h3 : toMatrix ((w252 (a hA) (b hB)) ^ 3) = decodeRows q253_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p304
  have h5 : toMatrix ((w252 (a hA) (b hB)) ^ 5) = decodeRows r253 := by
    simpa only [← pow_add] using mul_check h2 h3 p305
  exact h5

theorem eval254 : toMatrix (w254 (a hA) (b hB)) = decodeRows r254 := by
  unfold w254
  exact mul_check (eval45 hA hB) (eval55 hA hB) p306

theorem eval255 : toMatrix (w255 (a hA) (b hB)) = decodeRows r255 := by
  unfold w255
  exact mul_check (eval171 hA hB) (eval55 hA hB) p307

theorem eval256 : toMatrix (w256 (a hA) (b hB)) = decodeRows r256 := by
  unfold w256
  exact mul_check (eval255 hA hB) (eval43 hA hB) p308

theorem eval257 : toMatrix (w257 (a hA) (b hB)) = decodeRows r257 := by
  unfold w257
  exact mul_check (eval256 hA hB) (eval1 hA hB) p309

theorem eval258 : toMatrix (w258 (a hA) (b hB)) = decodeRows r258 := by
  unfold w258
  exact mul_check (eval257 hA hB) (eval2 hA hB) p310

theorem eval259 : toMatrix (w259 (a hA) (b hB)) = decodeRows r259 := by
  unfold w259
  exact mul_check (eval258 hA hB) (eval2 hA hB) p311

theorem eval260 : toMatrix (w260 (a hA) (b hB)) = decodeRows r260 := by
  unfold w260
  exact mul_check (eval259 hA hB) (eval43 hA hB) p312

theorem eval261 : toMatrix (w261 (a hA) (b hB)) = decodeRows r261 := by
  unfold w261
  exact mul_check (eval260 hA hB) (eval55 hA hB) p313

theorem eval262 : toMatrix (w262 (a hA) (b hB)) = decodeRows r262 := by
  unfold w262
  exact mul_check (eval261 hA hB) (eval2 hA hB) p314

theorem eval263 : toMatrix (w263 (a hA) (b hB)) = decodeRows r263 := by
  unfold w263
  exact mul_check (eval262 hA hB) (eval2 hA hB) p315

theorem eval264 : toMatrix (w264 (a hA) (b hB)) = decodeRows r264 := by
  unfold w264
  exact inv_check (eval263 hA hB) p316

theorem eval265 : toMatrix (w265 (a hA) (b hB)) = decodeRows r265 := by
  unfold w265
  exact mul_check (eval264 hA hB) (eval20 hA hB) p317

theorem eval266 : toMatrix (w266 (a hA) (b hB)) = decodeRows r266 := by
  unfold w266
  exact mul_check (eval265 hA hB) (eval263 hA hB) p318

theorem eval267 : toMatrix (w267 (a hA) (b hB)) = decodeRows r267 := by
  unfold w267
  exact mul_check (eval20 hA hB) (eval266 hA hB) p319

theorem eval268 : toMatrix (w268 (a hA) (b hB)) = decodeRows r268 := by
  unfold w268
  have h1 : toMatrix ((w267 (a hA) (b hB)) ^ 1) = decodeRows r267 := by
    simpa only [pow_one] using (eval267 hA hB)
  have h2 : toMatrix ((w267 (a hA) (b hB)) ^ 2) = decodeRows q268_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p320
  have h3 : toMatrix ((w267 (a hA) (b hB)) ^ 3) = decodeRows q268_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p321
  have h5 : toMatrix ((w267 (a hA) (b hB)) ^ 5) = decodeRows r268 := by
    simpa only [← pow_add] using mul_check h2 h3 p322
  exact h5

theorem eval269 : toMatrix (w269 (a hA) (b hB)) = decodeRows r269 := by
  unfold w269
  exact mul_check (eval263 hA hB) (eval268 hA hB) p323

theorem eval270 : toMatrix (w270 (a hA) (b hB)) = decodeRows r270 := by
  unfold w270
  exact mul_check (eval140 hA hB) (eval2 hA hB) p324

theorem eval271 : toMatrix (w271 (a hA) (b hB)) = decodeRows r271 := by
  unfold w271
  exact mul_check (eval270 hA hB) (eval1 hA hB) p325

theorem eval272 : toMatrix (w272 (a hA) (b hB)) = decodeRows r272 := by
  unfold w272
  exact mul_check (eval271 hA hB) (eval2 hA hB) p326

theorem eval273 : toMatrix (w273 (a hA) (b hB)) = decodeRows r273 := by
  unfold w273
  exact mul_check (eval272 hA hB) (eval55 hA hB) p327

theorem eval274 : toMatrix (w274 (a hA) (b hB)) = decodeRows r274 := by
  unfold w274
  exact mul_check (eval273 hA hB) (eval43 hA hB) p328

theorem eval275 : toMatrix (w275 (a hA) (b hB)) = decodeRows r275 := by
  unfold w275
  exact mul_check (eval274 hA hB) (eval1 hA hB) p329

theorem eval276 : toMatrix (w276 (a hA) (b hB)) = decodeRows r276 := by
  unfold w276
  exact mul_check (eval275 hA hB) (eval55 hA hB) p330

theorem eval277 : toMatrix (w277 (a hA) (b hB)) = decodeRows r277 := by
  unfold w277
  exact mul_check (eval276 hA hB) (eval0 hA hB) p331

theorem eval278 : toMatrix (w278 (a hA) (b hB)) = decodeRows r278 := by
  unfold w278
  exact mul_check (eval277 hA hB) (eval55 hA hB) p332

theorem eval279 : toMatrix (w279 (a hA) (b hB)) = decodeRows r279 := by
  unfold w279
  exact inv_check (eval278 hA hB) p333

theorem eval280 : toMatrix (w280 (a hA) (b hB)) = decodeRows r280 := by
  unfold w280
  exact mul_check (eval279 hA hB) (eval20 hA hB) p334

theorem eval281 : toMatrix (w281 (a hA) (b hB)) = decodeRows r281 := by
  unfold w281
  exact mul_check (eval280 hA hB) (eval278 hA hB) p335

theorem eval282 : toMatrix (w282 (a hA) (b hB)) = decodeRows r282 := by
  unfold w282
  exact mul_check (eval20 hA hB) (eval281 hA hB) p336

theorem eval283 : toMatrix (w283 (a hA) (b hB)) = decodeRows r283 := by
  unfold w283
  have h1 : toMatrix ((w282 (a hA) (b hB)) ^ 1) = decodeRows r282 := by
    simpa only [pow_one] using (eval282 hA hB)
  have h2 : toMatrix ((w282 (a hA) (b hB)) ^ 2) = decodeRows q283_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p337
  have h3 : toMatrix ((w282 (a hA) (b hB)) ^ 3) = decodeRows r283 := by
    simpa only [← pow_add] using mul_check h1 h2 p338
  exact h3

theorem eval284 : toMatrix (w284 (a hA) (b hB)) = decodeRows r284 := by
  unfold w284
  exact mul_check (eval50 hA hB) (eval55 hA hB) p339

theorem eval285 : toMatrix (w285 (a hA) (b hB)) = decodeRows r285 := by
  unfold w285
  exact mul_check (eval284 hA hB) (eval55 hA hB) p340

theorem eval286 : toMatrix (w286 (a hA) (b hB)) = decodeRows r286 := by
  unfold w286
  exact mul_check (eval285 hA hB) (eval43 hA hB) p341

theorem eval287 : toMatrix (w287 (a hA) (b hB)) = decodeRows r287 := by
  unfold w287
  exact inv_check (eval286 hA hB) p342

theorem eval288 : toMatrix (w288 (a hA) (b hB)) = decodeRows r288 := by
  unfold w288
  exact mul_check (eval287 hA hB) (eval20 hA hB) p343

theorem eval289 : toMatrix (w289 (a hA) (b hB)) = decodeRows r289 := by
  unfold w289
  exact mul_check (eval288 hA hB) (eval286 hA hB) p344

theorem eval290 : toMatrix (w290 (a hA) (b hB)) = decodeRows r290 := by
  unfold w290
  exact mul_check (eval20 hA hB) (eval289 hA hB) p345

theorem eval291 : toMatrix (w291 (a hA) (b hB)) = decodeRows r291 := by
  unfold w291
  have h1 : toMatrix ((w290 (a hA) (b hB)) ^ 1) = decodeRows r290 := by
    simpa only [pow_one] using (eval290 hA hB)
  have h2 : toMatrix ((w290 (a hA) (b hB)) ^ 2) = decodeRows r291 := by
    simpa only [← pow_add] using mul_check h1 h1 p346
  exact h2

theorem eval292 : toMatrix (w292 (a hA) (b hB)) = decodeRows r292 := by
  unfold w292
  exact mul_check (eval291 hA hB) (eval123 hA hB) p347

theorem eval293 : toMatrix (w293 (a hA) (b hB)) = decodeRows r293 := by
  unfold w293
  exact mul_check (eval292 hA hB) (eval291 hA hB) p348

theorem eval294 : toMatrix (w294 (a hA) (b hB)) = decodeRows r294 := by
  unfold w294
  exact mul_check (eval293 hA hB) (eval123 hA hB) p349

theorem eval295 : toMatrix (w295 (a hA) (b hB)) = decodeRows r295 := by
  unfold w295
  exact mul_check (eval291 hA hB) (eval91 hA hB) p350

theorem eval296 : toMatrix (w296 (a hA) (b hB)) = decodeRows r296 := by
  unfold w296
  exact mul_check (eval294 hA hB) (eval253 hA hB) p351

theorem eval297 : toMatrix (w297 (a hA) (b hB)) = decodeRows r297 := by
  unfold w297
  exact mul_check (eval295 hA hB) (eval269 hA hB) p352

theorem eval298 : toMatrix (w298 (a hA) (b hB)) = decodeRows r298 := by
  unfold w298
  exact mul_check (eval297 hA hB) (eval291 hA hB) p353

theorem eval299 : toMatrix (w299 (a hA) (b hB)) = decodeRows r299 := by
  unfold w299
  exact mul_check (eval298 hA hB) (eval159 hA hB) p354

theorem eval300 : toMatrix (w300 (a hA) (b hB)) = decodeRows r300 := by
  unfold w300
  exact mul_check (eval299 hA hB) (eval200 hA hB) p355

theorem eval301 : toMatrix (w301 (a hA) (b hB)) = decodeRows r301 := by
  unfold w301
  exact mul_check (eval300 hA hB) (eval283 hA hB) p356

theorem eval302 : toMatrix (w302 (a hA) (b hB)) = decodeRows r302 := by
  unfold w302
  exact mul_check (eval296 hA hB) (eval72 hA hB) p357

theorem eval303 : toMatrix (w303 (a hA) (b hB)) = decodeRows r303 := by
  unfold w303
  exact mul_check (eval301 hA hB) (eval213 hA hB) p358

theorem eval304 : toMatrix (w304 (a hA) (b hB)) = decodeRows r304 := by
  unfold w304
  exact mul_check (eval302 hA hB) (eval123 hA hB) p359

theorem eval305 : toMatrix (w305 (a hA) (b hB)) = decodeRows r305 := by
  unfold w305
  exact mul_check (eval293 hA hB) (eval139 hA hB) p360

theorem eval306 : toMatrix (w306 (a hA) (b hB)) = decodeRows r306 := by
  unfold w306
  exact inv_check (eval303 hA hB) p361

theorem eval307 : toMatrix (w307 (a hA) (b hB)) = decodeRows r307 := by
  unfold w307
  exact mul_check (eval303 hA hB) (eval226 hA hB) p362

theorem eval308 : toMatrix (w308 (a hA) (b hB)) = decodeRows r308 := by
  unfold w308
  exact mul_check (eval307 hA hB) (eval306 hA hB) p363

theorem eval309 : toMatrix (w309 (a hA) (b hB)) = decodeRows r309 := by
  unfold w309
  exact mul_check (eval304 hA hB) (eval183 hA hB) p364

theorem eval310 : toMatrix (w310 (a hA) (b hB)) = decodeRows r310 := by
  unfold w310
  exact mul_check (eval309 hA hB) (eval283 hA hB) p365

theorem eval311 : toMatrix (w311 (a hA) (b hB)) = decodeRows r311 := by
  unfold w311
  exact inv_check (eval305 hA hB) p366

theorem eval312 : toMatrix (w312 (a hA) (b hB)) = decodeRows r312 := by
  unfold w312
  exact mul_check (eval310 hA hB) (eval311 hA hB) p367

theorem eval313 : toMatrix (w313 (a hA) (b hB)) = decodeRows r313 := by
  unfold w313
  exact mul_check (eval308 hA hB) (eval312 hA hB) p368

theorem eval314 : toMatrix (w314 (a hA) (b hB)) = decodeRows r314 := by
  unfold w314
  have h1 : toMatrix ((w313 (a hA) (b hB)) ^ 1) = decodeRows r313 := by
    simpa only [pow_one] using (eval313 hA hB)
  have h2 : toMatrix ((w313 (a hA) (b hB)) ^ 2) = decodeRows q314_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p369
  have h3 : toMatrix ((w313 (a hA) (b hB)) ^ 3) = decodeRows q314_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p370
  have h4 : toMatrix ((w313 (a hA) (b hB)) ^ 4) = decodeRows q314_4 := by
    simpa only [← pow_add] using mul_check h2 h2 p371
  have h7 : toMatrix ((w313 (a hA) (b hB)) ^ 7) = decodeRows r314 := by
    simpa only [← pow_add] using mul_check h3 h4 p372
  exact h7

theorem eval315 : toMatrix (w315 (a hA) (b hB)) = decodeRows r315 := by
  unfold w315
  exact mul_check (eval170 hA hB) (eval253 hA hB) p373

theorem eval316 : toMatrix (w316 (a hA) (b hB)) = decodeRows r316 := by
  unfold w316
  exact mul_check (eval315 hA hB) (eval183 hA hB) p374

theorem eval317 : toMatrix (w317 (a hA) (b hB)) = decodeRows r317 := by
  unfold w317
  exact mul_check (eval123 hA hB) (eval213 hA hB) p375

theorem eval318 : toMatrix (w318 (a hA) (b hB)) = decodeRows r318 := by
  unfold w318
  exact mul_check (eval317 hA hB) (eval170 hA hB) p376

theorem eval319 : toMatrix (w319 (a hA) (b hB)) = decodeRows r319 := by
  unfold w319
  exact mul_check (eval318 hA hB) (eval269 hA hB) p377

theorem eval320 : toMatrix (w320 (a hA) (b hB)) = decodeRows r320 := by
  unfold w320
  exact mul_check (eval319 hA hB) (eval123 hA hB) p378

theorem eval321 : toMatrix (w321 (a hA) (b hB)) = decodeRows r321 := by
  unfold w321
  exact mul_check (eval320 hA hB) (eval240 hA hB) p379

theorem eval322 : toMatrix (w322 (a hA) (b hB)) = decodeRows r322 := by
  unfold w322
  exact mul_check (eval321 hA hB) (eval139 hA hB) p380

theorem eval323 : toMatrix (w323 (a hA) (b hB)) = decodeRows r323 := by
  unfold w323
  exact mul_check (eval322 hA hB) (eval170 hA hB) p381

theorem eval324 : toMatrix (w324 (a hA) (b hB)) = decodeRows r324 := by
  unfold w324
  exact mul_check (eval316 hA hB) (eval139 hA hB) p382

theorem eval325 : toMatrix (w325 (a hA) (b hB)) = decodeRows r325 := by
  unfold w325
  exact mul_check (eval324 hA hB) (eval200 hA hB) p383

theorem eval326 : toMatrix (w326 (a hA) (b hB)) = decodeRows r326 := by
  unfold w326
  exact mul_check (eval323 hA hB) (eval269 hA hB) p384

theorem eval327 : toMatrix (w327 (a hA) (b hB)) = decodeRows r327 := by
  unfold w327
  exact mul_check (eval326 hA hB) (eval72 hA hB) p385

theorem eval328 : toMatrix (w328 (a hA) (b hB)) = decodeRows r328 := by
  unfold w328
  exact mul_check (eval327 hA hB) (eval105 hA hB) p386

theorem eval329 : toMatrix (w329 (a hA) (b hB)) = decodeRows r329 := by
  unfold w329
  exact mul_check (eval328 hA hB) (eval159 hA hB) p387

theorem eval330 : toMatrix (w330 (a hA) (b hB)) = decodeRows r330 := by
  unfold w330
  exact mul_check (eval325 hA hB) (eval226 hA hB) p388

theorem eval331 : toMatrix (w331 (a hA) (b hB)) = decodeRows r331 := by
  unfold w331
  exact mul_check (eval330 hA hB) (eval213 hA hB) p389

theorem eval332 : toMatrix (w332 (a hA) (b hB)) = decodeRows r332 := by
  unfold w332
  exact mul_check (eval331 hA hB) (eval253 hA hB) p390

theorem eval333 : toMatrix (w333 (a hA) (b hB)) = decodeRows r333 := by
  unfold w333
  exact mul_check (eval332 hA hB) (eval200 hA hB) p391

theorem eval334 : toMatrix (w334 (a hA) (b hB)) = decodeRows r334 := by
  unfold w334
  exact mul_check (eval329 hA hB) (eval226 hA hB) p392

theorem eval335 : toMatrix (w335 (a hA) (b hB)) = decodeRows r335 := by
  unfold w335
  exact inv_check (eval333 hA hB) p393

theorem eval336 : toMatrix (w336 (a hA) (b hB)) = decodeRows r336 := by
  unfold w336
  exact mul_check (eval334 hA hB) (eval335 hA hB) p394

theorem eval337 : toMatrix (w337 (a hA) (b hB)) = decodeRows r337 := by
  unfold w337
  exact mul_check (eval23 hA hB) (eval20 hA hB) p395

theorem eval338 : toMatrix (w338 (a hA) (b hB)) = decodeRows r338 := by
  unfold w338
  exact mul_check (eval337 hA hB) (eval13 hA hB) p396

theorem eval339 : toMatrix (w339 (a hA) (b hB)) = decodeRows r339 := by
  unfold w339
  exact mul_check (eval338 hA hB) (eval13 hA hB) p397

theorem eval340 : toMatrix (w340 (a hA) (b hB)) = decodeRows r340 := by
  unfold w340
  exact mul_check (eval339 hA hB) (eval20 hA hB) p398

theorem eval341 : toMatrix (w341 (a hA) (b hB)) = decodeRows r341 := by
  unfold w341
  exact mul_check (eval340 hA hB) (eval13 hA hB) p399

theorem eval342 : toMatrix (w342 (a hA) (b hB)) = decodeRows r342 := by
  unfold w342
  exact mul_check (eval341 hA hB) (eval13 hA hB) p400

theorem eval343 : toMatrix (w343 (a hA) (b hB)) = decodeRows r343 := by
  unfold w343
  exact mul_check (eval342 hA hB) (eval20 hA hB) p401

theorem eval344 : toMatrix (w344 (a hA) (b hB)) = decodeRows r344 := by
  unfold w344
  exact mul_check (eval343 hA hB) (eval13 hA hB) p402

theorem eval345 : toMatrix (w345 (a hA) (b hB)) = decodeRows r345 := by
  unfold w345
  exact mul_check (eval344 hA hB) (eval13 hA hB) p403

theorem eval346 : toMatrix (w346 (a hA) (b hB)) = decodeRows r346 := by
  unfold w346
  exact mul_check (eval345 hA hB) (eval13 hA hB) p404

theorem eval347 : toMatrix (w347 (a hA) (b hB)) = decodeRows r347 := by
  unfold w347
  exact mul_check (eval346 hA hB) (eval13 hA hB) p405

theorem eval348 : toMatrix (w348 (a hA) (b hB)) = decodeRows r348 := by
  unfold w348
  exact mul_check (eval347 hA hB) (eval13 hA hB) p406

theorem eval349 : toMatrix (w349 (a hA) (b hB)) = decodeRows r349 := by
  unfold w349
  exact mul_check (eval348 hA hB) (eval336 hA hB) p407

theorem eval350 : toMatrix (w350 (a hA) (b hB)) = decodeRows r350 := by
  unfold w350
  have h1 : toMatrix ((w349 (a hA) (b hB)) ^ 1) = decodeRows r349 := by
    simpa only [pow_one] using (eval349 hA hB)
  have h2 : toMatrix ((w349 (a hA) (b hB)) ^ 2) = decodeRows q350_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p408
  have h3 : toMatrix ((w349 (a hA) (b hB)) ^ 3) = decodeRows q350_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p409
  have h4 : toMatrix ((w349 (a hA) (b hB)) ^ 4) = decodeRows q350_4 := by
    simpa only [← pow_add] using mul_check h2 h2 p410
  have h7 : toMatrix ((w349 (a hA) (b hB)) ^ 7) = decodeRows q350_7 := by
    simpa only [← pow_add] using mul_check h3 h4 p411
  have h8 : toMatrix ((w349 (a hA) (b hB)) ^ 8) = decodeRows q350_8 := by
    simpa only [← pow_add] using mul_check h4 h4 p412
  have h15 : toMatrix ((w349 (a hA) (b hB)) ^ 15) = decodeRows r350 := by
    simpa only [← pow_add] using mul_check h7 h8 p413
  exact h15

theorem eval351 : toMatrix (w351 (a hA) (b hB)) = decodeRows r351 := by
  unfold w351
  exact mul_check (eval171 hA hB) (eval2 hA hB) p414

theorem eval352 : toMatrix (w352 (a hA) (b hB)) = decodeRows r352 := by
  unfold w352
  exact mul_check (eval254 hA hB) (eval55 hA hB) p415

theorem eval353 : toMatrix (w353 (a hA) (b hB)) = decodeRows r353 := by
  unfold w353
  exact mul_check (eval352 hA hB) (eval0 hA hB) p416

theorem eval354 : toMatrix (w354 (a hA) (b hB)) = decodeRows r354 := by
  unfold w354
  exact mul_check (eval353 hA hB) (eval43 hA hB) p417

theorem eval355 : toMatrix (w355 (a hA) (b hB)) = decodeRows r355 := by
  unfold w355
  exact inv_check (eval354 hA hB) p418

theorem eval356 : toMatrix (w356 (a hA) (b hB)) = decodeRows r356 := by
  unfold w356
  exact mul_check (eval355 hA hB) (eval52 hA hB) p419

theorem eval357 : toMatrix (w357 (a hA) (b hB)) = decodeRows r357 := by
  unfold w357
  exact mul_check (eval356 hA hB) (eval354 hA hB) p420

theorem eval358 : toMatrix (w358 (a hA) (b hB)) = decodeRows r358 := by
  unfold w358
  exact mul_check (eval52 hA hB) (eval357 hA hB) p421

theorem eval359 : toMatrix (w359 (a hA) (b hB)) = decodeRows r359 := by
  unfold w359
  have h1 : toMatrix ((w358 (a hA) (b hB)) ^ 1) = decodeRows r358 := by
    simpa only [pow_one] using (eval358 hA hB)
  have h2 : toMatrix ((w358 (a hA) (b hB)) ^ 2) = decodeRows q359_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p422
  have h3 : toMatrix ((w358 (a hA) (b hB)) ^ 3) = decodeRows q359_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p423
  have h5 : toMatrix ((w358 (a hA) (b hB)) ^ 5) = decodeRows r359 := by
    simpa only [← pow_add] using mul_check h2 h3 p424
  exact h5

theorem eval360 : toMatrix (w360 (a hA) (b hB)) = decodeRows r360 := by
  unfold w360
  exact mul_check (eval270 hA hB) (eval55 hA hB) p425

theorem eval361 : toMatrix (w361 (a hA) (b hB)) = decodeRows r361 := by
  unfold w361
  exact inv_check (eval360 hA hB) p426

theorem eval362 : toMatrix (w362 (a hA) (b hB)) = decodeRows r362 := by
  unfold w362
  exact mul_check (eval361 hA hB) (eval52 hA hB) p427

theorem eval363 : toMatrix (w363 (a hA) (b hB)) = decodeRows r363 := by
  unfold w363
  exact mul_check (eval362 hA hB) (eval360 hA hB) p428

theorem eval364 : toMatrix (w364 (a hA) (b hB)) = decodeRows r364 := by
  unfold w364
  exact mul_check (eval52 hA hB) (eval363 hA hB) p429

theorem eval365 : toMatrix (w365 (a hA) (b hB)) = decodeRows r365 := by
  unfold w365
  have h1 : toMatrix ((w364 (a hA) (b hB)) ^ 1) = decodeRows r364 := by
    simpa only [pow_one] using (eval364 hA hB)
  have h2 : toMatrix ((w364 (a hA) (b hB)) ^ 2) = decodeRows q365_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p430
  have h3 : toMatrix ((w364 (a hA) (b hB)) ^ 3) = decodeRows q365_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p431
  have h5 : toMatrix ((w364 (a hA) (b hB)) ^ 5) = decodeRows r365 := by
    simpa only [← pow_add] using mul_check h2 h3 p432
  exact h5

theorem eval366 : toMatrix (w366 (a hA) (b hB)) = decodeRows r366 := by
  unfold w366
  exact mul_check (eval360 hA hB) (eval365 hA hB) p433

theorem eval367 : toMatrix (w367 (a hA) (b hB)) = decodeRows r367 := by
  unfold w367
  exact mul_check (eval92 hA hB) (eval43 hA hB) p434

theorem eval368 : toMatrix (w368 (a hA) (b hB)) = decodeRows r368 := by
  unfold w368
  exact mul_check (eval367 hA hB) (eval2 hA hB) p435

theorem eval369 : toMatrix (w369 (a hA) (b hB)) = decodeRows r369 := by
  unfold w369
  exact mul_check (eval368 hA hB) (eval1 hA hB) p436

theorem eval370 : toMatrix (w370 (a hA) (b hB)) = decodeRows r370 := by
  unfold w370
  exact mul_check (eval369 hA hB) (eval43 hA hB) p437

theorem eval371 : toMatrix (w371 (a hA) (b hB)) = decodeRows r371 := by
  unfold w371
  exact mul_check (eval370 hA hB) (eval1 hA hB) p438

theorem eval372 : toMatrix (w372 (a hA) (b hB)) = decodeRows r372 := by
  unfold w372
  exact mul_check (eval371 hA hB) (eval2 hA hB) p439

theorem eval373 : toMatrix (w373 (a hA) (b hB)) = decodeRows r373 := by
  unfold w373
  exact mul_check (eval372 hA hB) (eval2 hA hB) p440

theorem eval374 : toMatrix (w374 (a hA) (b hB)) = decodeRows r374 := by
  unfold w374
  exact mul_check (eval373 hA hB) (eval55 hA hB) p441

theorem eval375 : toMatrix (w375 (a hA) (b hB)) = decodeRows r375 := by
  unfold w375
  exact mul_check (eval374 hA hB) (eval55 hA hB) p442

theorem eval376 : toMatrix (w376 (a hA) (b hB)) = decodeRows r376 := by
  unfold w376
  exact mul_check (eval375 hA hB) (eval55 hA hB) p443

theorem eval377 : toMatrix (w377 (a hA) (b hB)) = decodeRows r377 := by
  unfold w377
  exact mul_check (eval376 hA hB) (eval1 hA hB) p444

theorem eval378 : toMatrix (w378 (a hA) (b hB)) = decodeRows r378 := by
  unfold w378
  exact mul_check (eval377 hA hB) (eval55 hA hB) p445

theorem eval379 : toMatrix (w379 (a hA) (b hB)) = decodeRows r379 := by
  unfold w379
  exact inv_check (eval378 hA hB) p446

theorem eval380 : toMatrix (w380 (a hA) (b hB)) = decodeRows r380 := by
  unfold w380
  exact mul_check (eval379 hA hB) (eval52 hA hB) p447

theorem eval381 : toMatrix (w381 (a hA) (b hB)) = decodeRows r381 := by
  unfold w381
  exact mul_check (eval380 hA hB) (eval378 hA hB) p448

theorem eval382 : toMatrix (w382 (a hA) (b hB)) = decodeRows r382 := by
  unfold w382
  exact mul_check (eval52 hA hB) (eval381 hA hB) p449

theorem eval383 : toMatrix (w383 (a hA) (b hB)) = decodeRows r383 := by
  unfold w383
  have h1 : toMatrix ((w382 (a hA) (b hB)) ^ 1) = decodeRows r382 := by
    simpa only [pow_one] using (eval382 hA hB)
  have h2 : toMatrix ((w382 (a hA) (b hB)) ^ 2) = decodeRows q383_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p450
  have h3 : toMatrix ((w382 (a hA) (b hB)) ^ 3) = decodeRows r383 := by
    simpa only [← pow_add] using mul_check h1 h2 p451
  exact h3

theorem eval384 : toMatrix (w384 (a hA) (b hB)) = decodeRows r384 := by
  unfold w384
  exact mul_check (eval108 hA hB) (eval1 hA hB) p452

theorem eval385 : toMatrix (w385 (a hA) (b hB)) = decodeRows r385 := by
  unfold w385
  exact mul_check (eval93 hA hB) (eval52 hA hB) p453

theorem eval386 : toMatrix (w386 (a hA) (b hB)) = decodeRows r386 := by
  unfold w386
  exact mul_check (eval385 hA hB) (eval384 hA hB) p454

theorem eval387 : toMatrix (w387 (a hA) (b hB)) = decodeRows r387 := by
  unfold w387
  exact mul_check (eval52 hA hB) (eval386 hA hB) p455

theorem eval388 : toMatrix (w388 (a hA) (b hB)) = decodeRows r388 := by
  unfold w388
  have h1 : toMatrix ((w387 (a hA) (b hB)) ^ 1) = decodeRows r387 := by
    simpa only [pow_one] using (eval387 hA hB)
  have h2 : toMatrix ((w387 (a hA) (b hB)) ^ 2) = decodeRows q388_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p456
  have h4 : toMatrix ((w387 (a hA) (b hB)) ^ 4) = decodeRows r388 := by
    simpa only [← pow_add] using mul_check h2 h2 p457
  exact h4

theorem eval389 : toMatrix (w389 (a hA) (b hB)) = decodeRows r389 := by
  unfold w389
  exact mul_check (eval160 hA hB) (eval43 hA hB) p458

theorem eval390 : toMatrix (w390 (a hA) (b hB)) = decodeRows r390 := by
  unfold w390
  exact mul_check (eval389 hA hB) (eval43 hA hB) p459

theorem eval391 : toMatrix (w391 (a hA) (b hB)) = decodeRows r391 := by
  unfold w391
  exact mul_check (eval390 hA hB) (eval2 hA hB) p460

theorem eval392 : toMatrix (w392 (a hA) (b hB)) = decodeRows r392 := by
  unfold w392
  exact mul_check (eval391 hA hB) (eval1 hA hB) p461

theorem eval393 : toMatrix (w393 (a hA) (b hB)) = decodeRows r393 := by
  unfold w393
  exact mul_check (eval392 hA hB) (eval0 hA hB) p462

theorem eval394 : toMatrix (w394 (a hA) (b hB)) = decodeRows r394 := by
  unfold w394
  exact mul_check (eval393 hA hB) (eval43 hA hB) p463

theorem eval395 : toMatrix (w395 (a hA) (b hB)) = decodeRows r395 := by
  unfold w395
  exact inv_check (eval394 hA hB) p464

theorem eval396 : toMatrix (w396 (a hA) (b hB)) = decodeRows r396 := by
  unfold w396
  exact mul_check (eval395 hA hB) (eval52 hA hB) p465

theorem eval397 : toMatrix (w397 (a hA) (b hB)) = decodeRows r397 := by
  unfold w397
  exact mul_check (eval396 hA hB) (eval394 hA hB) p466

theorem eval398 : toMatrix (w398 (a hA) (b hB)) = decodeRows r398 := by
  unfold w398
  exact mul_check (eval52 hA hB) (eval397 hA hB) p467

theorem eval399 : toMatrix (w399 (a hA) (b hB)) = decodeRows r399 := by
  unfold w399
  have h1 : toMatrix ((w398 (a hA) (b hB)) ^ 1) = decodeRows r398 := by
    simpa only [pow_one] using (eval398 hA hB)
  have h2 : toMatrix ((w398 (a hA) (b hB)) ^ 2) = decodeRows q399_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p468
  have h3 : toMatrix ((w398 (a hA) (b hB)) ^ 3) = decodeRows r399 := by
    simpa only [← pow_add] using mul_check h1 h2 p469
  exact h3

theorem eval400 : toMatrix (w400 (a hA) (b hB)) = decodeRows r400 := by
  unfold w400
  exact mul_check (eval150 hA hB) (eval1 hA hB) p470

theorem eval401 : toMatrix (w401 (a hA) (b hB)) = decodeRows r401 := by
  unfold w401
  exact mul_check (eval400 hA hB) (eval2 hA hB) p471

theorem eval402 : toMatrix (w402 (a hA) (b hB)) = decodeRows r402 := by
  unfold w402
  exact mul_check (eval401 hA hB) (eval55 hA hB) p472

theorem eval403 : toMatrix (w403 (a hA) (b hB)) = decodeRows r403 := by
  unfold w403
  exact mul_check (eval402 hA hB) (eval43 hA hB) p473

theorem eval404 : toMatrix (w404 (a hA) (b hB)) = decodeRows r404 := by
  unfold w404
  exact mul_check (eval403 hA hB) (eval0 hA hB) p474

theorem eval405 : toMatrix (w405 (a hA) (b hB)) = decodeRows r405 := by
  unfold w405
  exact inv_check (eval404 hA hB) p475

theorem eval406 : toMatrix (w406 (a hA) (b hB)) = decodeRows r406 := by
  unfold w406
  exact mul_check (eval405 hA hB) (eval52 hA hB) p476

theorem eval407 : toMatrix (w407 (a hA) (b hB)) = decodeRows r407 := by
  unfold w407
  exact mul_check (eval406 hA hB) (eval404 hA hB) p477

theorem eval408 : toMatrix (w408 (a hA) (b hB)) = decodeRows r408 := by
  unfold w408
  exact mul_check (eval52 hA hB) (eval407 hA hB) p478

theorem eval409 : toMatrix (w409 (a hA) (b hB)) = decodeRows r409 := by
  unfold w409
  have h1 : toMatrix ((w408 (a hA) (b hB)) ^ 1) = decodeRows r408 := by
    simpa only [pow_one] using (eval408 hA hB)
  have h2 : toMatrix ((w408 (a hA) (b hB)) ^ 2) = decodeRows q409_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p479
  have h3 : toMatrix ((w408 (a hA) (b hB)) ^ 3) = decodeRows q409_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p480
  have h6 : toMatrix ((w408 (a hA) (b hB)) ^ 6) = decodeRows r409 := by
    simpa only [← pow_add] using mul_check h3 h3 p481
  exact h6

theorem eval410 : toMatrix (w410 (a hA) (b hB)) = decodeRows r410 := by
  unfold w410
  exact mul_check (eval46 hA hB) (eval2 hA hB) p482

theorem eval411 : toMatrix (w411 (a hA) (b hB)) = decodeRows r411 := by
  unfold w411
  exact mul_check (eval410 hA hB) (eval43 hA hB) p483

theorem eval412 : toMatrix (w412 (a hA) (b hB)) = decodeRows r412 := by
  unfold w412
  exact mul_check (eval411 hA hB) (eval55 hA hB) p484

theorem eval413 : toMatrix (w413 (a hA) (b hB)) = decodeRows r413 := by
  unfold w413
  exact mul_check (eval412 hA hB) (eval0 hA hB) p485

theorem eval414 : toMatrix (w414 (a hA) (b hB)) = decodeRows r414 := by
  unfold w414
  exact mul_check (eval413 hA hB) (eval2 hA hB) p486

theorem eval415 : toMatrix (w415 (a hA) (b hB)) = decodeRows r415 := by
  unfold w415
  exact mul_check (eval414 hA hB) (eval2 hA hB) p487

theorem eval416 : toMatrix (w416 (a hA) (b hB)) = decodeRows r416 := by
  unfold w416
  exact mul_check (eval415 hA hB) (eval55 hA hB) p488

theorem eval417 : toMatrix (w417 (a hA) (b hB)) = decodeRows r417 := by
  unfold w417
  exact mul_check (eval416 hA hB) (eval43 hA hB) p489

theorem eval418 : toMatrix (w418 (a hA) (b hB)) = decodeRows r418 := by
  unfold w418
  exact mul_check (eval164 hA hB) (eval52 hA hB) p490

theorem eval419 : toMatrix (w419 (a hA) (b hB)) = decodeRows r419 := by
  unfold w419
  exact mul_check (eval418 hA hB) (eval417 hA hB) p491

theorem eval420 : toMatrix (w420 (a hA) (b hB)) = decodeRows r420 := by
  unfold w420
  exact mul_check (eval52 hA hB) (eval419 hA hB) p492

theorem eval421 : toMatrix (w421 (a hA) (b hB)) = decodeRows r421 := by
  unfold w421
  have h1 : toMatrix ((w420 (a hA) (b hB)) ^ 1) = decodeRows r420 := by
    simpa only [pow_one] using (eval420 hA hB)
  have h2 : toMatrix ((w420 (a hA) (b hB)) ^ 2) = decodeRows q421_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p493
  have h3 : toMatrix ((w420 (a hA) (b hB)) ^ 3) = decodeRows q421_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p494
  have h5 : toMatrix ((w420 (a hA) (b hB)) ^ 5) = decodeRows r421 := by
    simpa only [← pow_add] using mul_check h2 h3 p495
  exact h5

theorem eval422 : toMatrix (w422 (a hA) (b hB)) = decodeRows r422 := by
  unfold w422
  exact mul_check (eval351 hA hB) (eval2 hA hB) p496

theorem eval423 : toMatrix (w423 (a hA) (b hB)) = decodeRows r423 := by
  unfold w423
  exact mul_check (eval422 hA hB) (eval2 hA hB) p497

theorem eval424 : toMatrix (w424 (a hA) (b hB)) = decodeRows r424 := by
  unfold w424
  exact mul_check (eval423 hA hB) (eval1 hA hB) p498

theorem eval425 : toMatrix (w425 (a hA) (b hB)) = decodeRows r425 := by
  unfold w425
  exact inv_check (eval424 hA hB) p499

theorem eval426 : toMatrix (w426 (a hA) (b hB)) = decodeRows r426 := by
  unfold w426
  exact mul_check (eval425 hA hB) (eval52 hA hB) p500

theorem eval427 : toMatrix (w427 (a hA) (b hB)) = decodeRows r427 := by
  unfold w427
  exact mul_check (eval426 hA hB) (eval424 hA hB) p501

theorem eval428 : toMatrix (w428 (a hA) (b hB)) = decodeRows r428 := by
  unfold w428
  exact mul_check (eval52 hA hB) (eval427 hA hB) p502

theorem eval429 : toMatrix (w429 (a hA) (b hB)) = decodeRows r429 := by
  unfold w429
  have h1 : toMatrix ((w428 (a hA) (b hB)) ^ 1) = decodeRows r428 := by
    simpa only [pow_one] using (eval428 hA hB)
  have h2 : toMatrix ((w428 (a hA) (b hB)) ^ 2) = decodeRows q429_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p503
  have h3 : toMatrix ((w428 (a hA) (b hB)) ^ 3) = decodeRows q429_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p504
  have h6 : toMatrix ((w428 (a hA) (b hB)) ^ 6) = decodeRows r429 := by
    simpa only [← pow_add] using mul_check h3 h3 p505
  exact h6

theorem eval430 : toMatrix (w430 (a hA) (b hB)) = decodeRows r430 := by
  unfold w430
  exact mul_check (eval54 hA hB) (eval55 hA hB) p506

theorem eval431 : toMatrix (w431 (a hA) (b hB)) = decodeRows r431 := by
  unfold w431
  exact mul_check (eval430 hA hB) (eval43 hA hB) p507

theorem eval432 : toMatrix (w432 (a hA) (b hB)) = decodeRows r432 := by
  unfold w432
  exact mul_check (eval431 hA hB) (eval1 hA hB) p508

theorem eval433 : toMatrix (w433 (a hA) (b hB)) = decodeRows r433 := by
  unfold w433
  exact mul_check (eval432 hA hB) (eval55 hA hB) p509

theorem eval434 : toMatrix (w434 (a hA) (b hB)) = decodeRows r434 := by
  unfold w434
  exact mul_check (eval433 hA hB) (eval2 hA hB) p510

theorem eval435 : toMatrix (w435 (a hA) (b hB)) = decodeRows r435 := by
  unfold w435
  exact mul_check (eval434 hA hB) (eval1 hA hB) p511

theorem eval436 : toMatrix (w436 (a hA) (b hB)) = decodeRows r436 := by
  unfold w436
  exact mul_check (eval435 hA hB) (eval2 hA hB) p512

theorem eval437 : toMatrix (w437 (a hA) (b hB)) = decodeRows r437 := by
  unfold w437
  exact mul_check (eval436 hA hB) (eval43 hA hB) p513

theorem eval438 : toMatrix (w438 (a hA) (b hB)) = decodeRows r438 := by
  unfold w438
  exact mul_check (eval437 hA hB) (eval2 hA hB) p514

theorem eval439 : toMatrix (w439 (a hA) (b hB)) = decodeRows r439 := by
  unfold w439
  exact mul_check (eval438 hA hB) (eval0 hA hB) p515

theorem eval440 : toMatrix (w440 (a hA) (b hB)) = decodeRows r440 := by
  unfold w440
  exact inv_check (eval439 hA hB) p516

theorem eval441 : toMatrix (w441 (a hA) (b hB)) = decodeRows r441 := by
  unfold w441
  exact mul_check (eval440 hA hB) (eval52 hA hB) p517

theorem eval442 : toMatrix (w442 (a hA) (b hB)) = decodeRows r442 := by
  unfold w442
  exact mul_check (eval441 hA hB) (eval439 hA hB) p518

theorem eval443 : toMatrix (w443 (a hA) (b hB)) = decodeRows r443 := by
  unfold w443
  exact mul_check (eval52 hA hB) (eval442 hA hB) p519

theorem eval444 : toMatrix (w444 (a hA) (b hB)) = decodeRows r444 := by
  unfold w444
  have h1 : toMatrix ((w443 (a hA) (b hB)) ^ 1) = decodeRows r443 := by
    simpa only [pow_one] using (eval443 hA hB)
  have h2 : toMatrix ((w443 (a hA) (b hB)) ^ 2) = decodeRows q444_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p520
  have h3 : toMatrix ((w443 (a hA) (b hB)) ^ 3) = decodeRows q444_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p521
  have h6 : toMatrix ((w443 (a hA) (b hB)) ^ 6) = decodeRows r444 := by
    simpa only [← pow_add] using mul_check h3 h3 p522
  exact h6

theorem eval445 : toMatrix (w445 (a hA) (b hB)) = decodeRows r445 := by
  unfold w445
  exact mul_check (eval165 hA hB) (eval55 hA hB) p523

theorem eval446 : toMatrix (w446 (a hA) (b hB)) = decodeRows r446 := by
  unfold w446
  exact mul_check (eval445 hA hB) (eval0 hA hB) p524

theorem eval447 : toMatrix (w447 (a hA) (b hB)) = decodeRows r447 := by
  unfold w447
  exact inv_check (eval446 hA hB) p525

theorem eval448 : toMatrix (w448 (a hA) (b hB)) = decodeRows r448 := by
  unfold w448
  exact mul_check (eval447 hA hB) (eval52 hA hB) p526

theorem eval449 : toMatrix (w449 (a hA) (b hB)) = decodeRows r449 := by
  unfold w449
  exact mul_check (eval448 hA hB) (eval446 hA hB) p527

theorem eval450 : toMatrix (w450 (a hA) (b hB)) = decodeRows r450 := by
  unfold w450
  exact mul_check (eval52 hA hB) (eval449 hA hB) p528

theorem eval451 : toMatrix (w451 (a hA) (b hB)) = decodeRows r451 := by
  unfold w451
  have h1 : toMatrix ((w450 (a hA) (b hB)) ^ 1) = decodeRows r450 := by
    simpa only [pow_one] using (eval450 hA hB)
  have h2 : toMatrix ((w450 (a hA) (b hB)) ^ 2) = decodeRows q451_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p529
  have h3 : toMatrix ((w450 (a hA) (b hB)) ^ 3) = decodeRows q451_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p530
  have h6 : toMatrix ((w450 (a hA) (b hB)) ^ 6) = decodeRows r451 := by
    simpa only [← pow_add] using mul_check h3 h3 p531
  exact h6

theorem eval452 : toMatrix (w452 (a hA) (b hB)) = decodeRows r452 := by
  unfold w452
  exact mul_check (eval242 hA hB) (eval0 hA hB) p532

theorem eval453 : toMatrix (w453 (a hA) (b hB)) = decodeRows r453 := by
  unfold w453
  exact mul_check (eval452 hA hB) (eval1 hA hB) p533

theorem eval454 : toMatrix (w454 (a hA) (b hB)) = decodeRows r454 := by
  unfold w454
  exact mul_check (eval453 hA hB) (eval2 hA hB) p534

theorem eval455 : toMatrix (w455 (a hA) (b hB)) = decodeRows r455 := by
  unfold w455
  exact mul_check (eval454 hA hB) (eval55 hA hB) p535

theorem eval456 : toMatrix (w456 (a hA) (b hB)) = decodeRows r456 := by
  unfold w456
  exact mul_check (eval455 hA hB) (eval43 hA hB) p536

theorem eval457 : toMatrix (w457 (a hA) (b hB)) = decodeRows r457 := by
  unfold w457
  exact mul_check (eval456 hA hB) (eval1 hA hB) p537

theorem eval458 : toMatrix (w458 (a hA) (b hB)) = decodeRows r458 := by
  unfold w458
  exact mul_check (eval457 hA hB) (eval43 hA hB) p538

theorem eval459 : toMatrix (w459 (a hA) (b hB)) = decodeRows r459 := by
  unfold w459
  exact mul_check (eval458 hA hB) (eval43 hA hB) p539

theorem eval460 : toMatrix (w460 (a hA) (b hB)) = decodeRows r460 := by
  unfold w460
  exact mul_check (eval459 hA hB) (eval1 hA hB) p540

theorem eval461 : toMatrix (w461 (a hA) (b hB)) = decodeRows r461 := by
  unfold w461
  exact mul_check (eval460 hA hB) (eval43 hA hB) p541

theorem eval462 : toMatrix (w462 (a hA) (b hB)) = decodeRows r462 := by
  unfold w462
  exact inv_check (eval461 hA hB) p542

theorem eval463 : toMatrix (w463 (a hA) (b hB)) = decodeRows r463 := by
  unfold w463
  exact mul_check (eval462 hA hB) (eval52 hA hB) p543

theorem eval464 : toMatrix (w464 (a hA) (b hB)) = decodeRows r464 := by
  unfold w464
  exact mul_check (eval463 hA hB) (eval461 hA hB) p544

theorem eval465 : toMatrix (w465 (a hA) (b hB)) = decodeRows r465 := by
  unfold w465
  exact mul_check (eval52 hA hB) (eval464 hA hB) p545

theorem eval466 : toMatrix (w466 (a hA) (b hB)) = decodeRows r466 := by
  unfold w466
  have h1 : toMatrix ((w465 (a hA) (b hB)) ^ 1) = decodeRows r465 := by
    simpa only [pow_one] using (eval465 hA hB)
  have h2 : toMatrix ((w465 (a hA) (b hB)) ^ 2) = decodeRows r466 := by
    simpa only [← pow_add] using mul_check h1 h1 p546
  exact h2

theorem eval467 : toMatrix (w467 (a hA) (b hB)) = decodeRows r467 := by
  unfold w467
  exact mul_check (eval461 hA hB) (eval466 hA hB) p547

theorem eval468 : toMatrix (w468 (a hA) (b hB)) = decodeRows r468 := by
  unfold w468
  exact mul_check (eval73 hA hB) (eval43 hA hB) p548

theorem eval469 : toMatrix (w469 (a hA) (b hB)) = decodeRows r469 := by
  unfold w469
  exact mul_check (eval468 hA hB) (eval43 hA hB) p549

theorem eval470 : toMatrix (w470 (a hA) (b hB)) = decodeRows r470 := by
  unfold w470
  exact mul_check (eval469 hA hB) (eval1 hA hB) p550

theorem eval471 : toMatrix (w471 (a hA) (b hB)) = decodeRows r471 := by
  unfold w471
  exact mul_check (eval470 hA hB) (eval43 hA hB) p551

theorem eval472 : toMatrix (w472 (a hA) (b hB)) = decodeRows r472 := by
  unfold w472
  exact mul_check (eval471 hA hB) (eval1 hA hB) p552

theorem eval473 : toMatrix (w473 (a hA) (b hB)) = decodeRows r473 := by
  unfold w473
  exact mul_check (eval472 hA hB) (eval2 hA hB) p553

theorem eval474 : toMatrix (w474 (a hA) (b hB)) = decodeRows r474 := by
  unfold w474
  exact mul_check (eval473 hA hB) (eval0 hA hB) p554

theorem eval475 : toMatrix (w475 (a hA) (b hB)) = decodeRows r475 := by
  unfold w475
  exact inv_check (eval474 hA hB) p555

theorem eval476 : toMatrix (w476 (a hA) (b hB)) = decodeRows r476 := by
  unfold w476
  exact mul_check (eval475 hA hB) (eval52 hA hB) p556

theorem eval477 : toMatrix (w477 (a hA) (b hB)) = decodeRows r477 := by
  unfold w477
  exact mul_check (eval476 hA hB) (eval474 hA hB) p557

theorem eval478 : toMatrix (w478 (a hA) (b hB)) = decodeRows r478 := by
  unfold w478
  exact mul_check (eval52 hA hB) (eval477 hA hB) p558

theorem eval479 : toMatrix (w479 (a hA) (b hB)) = decodeRows r479 := by
  unfold w479
  have h1 : toMatrix ((w478 (a hA) (b hB)) ^ 1) = decodeRows r478 := by
    simpa only [pow_one] using (eval478 hA hB)
  have h2 : toMatrix ((w478 (a hA) (b hB)) ^ 2) = decodeRows q479_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p559
  have h3 : toMatrix ((w478 (a hA) (b hB)) ^ 3) = decodeRows q479_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p560
  have h5 : toMatrix ((w478 (a hA) (b hB)) ^ 5) = decodeRows r479 := by
    simpa only [← pow_add] using mul_check h2 h3 p561
  exact h5

theorem eval480 : toMatrix (w480 (a hA) (b hB)) = decodeRows r480 := by
  unfold w480
  exact mul_check (eval474 hA hB) (eval479 hA hB) p562

theorem eval481 : toMatrix (w481 (a hA) (b hB)) = decodeRows r481 := by
  unfold w481
  exact mul_check (eval1 hA hB) (eval2 hA hB) p563

theorem eval482 : toMatrix (w482 (a hA) (b hB)) = decodeRows r482 := by
  unfold w482
  exact mul_check (eval481 hA hB) (eval43 hA hB) p564

theorem eval483 : toMatrix (w483 (a hA) (b hB)) = decodeRows r483 := by
  unfold w483
  exact mul_check (eval482 hA hB) (eval43 hA hB) p565

theorem eval484 : toMatrix (w484 (a hA) (b hB)) = decodeRows r484 := by
  unfold w484
  exact mul_check (eval483 hA hB) (eval1 hA hB) p566

theorem eval485 : toMatrix (w485 (a hA) (b hB)) = decodeRows r485 := by
  unfold w485
  exact mul_check (eval484 hA hB) (eval1 hA hB) p567

theorem eval486 : toMatrix (w486 (a hA) (b hB)) = decodeRows r486 := by
  unfold w486
  exact mul_check (eval485 hA hB) (eval1 hA hB) p568

theorem eval487 : toMatrix (w487 (a hA) (b hB)) = decodeRows r487 := by
  unfold w487
  exact mul_check (eval486 hA hB) (eval0 hA hB) p569

theorem eval488 : toMatrix (w488 (a hA) (b hB)) = decodeRows r488 := by
  unfold w488
  exact mul_check (eval487 hA hB) (eval1 hA hB) p570

theorem eval489 : toMatrix (w489 (a hA) (b hB)) = decodeRows r489 := by
  unfold w489
  exact mul_check (eval488 hA hB) (eval43 hA hB) p571

theorem eval490 : toMatrix (w490 (a hA) (b hB)) = decodeRows r490 := by
  unfold w490
  exact mul_check (eval489 hA hB) (eval55 hA hB) p572

theorem eval491 : toMatrix (w491 (a hA) (b hB)) = decodeRows r491 := by
  unfold w491
  exact mul_check (eval490 hA hB) (eval43 hA hB) p573

theorem eval492 : toMatrix (w492 (a hA) (b hB)) = decodeRows r492 := by
  unfold w492
  exact mul_check (eval491 hA hB) (eval43 hA hB) p574

theorem eval493 : toMatrix (w493 (a hA) (b hB)) = decodeRows r493 := by
  unfold w493
  exact mul_check (eval492 hA hB) (eval55 hA hB) p575

theorem eval494 : toMatrix (w494 (a hA) (b hB)) = decodeRows r494 := by
  unfold w494
  exact mul_check (eval493 hA hB) (eval2 hA hB) p576

theorem eval495 : toMatrix (w495 (a hA) (b hB)) = decodeRows r495 := by
  unfold w495
  exact inv_check (eval494 hA hB) p577

theorem eval496 : toMatrix (w496 (a hA) (b hB)) = decodeRows r496 := by
  unfold w496
  exact mul_check (eval495 hA hB) (eval52 hA hB) p578

theorem eval497 : toMatrix (w497 (a hA) (b hB)) = decodeRows r497 := by
  unfold w497
  exact mul_check (eval496 hA hB) (eval494 hA hB) p579

theorem eval498 : toMatrix (w498 (a hA) (b hB)) = decodeRows r498 := by
  unfold w498
  exact mul_check (eval52 hA hB) (eval497 hA hB) p580

theorem eval499 : toMatrix (w499 (a hA) (b hB)) = decodeRows r499 := by
  unfold w499
  have h1 : toMatrix ((w498 (a hA) (b hB)) ^ 1) = decodeRows r498 := by
    simpa only [pow_one] using (eval498 hA hB)
  have h2 : toMatrix ((w498 (a hA) (b hB)) ^ 2) = decodeRows q499_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p581
  have h3 : toMatrix ((w498 (a hA) (b hB)) ^ 3) = decodeRows q499_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p582
  have h6 : toMatrix ((w498 (a hA) (b hB)) ^ 6) = decodeRows r499 := by
    simpa only [← pow_add] using mul_check h3 h3 p583
  exact h6

theorem eval500 : toMatrix (w500 (a hA) (b hB)) = decodeRows r500 := by
  unfold w500
  exact mul_check (eval415 hA hB) (eval0 hA hB) p584

theorem eval501 : toMatrix (w501 (a hA) (b hB)) = decodeRows r501 := by
  unfold w501
  exact mul_check (eval500 hA hB) (eval1 hA hB) p585

theorem eval502 : toMatrix (w502 (a hA) (b hB)) = decodeRows r502 := by
  unfold w502
  exact mul_check (eval501 hA hB) (eval2 hA hB) p586

theorem eval503 : toMatrix (w503 (a hA) (b hB)) = decodeRows r503 := by
  unfold w503
  exact mul_check (eval502 hA hB) (eval1 hA hB) p587

theorem eval504 : toMatrix (w504 (a hA) (b hB)) = decodeRows r504 := by
  unfold w504
  exact mul_check (eval503 hA hB) (eval2 hA hB) p588

theorem eval505 : toMatrix (w505 (a hA) (b hB)) = decodeRows r505 := by
  unfold w505
  exact mul_check (eval504 hA hB) (eval55 hA hB) p589

theorem eval506 : toMatrix (w506 (a hA) (b hB)) = decodeRows r506 := by
  unfold w506
  exact mul_check (eval505 hA hB) (eval1 hA hB) p590

theorem eval507 : toMatrix (w507 (a hA) (b hB)) = decodeRows r507 := by
  unfold w507
  exact mul_check (eval506 hA hB) (eval55 hA hB) p591

theorem eval508 : toMatrix (w508 (a hA) (b hB)) = decodeRows r508 := by
  unfold w508
  exact inv_check (eval507 hA hB) p592

theorem eval509 : toMatrix (w509 (a hA) (b hB)) = decodeRows r509 := by
  unfold w509
  exact mul_check (eval508 hA hB) (eval52 hA hB) p593

theorem eval510 : toMatrix (w510 (a hA) (b hB)) = decodeRows r510 := by
  unfold w510
  exact mul_check (eval509 hA hB) (eval507 hA hB) p594

theorem eval511 : toMatrix (w511 (a hA) (b hB)) = decodeRows r511 := by
  unfold w511
  exact mul_check (eval52 hA hB) (eval510 hA hB) p595

theorem eval512 : toMatrix (w512 (a hA) (b hB)) = decodeRows r512 := by
  unfold w512
  have h1 : toMatrix ((w511 (a hA) (b hB)) ^ 1) = decodeRows r511 := by
    simpa only [pow_one] using (eval511 hA hB)
  have h2 : toMatrix ((w511 (a hA) (b hB)) ^ 2) = decodeRows q512_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p596
  have h3 : toMatrix ((w511 (a hA) (b hB)) ^ 3) = decodeRows q512_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p597
  have h6 : toMatrix ((w511 (a hA) (b hB)) ^ 6) = decodeRows r512 := by
    simpa only [← pow_add] using mul_check h3 h3 p598
  exact h6

theorem eval513 : toMatrix (w513 (a hA) (b hB)) = decodeRows r513 := by
  unfold w513
  exact mul_check (eval93 hA hB) (eval55 hA hB) p599

theorem eval514 : toMatrix (w514 (a hA) (b hB)) = decodeRows r514 := by
  unfold w514
  exact mul_check (eval513 hA hB) (eval43 hA hB) p600

theorem eval515 : toMatrix (w515 (a hA) (b hB)) = decodeRows r515 := by
  unfold w515
  exact mul_check (eval514 hA hB) (eval2 hA hB) p601

theorem eval516 : toMatrix (w516 (a hA) (b hB)) = decodeRows r516 := by
  unfold w516
  exact mul_check (eval515 hA hB) (eval55 hA hB) p602

theorem eval517 : toMatrix (w517 (a hA) (b hB)) = decodeRows r517 := by
  unfold w517
  exact mul_check (eval516 hA hB) (eval0 hA hB) p603

theorem eval518 : toMatrix (w518 (a hA) (b hB)) = decodeRows r518 := by
  unfold w518
  exact mul_check (eval517 hA hB) (eval43 hA hB) p604

theorem eval519 : toMatrix (w519 (a hA) (b hB)) = decodeRows r519 := by
  unfold w519
  exact mul_check (eval518 hA hB) (eval0 hA hB) p605

theorem eval520 : toMatrix (w520 (a hA) (b hB)) = decodeRows r520 := by
  unfold w520
  exact mul_check (eval519 hA hB) (eval2 hA hB) p606

theorem eval521 : toMatrix (w521 (a hA) (b hB)) = decodeRows r521 := by
  unfold w521
  exact mul_check (eval520 hA hB) (eval43 hA hB) p607

theorem eval522 : toMatrix (w522 (a hA) (b hB)) = decodeRows r522 := by
  unfold w522
  exact mul_check (eval521 hA hB) (eval0 hA hB) p608

theorem eval523 : toMatrix (w523 (a hA) (b hB)) = decodeRows r523 := by
  unfold w523
  exact mul_check (eval522 hA hB) (eval1 hA hB) p609

theorem eval524 : toMatrix (w524 (a hA) (b hB)) = decodeRows r524 := by
  unfold w524
  exact mul_check (eval523 hA hB) (eval1 hA hB) p610

theorem eval525 : toMatrix (w525 (a hA) (b hB)) = decodeRows r525 := by
  unfold w525
  exact mul_check (eval524 hA hB) (eval1 hA hB) p611

theorem eval526 : toMatrix (w526 (a hA) (b hB)) = decodeRows r526 := by
  unfold w526
  exact inv_check (eval525 hA hB) p612

theorem eval527 : toMatrix (w527 (a hA) (b hB)) = decodeRows r527 := by
  unfold w527
  exact mul_check (eval526 hA hB) (eval52 hA hB) p613

theorem eval528 : toMatrix (w528 (a hA) (b hB)) = decodeRows r528 := by
  unfold w528
  exact mul_check (eval527 hA hB) (eval525 hA hB) p614

theorem eval529 : toMatrix (w529 (a hA) (b hB)) = decodeRows r529 := by
  unfold w529
  exact mul_check (eval52 hA hB) (eval528 hA hB) p615

theorem eval530 : toMatrix (w530 (a hA) (b hB)) = decodeRows r530 := by
  unfold w530
  have h1 : toMatrix ((w529 (a hA) (b hB)) ^ 1) = decodeRows r529 := by
    simpa only [pow_one] using (eval529 hA hB)
  have h2 : toMatrix ((w529 (a hA) (b hB)) ^ 2) = decodeRows q530_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p616
  have h3 : toMatrix ((w529 (a hA) (b hB)) ^ 3) = decodeRows q530_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p617
  have h6 : toMatrix ((w529 (a hA) (b hB)) ^ 6) = decodeRows r530 := by
    simpa only [← pow_add] using mul_check h3 h3 p618
  exact h6

theorem eval531 : toMatrix (w531 (a hA) (b hB)) = decodeRows r531 := by
  unfold w531
  exact inv_check (eval513 hA hB) p619

theorem eval532 : toMatrix (w532 (a hA) (b hB)) = decodeRows r532 := by
  unfold w532
  exact mul_check (eval531 hA hB) (eval52 hA hB) p620

theorem eval533 : toMatrix (w533 (a hA) (b hB)) = decodeRows r533 := by
  unfold w533
  exact mul_check (eval532 hA hB) (eval513 hA hB) p621

theorem eval534 : toMatrix (w534 (a hA) (b hB)) = decodeRows r534 := by
  unfold w534
  exact mul_check (eval52 hA hB) (eval533 hA hB) p622

theorem eval535 : toMatrix (w535 (a hA) (b hB)) = decodeRows r535 := by
  unfold w535
  have h1 : toMatrix ((w534 (a hA) (b hB)) ^ 1) = decodeRows r534 := by
    simpa only [pow_one] using (eval534 hA hB)
  have h2 : toMatrix ((w534 (a hA) (b hB)) ^ 2) = decodeRows q535_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p623
  have h3 : toMatrix ((w534 (a hA) (b hB)) ^ 3) = decodeRows q535_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p624
  have h6 : toMatrix ((w534 (a hA) (b hB)) ^ 6) = decodeRows r535 := by
    simpa only [← pow_add] using mul_check h3 h3 p625
  exact h6

theorem eval536 : toMatrix (w536 (a hA) (b hB)) = decodeRows r536 := by
  unfold w536
  exact mul_check (eval501 hA hB) (eval55 hA hB) p626

theorem eval537 : toMatrix (w537 (a hA) (b hB)) = decodeRows r537 := by
  unfold w537
  exact mul_check (eval536 hA hB) (eval2 hA hB) p627

theorem eval538 : toMatrix (w538 (a hA) (b hB)) = decodeRows r538 := by
  unfold w538
  exact mul_check (eval537 hA hB) (eval0 hA hB) p628

theorem eval539 : toMatrix (w539 (a hA) (b hB)) = decodeRows r539 := by
  unfold w539
  exact mul_check (eval538 hA hB) (eval2 hA hB) p629

theorem eval540 : toMatrix (w540 (a hA) (b hB)) = decodeRows r540 := by
  unfold w540
  exact inv_check (eval539 hA hB) p630

theorem eval541 : toMatrix (w541 (a hA) (b hB)) = decodeRows r541 := by
  unfold w541
  exact mul_check (eval540 hA hB) (eval314 hA hB) p631

theorem eval542 : toMatrix (w542 (a hA) (b hB)) = decodeRows r542 := by
  unfold w542
  exact mul_check (eval541 hA hB) (eval539 hA hB) p632

theorem eval543 : toMatrix (w543 (a hA) (b hB)) = decodeRows r543 := by
  unfold w543
  exact mul_check (eval542 hA hB) (eval52 hA hB) p633

theorem eval544 : toMatrix (w544 (a hA) (b hB)) = decodeRows r544 := by
  unfold w544
  have h1 : toMatrix ((w543 (a hA) (b hB)) ^ 1) = decodeRows r543 := by
    simpa only [pow_one] using (eval543 hA hB)
  have h2 : toMatrix ((w543 (a hA) (b hB)) ^ 2) = decodeRows q544_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p634
  have h3 : toMatrix ((w543 (a hA) (b hB)) ^ 3) = decodeRows q544_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p635
  have h6 : toMatrix ((w543 (a hA) (b hB)) ^ 6) = decodeRows r544 := by
    simpa only [← pow_add] using mul_check h3 h3 p636
  exact h6

theorem eval545 : toMatrix (w545 (a hA) (b hB)) = decodeRows r545 := by
  unfold w545
  exact mul_check (eval539 hA hB) (eval544 hA hB) p637

theorem eval546 : toMatrix (w546 (a hA) (b hB)) = decodeRows r546 := by
  unfold w546
  exact mul_check (eval429 hA hB) (eval359 hA hB) p638

theorem eval547 : toMatrix (w547 (a hA) (b hB)) = decodeRows r547 := by
  unfold w547
  exact mul_check (eval546 hA hB) (eval366 hA hB) p639

theorem eval548 : toMatrix (w548 (a hA) (b hB)) = decodeRows r548 := by
  unfold w548
  exact mul_check (eval547 hA hB) (eval530 hA hB) p640

theorem eval549 : toMatrix (w549 (a hA) (b hB)) = decodeRows r549 := by
  unfold w549
  exact mul_check (eval480 hA hB) (eval499 hA hB) p641

theorem eval550 : toMatrix (w550 (a hA) (b hB)) = decodeRows r550 := by
  unfold w550
  exact mul_check (eval548 hA hB) (eval399 hA hB) p642

theorem eval551 : toMatrix (w551 (a hA) (b hB)) = decodeRows r551 := by
  unfold w551
  exact mul_check (eval549 hA hB) (eval409 hA hB) p643

theorem eval552 : toMatrix (w552 (a hA) (b hB)) = decodeRows r552 := by
  unfold w552
  exact mul_check (eval551 hA hB) (eval444 hA hB) p644

theorem eval553 : toMatrix (w553 (a hA) (b hB)) = decodeRows r553 := by
  unfold w553
  exact mul_check (eval550 hA hB) (eval429 hA hB) p645

theorem eval554 : toMatrix (w554 (a hA) (b hB)) = decodeRows r554 := by
  unfold w554
  exact inv_check (eval553 hA hB) p646

theorem eval555 : toMatrix (w555 (a hA) (b hB)) = decodeRows r555 := by
  unfold w555
  exact mul_check (eval552 hA hB) (eval554 hA hB) p647

theorem eval556 : toMatrix (w556 (a hA) (b hB)) = decodeRows r556 := by
  unfold w556
  exact mul_check (eval545 hA hB) (eval555 hA hB) p648

theorem eval557 : toMatrix (w557 (a hA) (b hB)) = decodeRows r557 := by
  unfold w557
  exact mul_check (eval389 hA hB) (eval2 hA hB) p649

theorem eval558 : toMatrix (w558 (a hA) (b hB)) = decodeRows r558 := by
  unfold w558
  exact mul_check (eval557 hA hB) (eval2 hA hB) p650

theorem eval559 : toMatrix (w559 (a hA) (b hB)) = decodeRows r559 := by
  unfold w559
  exact mul_check (eval558 hA hB) (eval1 hA hB) p651

theorem eval560 : toMatrix (w560 (a hA) (b hB)) = decodeRows r560 := by
  unfold w560
  exact mul_check (eval559 hA hB) (eval43 hA hB) p652

theorem eval561 : toMatrix (w561 (a hA) (b hB)) = decodeRows r561 := by
  unfold w561
  exact mul_check (eval560 hA hB) (eval1 hA hB) p653

theorem eval562 : toMatrix (w562 (a hA) (b hB)) = decodeRows r562 := by
  unfold w562
  exact mul_check (eval561 hA hB) (eval2 hA hB) p654

theorem eval563 : toMatrix (w563 (a hA) (b hB)) = decodeRows r563 := by
  unfold w563
  exact mul_check (eval562 hA hB) (eval55 hA hB) p655

theorem eval564 : toMatrix (w564 (a hA) (b hB)) = decodeRows r564 := by
  unfold w564
  exact inv_check (eval563 hA hB) p656

theorem eval565 : toMatrix (w565 (a hA) (b hB)) = decodeRows r565 := by
  unfold w565
  exact mul_check (eval564 hA hB) (eval350 hA hB) p657

theorem eval566 : toMatrix (w566 (a hA) (b hB)) = decodeRows r566 := by
  unfold w566
  exact mul_check (eval565 hA hB) (eval563 hA hB) p658

theorem eval567 : toMatrix (w567 (a hA) (b hB)) = decodeRows r567 := by
  unfold w567
  exact mul_check (eval566 hA hB) (eval52 hA hB) p659

theorem eval568 : toMatrix (w568 (a hA) (b hB)) = decodeRows r568 := by
  unfold w568
  have h1 : toMatrix ((w567 (a hA) (b hB)) ^ 1) = decodeRows r567 := by
    simpa only [pow_one] using (eval567 hA hB)
  have h2 : toMatrix ((w567 (a hA) (b hB)) ^ 2) = decodeRows q568_2 := by
    simpa only [← pow_add] using mul_check h1 h1 p660
  have h3 : toMatrix ((w567 (a hA) (b hB)) ^ 3) = decodeRows q568_3 := by
    simpa only [← pow_add] using mul_check h1 h2 p661
  have h6 : toMatrix ((w567 (a hA) (b hB)) ^ 6) = decodeRows r568 := by
    simpa only [← pow_add] using mul_check h3 h3 p662
  exact h6

theorem eval569 : toMatrix (w569 (a hA) (b hB)) = decodeRows r569 := by
  unfold w569
  exact mul_check (eval563 hA hB) (eval568 hA hB) p663

theorem eval570 : toMatrix (w570 (a hA) (b hB)) = decodeRows r570 := by
  unfold w570
  exact mul_check (eval421 hA hB) (eval409 hA hB) p664

theorem eval571 : toMatrix (w571 (a hA) (b hB)) = decodeRows r571 := by
  unfold w571
  exact mul_check (eval467 hA hB) (eval535 hA hB) p665

theorem eval572 : toMatrix (w572 (a hA) (b hB)) = decodeRows r572 := by
  unfold w572
  exact mul_check (eval571 hA hB) (eval383 hA hB) p666

theorem eval573 : toMatrix (w573 (a hA) (b hB)) = decodeRows r573 := by
  unfold w573
  exact mul_check (eval572 hA hB) (eval467 hA hB) p667

theorem eval574 : toMatrix (w574 (a hA) (b hB)) = decodeRows r574 := by
  unfold w574
  exact mul_check (eval570 hA hB) (eval388 hA hB) p668

theorem eval575 : toMatrix (w575 (a hA) (b hB)) = decodeRows r575 := by
  unfold w575
  exact mul_check (eval573 hA hB) (eval409 hA hB) p669

theorem eval576 : toMatrix (w576 (a hA) (b hB)) = decodeRows r576 := by
  unfold w576
  exact mul_check (eval575 hA hB) (eval444 hA hB) p670

theorem eval577 : toMatrix (w577 (a hA) (b hB)) = decodeRows r577 := by
  unfold w577
  exact mul_check (eval576 hA hB) (eval383 hA hB) p671

theorem eval578 : toMatrix (w578 (a hA) (b hB)) = decodeRows r578 := by
  unfold w578
  exact mul_check (eval577 hA hB) (eval512 hA hB) p672

theorem eval579 : toMatrix (w579 (a hA) (b hB)) = decodeRows r579 := by
  unfold w579
  exact mul_check (eval574 hA hB) (eval421 hA hB) p673

theorem eval580 : toMatrix (w580 (a hA) (b hB)) = decodeRows r580 := by
  unfold w580
  exact mul_check (eval578 hA hB) (eval480 hA hB) p674

theorem eval581 : toMatrix (w581 (a hA) (b hB)) = decodeRows r581 := by
  unfold w581
  exact mul_check (eval579 hA hB) (eval451 hA hB) p675

theorem eval582 : toMatrix (w582 (a hA) (b hB)) = decodeRows r582 := by
  unfold w582
  exact inv_check (eval581 hA hB) p676

theorem eval583 : toMatrix (w583 (a hA) (b hB)) = decodeRows r583 := by
  unfold w583
  exact mul_check (eval580 hA hB) (eval582 hA hB) p677

theorem eval584 : toMatrix (w584 (a hA) (b hB)) = decodeRows r584 := by
  unfold w584
  exact mul_check (eval569 hA hB) (eval583 hA hB) p678


end Janko4.Simplicity.ThreeFusion
