module

public import Theory.GroupTheory.Recognition.HeldM22A10.CentralizerSplitting.NonsplitAlternatives.StandardExtensions.TwistedCohomology.PolynomialTables
public import Mathlib.Tactic.FinCases
/-!
# Elimination of the normalized twisted cocycle equations

Ninety-five cocycle equations, interpreted by `PolynomialTables`, eliminate
ninety-five of the one hundred edge coordinates. Each pivot is an explicit
XOR combination of a cocycle equation and preceding pivots. Back substitution
expresses every coordinate in entries 0, 4, 6, 8, and 9.

The generator in `source/certificates.py` finds these combinations; every
polynomial equality and combination is checked by Lean. No dimension or
classification result is assumed. Source context: Huppert--Blackburn III,
XII.1.18(b), p.314, independent finite extension step.
-/

namespace Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions.TwistedCohomology
open LocalModelDichotomy AbelianExtension
attribute [local irreducible] value
private theorem pivot0 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 67787047715939478195438354447 = 0 := by
  have h0 : value x 67787047715939478195438354447 = 0 := by
    have hm : equation 6 1 1 0 = 67787047715939478195438354447 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot1 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 18584077205646454835323600896 = 0 := by
  have h0 : value x 71496188632693952224016990223 = 0 := by
    have hm : equation 6 1 1 1 = 71496188632693952224016990223 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot0 x h)

private theorem pivot2 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 31579812113370339987857342476 = 0 := by
  have h0 : value x 58495183305720767515491041283 = 0 := by
    have hm : equation 6 1 1 2 = 58495183305720767515491041283 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot0 x h)

private theorem pivot3 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 7441831666416394176678592527 = 0 := by
  have h0 : value x 38996964508079816661553643523 = 0 := by
    have hm : equation 6 1 1 3 = 38996964508079816661553643523 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot2 x h)

private theorem pivot4 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 554754297956418279827065274625 = 0 := by
  have h0 : value x 554754297956418279827065274625 = 0 := by
    have hm : equation 6 1 2 0 = 554754297956418279827065274625 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot5 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1109276482155470550646428533250 = 0 := by
  have h0 : value x 1109276482155470550646428533250 = 0 := by
    have hm : equation 6 1 2 1 = 1109276482155470550646428533250 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot6 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 237806589050614623067520894470 = 0 := by
  have h0 : value x 1030006007237488176040536704004 = 0 := by
    have hm : equation 6 1 2 2 = 1030006007237488176040536704004 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot5 x h)

private theorem pivot7 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 79454231642563798721483509005 = 0 := by
  have h0 : value x 871538801876587472721784342536 = 0 := by
    have hm : equation 6 1 2 3 = 871538801876587472721784342536 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot4 x h)) (pivot6 x h)

private theorem pivot8 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 309485009822470968631628001 = 0 := by
  have h0 : value x 309485009822470968631628001 = 0 := by
    have hm : equation 6 1 3 0 = 309485009822470968631628001 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot9 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2475880078573012349611942098 = 0 := by
  have h0 : value x 2475880078573012349611942098 = 0 := by
    have hm : equation 6 1 3 1 = 2475880078573012349611942098 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot10 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 618970019642971612426289268 = 0 := by
  have h0 : value x 618970019642971612426289268 = 0 := by
    have hm : equation 6 1 3 2 = 618970019642971612426289268 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot11 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1237940039285943224852578488 = 0 := by
  have h0 : value x 1237940039285943224852578488 = 0 := by
    have hm : equation 6 1 3 3 = 1237940039285943224852578488 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot12 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 52245790902763877568001 = 0 := by
  have h0 : value x 52245790902763877568001 = 0 := by
    have hm : equation 6 1 4 0 = 52245790902763877568001 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot13 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 29233477670811211924227 = 0 := by
  have h0 : value x 61990283459700948208898 = 0 := by
    have hm : equation 6 1 4 1 = 61990283459700948208898 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot12 x h)

private theorem pivot14 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 15948363173226514221574 = 0 := by
  have h0 : value x 67294875302397051143940 = 0 := by
    have hm : equation 6 1 4 2 = 67294875302397051143940 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (h0) (pivot12 x h)) (pivot13 x h)

private theorem pivot15 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 7985134340907022157835 = 0 := by
  have h0 : value x 35420054464531552799496 = 0 := by
    have hm : equation 6 1 4 3 = 35420054464531552799496 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot13 x h)

private theorem pivot16 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 52177535264903659535 = 0 := by
  have h0 : value x 1064667723874852749934157946897 = 0 := by
    have hm : equation 6 1 5 0 = 1064667723874852749934157946897 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot6 x h)) (pivot2 x h)) (pivot3 x h)) (pivot9 x h)) (pivot11 x h)) (pivot10 x h)) (pivot12 x h)) (pivot14 x h)

private theorem pivot17 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 156259069360672342031 = 0 := by
  have h0 : value x 1178596590884168734475372515362 = 0 := by
    have hm : equation 6 1 5 1 = 1178596590884168734475372515362 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot0 x h)) (pivot1 x h)) (pivot11 x h)) (pivot10 x h)) (pivot8 x h)) (pivot14 x h)) (pivot15 x h)

private theorem pivot18 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 90012740759142268943 = 0 := by
  have h0 : value x 935902163628660846706380795972 = 0 := by
    have hm : equation 6 1 5 2 = 935902163628660846706380795972 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot4 x h)) (pivot6 x h)) (pivot7 x h)) (pivot0 x h)) (pivot9 x h)) (pivot10 x h)) (pivot8 x h)) (pivot15 x h)

private theorem pivot19 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 31295211925936275471 = 0 := by
  have h0 : value x 609221317391325623180781990024 = 0 := by
    have hm : equation 6 1 5 3 = 609221317391325623180781990024 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot4 x h)) (pivot0 x h)) (pivot2 x h)) (pivot9 x h)) (pivot11 x h)) (pivot8 x h)) (pivot13 x h)) (pivot14 x h)) (pivot15 x h)

private theorem pivot20 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1966081 = 0 := by
  have h0 : value x 1966081 = 0 := by
    have hm : equation 6 1 6 0 = 1966081 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot21 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2949122 = 0 := by
  have h0 : value x 2949122 = 0 := by
    have hm : equation 6 1 6 1 = 2949122 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot22 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4653060 = 0 := by
  have h0 : value x 4653060 = 0 := by
    have hm : equation 6 1 6 2 = 4653060 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot23 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9109512 = 0 := by
  have h0 : value x 9109512 = 0 := by
    have hm : equation 6 1 6 3 = 9109512 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot24 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 503319820 = 0 := by
  have h0 : value x 79454231642563798721986822145 = 0 := by
    have hm : equation 6 1 8 0 = 79454231642563798721986822145 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot7 x h)

private theorem pivot25 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 754978316 = 0 := by
  have h0 : value x 633976415841616069541601738754 = 0 := by
    have hm : equation 6 1 8 1 = 633976415841616069541601738754 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot4 x h)) (pivot7 x h)

private theorem pivot26 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1191185167 = 0 := by
  have h0 : value x 158724706560546173328566517764 = 0 := by
    have hm : equation 6 1 8 2 = 158724706560546173328566517764 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (h0) (pivot6 x h)) (pivot7 x h)

private theorem pivot27 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2332034831 = 0 := by
  have h0 : value x 317191911921446876648459730952 = 0 := by
    have hm : equation 6 1 8 3 = 317191911921446876648459730952 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (h0) (pivot4 x h)) (pivot6 x h)

private theorem pivot28 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4295020588 = 0 := by
  have h0 : value x 2166395068751385810205409281 = 0 := by
    have hm : equation 6 1 9 0 = 2166395068751385810205409281 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot11 x h)) (pivot10 x h)) (pivot8 x h)

private theorem pivot29 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 8589991964 = 0 := by
  have h0 : value x 4332790137501927195480686594 = 0 := by
    have hm : equation 6 1 9 1 = 4332790137501927195480686594 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot9 x h)) (pivot11 x h)) (pivot10 x h)

private theorem pivot30 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 17179914383 = 0 := by
  have h0 : value x 4023305127681426560275972100 = 0 := by
    have hm : equation 6 1 9 2 = 4023305127681426560275972100 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot9 x h)) (pivot11 x h)) (pivot8 x h)

private theorem pivot31 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 34359767119 = 0 := by
  have h0 : value x 3404335108038454965029568520 = 0 := by
    have hm : equation 6 1 9 3 = 3404335108038454965029568520 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot9 x h)) (pivot10 x h)) (pivot8 x h)

private theorem pivot32 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 15716035704530324928073227 = 0 := by
  have h0 : value x 634579669825554510828344983665 = 0 := by
    have hm : equation 6 1 12 0 = 634579669825554510828344983665 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot4 x h)) (pivot7 x h)) (pivot10 x h)

private theorem pivot33 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 8462480795849336817714957 = 0 := by
  have h0 : value x 318421389479936970534162563250 = 0 := by
    have hm : equation 6 1 12 1 = 318421389479936970534162563250 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot4 x h)) (pivot6 x h)) (pivot11 x h)

private theorem pivot34 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 3626777481362504136262917 = 0 := by
  have h0 : value x 159017266608830989024058413284 = 0 := by
    have hm : equation 6 1 12 2 = 159017266608830989024058413284 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot6 x h)) (pivot7 x h)) (pivot8 x h)) (pivot32 x h)

private theorem pivot35 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1208925824119190874752001 = 0 := by
  have h0 : value x 81916813537089524677904179416 = 0 := by
    have hm : equation 6 1 12 3 = 81916813537089524677904179416 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot7 x h)) (pivot9 x h)) (pivot32 x h)) (pivot33 x h)

private theorem pivot36 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 75732161897955340 = 0 := by
  have h0 : value x 874933465578128416338952089665 = 0 := by
    have hm : equation 6 1 14 0 = 874933465578128416338952089665 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot4 x h)) (pivot6 x h)) (pivot7 x h)) (pivot9 x h)) (pivot10 x h)) (pivot8 x h)) (pivot32 x h)) (pivot33 x h)) (pivot34 x h)) (pivot35 x h)

private theorem pivot37 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 148070131400966156 = 0 := by
  have h0 : value x 558775185232582651064319258754 = 0 := by
    have hm : equation 6 1 14 1 = 558775185232582651064319258754 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot4 x h)) (pivot9 x h)) (pivot11 x h)) (pivot8 x h)) (pivot34 x h)) (pivot35 x h)

private theorem pivot38 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 291334297476923407 = 0 := by
  have h0 : value x 1034337588449451125884542050324 = 0 := by
    have hm : equation 6 1 14 2 = 1034337588449451125884542050324 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot6 x h)) (pivot9 x h)) (pivot11 x h)) (pivot10 x h)) (pivot35 x h)

private theorem pivot39 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 578443171768303631 = 0 := by
  have h0 : value x 1111438041521481950904801349672 = 0 := by
    have hm : equation 6 1 14 3 = 1111438041521481950904801349672 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot11 x h)) (pivot10 x h)) (pivot8 x h)) (pivot33 x h)) (pivot34 x h)

private theorem pivot40 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1211468437201616908 = 0 := by
  have h0 : value x 8462481890223908829792001 = 0 := by
    have hm : equation 6 1 15 0 = 8462481890223908829792001 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot33 x h)

private theorem pivot41 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2368893472716357644 = 0 := by
  have h0 : value x 16924963780447817659583234 = 0 := by
    have hm : equation 6 1 15 1 = 16924963780447817659583234 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (h0) (pivot32 x h)) (pivot34 x h)

private theorem pivot42 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4661226164084277263 = 0 := by
  have h0 : value x 15716040266676197698571780 = 0 := by
    have hm : equation 6 1 15 2 = 15716040266676197698571780 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot32 x h)

private theorem pivot43 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9254897509124276239 = 0 := by
  have h0 : value x 13298193239132957776547080 = 0 := by
    have hm : equation 6 1 15 3 = 13298193239132957776547080 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot32 x h)) (pivot33 x h)) (pivot35 x h)

private theorem pivot44 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 15 = 0 := by
  have h0 : value x 54469437286424398676738703361 = 0 := by
    have hm : equation 6 1 18 0 = 54469437286424398676738703361 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot0 x h)) (pivot2 x h)) (pivot9 x h)) (pivot11 x h)) (pivot8 x h)) (pivot34 x h)) (pivot35 x h)) (pivot13 x h)) (pivot14 x h)) (pivot15 x h)) (pivot19 x h)) (pivot37 x h)) (pivot30 x h)

private theorem pivot45 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 218103824 = 0 := by
  have h0 : value x 218103824 = 0 := by
    have hm : equation 6 3 1 0 = 218103824 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot46 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 50331696 = 0 := by
  have h0 : value x 234881056 = 0 := by
    have hm : equation 6 3 1 1 = 234881056 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot45 x h)

private theorem pivot47 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 100663376 = 0 := by
  have h0 : value x 184549440 = 0 := by
    have hm : equation 6 3 1 2 = 184549440 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot45 x h)

private theorem pivot48 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 16777424 = 0 := by
  have h0 : value x 117440640 = 0 := by
    have hm : equation 6 3 1 3 = 117440640 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot47 x h)

private theorem pivot49 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 252 = 0 := by
  have h0 : value x 55834578960 = 0 := by
    have hm : equation 6 3 2 0 = 55834578960 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot31 x h)) (pivot30 x h)) (pivot28 x h)

private theorem pivot50 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 63 = 0 := by
  have h0 : value x 47244656704 = 0 := by
    have hm : equation 6 3 2 2 = 47244656704 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot31 x h)) (pivot29 x h)) (pivot28 x h)

private theorem pivot51 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 851984 = 0 := by
  have h0 : value x 851984 = 0 := by
    have hm : equation 6 3 4 0 = 851984 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot52 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 196656 = 0 := by
  have h0 : value x 917536 = 0 := by
    have hm : equation 6 3 4 1 = 917536 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot51 x h)

private theorem pivot53 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 393296 = 0 := by
  have h0 : value x 720960 = 0 := by
    have hm : equation 6 3 4 2 = 720960 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot51 x h)

private theorem pivot54 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 65744 = 0 := by
  have h0 : value x 458880 = 0 := by
    have hm : equation 6 3 4 3 = 458880 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot53 x h)

private theorem pivot55 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 68719476752 = 0 := by
  have h0 : value x 68719476752 = 0 := by
    have hm : equation 6 3 6 0 = 68719476752 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot56 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 137438953504 = 0 := by
  have h0 : value x 137438953504 = 0 := by
    have hm : equation 6 3 6 1 = 137438953504 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot57 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 274877907008 = 0 := by
  have h0 : value x 274877907008 = 0 := by
    have hm : equation 6 3 6 2 = 274877907008 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot58 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 549755814016 = 0 := by
  have h0 : value x 549755814016 = 0 := by
    have hm : equation 6 3 6 3 = 549755814016 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot59 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 14293651161104 = 0 := by
  have h0 : value x 14293651161104 = 0 := by
    have hm : equation 6 3 7 0 = 14293651161104 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot60 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 3298534883376 = 0 := by
  have h0 : value x 15393162788896 = 0 := by
    have hm : equation 6 3 7 1 = 15393162788896 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot59 x h)

private theorem pivot61 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 6597069766736 = 0 := by
  have h0 : value x 12094627905600 = 0 := by
    have hm : equation 6 3 7 2 = 12094627905600 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot59 x h)

private theorem pivot62 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1099511627984 = 0 := by
  have h0 : value x 7696581394560 = 0 := by
    have hm : equation 6 3 7 3 = 7696581394560 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot61 x h)

private theorem pivot63 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 228698418577424 = 0 := by
  have h0 : value x 228698418577424 = 0 := by
    have hm : equation 6 3 8 0 = 228698418577424 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot64 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 52776558133296 = 0 := by
  have h0 : value x 246290604621856 = 0 := by
    have hm : equation 6 3 8 1 = 246290604621856 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot63 x h)

private theorem pivot65 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 105553116266576 = 0 := by
  have h0 : value x 193514046488640 = 0 := by
    have hm : equation 6 3 8 2 = 193514046488640 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot63 x h)

private theorem pivot66 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 17592186044624 = 0 := by
  have h0 : value x 123145302311040 = 0 := by
    have hm : equation 6 3 8 3 = 123145302311040 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot65 x h)

private theorem pivot67 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 3 = 0 := by
  have h0 : value x 17592186044432 = 0 := by
    have hm : equation 6 3 9 0 = 17592186044432 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot66 x h)) (pivot49 x h)) (pivot50 x h)

private theorem pivot68 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 531266230448735110824421 = 0 := by
  have h0 : value x 310016276050667903928766724 = 0 := by
    have hm : equation 6 4 1 0 = 310016276050667903928766724 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot8 x h)

private theorem pivot69 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 831726799047216311829200 = 0 := by
  have h0 : value x 2476711805367555966296400386 = 0 := by
    have hm : equation 6 4 1 1 = 2476711805367555966296400386 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot9 x h)

private theorem pivot70 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 154362358067976292271945 = 0 := by
  have h0 : value x 620028124882758117548377096 = 0 := by
    have hm : equation 6 4 1 2 = 620028124882758117548377096 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot10 x h)) (pivot69 x h)) (pivot68 x h)

private theorem pivot71 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 79689938339074970487692 = 0 := by
  have h0 : value x 1238923472105437878699460609 = 0 := by
    have hm : equation 6 4 1 3 = 1238923472105437878699460609 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot11 x h)) (pivot69 x h)) (pivot68 x h)

private theorem pivot72 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 58546962659542540 = 0 := by
  have h0 : value x 8462480737302434287714561 = 0 := by
    have hm : equation 6 4 2 0 = 8462480737302434287714561 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot33 x h)

private theorem pivot73 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 31525532399046405 = 0 := by
  have h0 : value x 13298184015760981051310594 = 0 := by
    have hm : equation 6 4 2 1 = 13298184015760981051310594 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot32 x h)) (pivot33 x h)) (pivot35 x h)

private theorem pivot74 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 13511047990216966 = 0 := by
  have h0 : value x 16924961474604864280462340 = 0 := by
    have hm : equation 6 4 2 2 = 16924961474604864280462340 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot32 x h)) (pivot34 x h)) (pivot72 x h)

private theorem pivot75 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4504570289983242 = 0 := by
  have h0 : value x 15716035654990226515822600 = 0 := by
    have hm : equation 6 4 2 3 = 15716035654990226515822600 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot32 x h)) (pivot72 x h)) (pivot73 x h)

private theorem pivot76 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2316 = 0 := by
  have h0 : value x 54469380618022663577631982720 = 0 := by
    have hm : equation 6 4 3 2 = 54469380618022663577631982720 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot0 x h)) (pivot2 x h)) (pivot9 x h)) (pivot11 x h)) (pivot8 x h)) (pivot34 x h)) (pivot35 x h)) (pivot71 x h)) (pivot19 x h)) (pivot43 x h)) (pivot41 x h)) (pivot40 x h)) (pivot37 x h)) (pivot73 x h)) (pivot74 x h)) (pivot30 x h)) (pivot27 x h)) (pivot26 x h)) (pivot24 x h)

private theorem pivot77 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 39932330983650281627517204 = 0 := by
  have h0 : value x 1029966150464368251673233523984 = 0 := by
    have hm : equation 6 4 4 0 = 1029966150464368251673233523984 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot6 x h)

private theorem pivot78 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 82216400502790076104573474 = 0 := by
  have h0 : value x 1109194284644433692048906649632 = 0 := by
    have hm : equation 6 4 4 1 = 1109194284644433692048906649632 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot5 x h)

private theorem pivot79 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 29018942046242062446953544 = 0 := by
  have h0 : value x 871509792379274196398629522496 = 0 := by
    have hm : equation 6 4 4 2 = 871509792379274196398629522496 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot5 x h)) (pivot4 x h)) (pivot6 x h)) (pivot7 x h)

private theorem pivot80 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 157179246033848150839199873 = 0 := by
  have h0 : value x 554597156489316294633389230464 = 0 := by
    have hm : equation 6 4 4 3 = 554597156489316294633389230464 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (h0) (pivot4 x h)

private theorem pivot81 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 281474976973056 = 0 := by
  have h0 : value x 281474976973056 = 0 := by
    have hm : equation 6 4 6 0 = 281474976973056 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot82 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 562949953552896 = 0 := by
  have h0 : value x 562949953552896 = 0 := by
    have hm : equation 6 4 6 1 = 562949953552896 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot83 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1125899907367936 = 0 := by
  have h0 : value x 1125899907367936 = 0 := by
    have hm : equation 6 4 6 2 = 1125899907367936 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot84 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2251799813752832 = 0 := by
  have h0 : value x 2251799813752832 = 0 := by
    have hm : equation 6 4 6 3 = 2251799813752832 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact h0

private theorem pivot85 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 6 = 0 := by
  have h0 : value x 9825768920348427345199616 = 0 := by
    have hm : equation 6 4 7 1 = 9825768920348427345199616 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot32 x h)) (pivot33 x h)) (pivot34 x h)) (pivot35 x h)) (pivot70 x h)) (pivot84 x h)) (pivot83 x h)) (pivot81 x h)) (pivot59 x h)) (pivot60 x h)) (pivot58 x h)) (pivot57 x h)) (pivot55 x h)) (pivot47 x h)) (pivot46 x h)) (pivot48 x h)) (pivot21 x h)) (pivot44 x h)

private theorem pivot86 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 3262849046869393083715 = 0 := by
  have h0 : value x 29014219742931839600296192 = 0 := by
    have hm : equation 6 4 8 0 = 29014219742931839600296192 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (h0) (pivot79 x h)) (pivot15 x h)

private theorem pivot87 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1481747486816646596300 = 0 := by
  have h0 : value x 157160356694263271425835520 = 0 := by
    have hm : equation 6 4 8 1 = 157160356694263271425835520 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot80 x h)) (pivot13 x h)) (pivot14 x h)) (pivot15 x h)) (pivot86 x h)

private theorem pivot88 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 600055181395074549727 = 0 := by
  have h0 : value x 39894552335741837469811712 = 0 := by
    have hm : equation 6 4 8 2 = 39894552335741837469811712 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot77 x h)) (pivot12 x h)) (pivot14 x h)) (pivot87 x h)

private theorem pivot89 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 300745897658334577791 = 0 := by
  have h0 : value x 82206956310449050246711296 = 0 := by
    have hm : equation 6 4 8 3 = 82206956310449050246711296 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot78 x h)) (pivot14 x h)) (pivot15 x h)) (pivot86 x h)) (pivot87 x h)) (pivot88 x h)

private theorem pivot90 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 34751 = 0 := by
  have h0 : value x 1152921504606847232 = 0 := by
    have hm : equation 6 4 9 0 = 1152921504606847232 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot40 x h)) (pivot72 x h)) (pivot30 x h)) (pivot29 x h)) (pivot28 x h)

private theorem pivot91 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 7658 = 0 := by
  have h0 : value x 2305843009213694464 = 0 := by
    have hm : equation 6 4 9 1 = 2305843009213694464 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot41 x h)) (pivot72 x h)) (pivot74 x h)) (pivot31 x h)) (pivot30 x h)) (pivot28 x h)

private theorem pivot92 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 17011 = 0 := by
  have h0 : value x 4611686018427388928 = 0 := by
    have hm : equation 6 4 9 2 = 4611686018427388928 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot42 x h)) (pivot72 x h)) (pivot73 x h)) (pivot75 x h)) (pivot31 x h)) (pivot29 x h)) (pivot28 x h)

private theorem pivot93 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 10198 = 0 := by
  have h0 : value x 9223372036854777856 = 0 := by
    have hm : equation 6 4 9 3 = 9223372036854777856 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot43 x h)) (pivot73 x h)) (pivot31 x h)) (pivot30 x h)) (pivot29 x h)

private theorem pivot94 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1430 = 0 := by
  have h0 : value x 39865537827613137633737179392 = 0 := by
    have hm : equation 6 4 18 0 = 39865537827613137633737179392 := by decide +kernel
    rw [← hm]
    exact equation_zero x h _ _ _ _
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (h0) (pivot0 x h)) (pivot2 x h)) (pivot1 x h)) (pivot8 x h)) (pivot80 x h)) (pivot78 x h)) (pivot79 x h)) (pivot68 x h)) (pivot17 x h)) (pivot18 x h)) (pivot19 x h)) (pivot41 x h)) (pivot39 x h)) (pivot37 x h)) (pivot36 x h)) (pivot72 x h)) (pivot74 x h)) (pivot83 x h)) (pivot55 x h)) (pivot31 x h)) (pivot30 x h)) (pivot28 x h)) (pivot47 x h)) (pivot48 x h)

private theorem reduced1 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 3 = 0 := by
  exact pivot67 x h

private theorem reduced2 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 5 = 0 := by
  exact value_xor_zero x (pivot85 x h) (reduced1 x h)

private theorem reduced3 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot44 x h) (reduced1 x h)) (reduced2 x h)

private theorem reduced5 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 48 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot50 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)

private theorem reduced7 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 192 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot49 x h) (reduced2 x h)) (reduced3 x h)) (reduced5 x h)

private theorem reduced10 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1360 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot94 x h) (reduced1 x h)) (reduced2 x h)) (reduced7 x h)

private theorem reduced11 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2304 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot76 x h) (reduced2 x h)) (reduced3 x h)

private theorem reduced12 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4416 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot91 x h) (reduced1 x h)) (reduced3 x h)) (reduced5 x h)) (reduced7 x h)) (reduced10 x h)) (reduced11 x h)

private theorem reduced13 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 8768 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot93 x h) (reduced1 x h)) (reduced2 x h)) (reduced7 x h)) (reduced10 x h)

private theorem reduced14 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 16960 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot92 x h) (reduced1 x h)) (reduced5 x h)

private theorem reduced15 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 33296 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot90 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced5 x h)) (reduced7 x h)) (reduced10 x h)

private theorem reduced16 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 65552 = 0 := by
  exact value_xor_zero x (pivot54 x h) (reduced7 x h)

private theorem reduced17 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 131088 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot52 x h) (reduced5 x h)) (reduced16 x h)

private theorem reduced18 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 262208 = 0 := by
  exact value_xor_zero x (pivot53 x h) (reduced17 x h)

private theorem reduced19 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 524352 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot51 x h) (reduced16 x h)) (reduced18 x h)

private theorem reduced20 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1048593 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot20 x h) (reduced17 x h)) (reduced18 x h)) (reduced19 x h)

private theorem reduced21 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2097169 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot21 x h) (reduced1 x h)) (reduced16 x h)) (reduced18 x h)) (reduced19 x h)

private theorem reduced22 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4194369 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot22 x h) (reduced2 x h)) (reduced16 x h)) (reduced17 x h)) (reduced18 x h)

private theorem reduced23 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 8388673 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot23 x h) (reduced3 x h)) (reduced16 x h)) (reduced17 x h)) (reduced19 x h)

private theorem reduced24 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 16777232 = 0 := by
  exact value_xor_zero x (pivot48 x h) (reduced7 x h)

private theorem reduced25 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 33554448 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot46 x h) (reduced5 x h)) (reduced24 x h)

private theorem reduced26 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 67108928 = 0 := by
  exact value_xor_zero x (pivot47 x h) (reduced25 x h)

private theorem reduced27 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 134217792 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot45 x h) (reduced24 x h)) (reduced26 x h)

private theorem reduced28 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 268435776 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot24 x h) (reduced2 x h)) (reduced3 x h)) (reduced10 x h)) (reduced11 x h)) (reduced25 x h)) (reduced26 x h)) (reduced27 x h)

private theorem reduced29 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 536871488 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot25 x h) (reduced2 x h)) (reduced3 x h)) (reduced10 x h)) (reduced11 x h)) (reduced24 x h)) (reduced26 x h)) (reduced27 x h)

private theorem reduced30 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1073742400 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot26 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced11 x h)) (reduced24 x h)) (reduced25 x h)) (reduced26 x h)

private theorem reduced31 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2147484176 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot27 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced10 x h)) (reduced24 x h)) (reduced25 x h)) (reduced27 x h)

private theorem reduced32 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4294967552 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot28 x h) (reduced2 x h)) (reduced3 x h)) (reduced5 x h)) (reduced12 x h)) (reduced14 x h)) (reduced15 x h)

private theorem reduced33 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 8589935104 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot29 x h) (reduced2 x h)) (reduced3 x h)) (reduced13 x h)) (reduced14 x h)) (reduced15 x h)

private theorem reduced34 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 17179869520 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot30 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced7 x h)) (reduced12 x h)) (reduced13 x h)) (reduced15 x h)

private theorem reduced35 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 34359738624 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot31 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced12 x h)) (reduced13 x h)) (reduced14 x h)

private theorem reduced36 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 68719476752 = 0 := by
  exact pivot55 x h

private theorem reduced37 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 137438953488 = 0 := by
  exact value_xor_zero x (pivot56 x h) (reduced5 x h)

private theorem reduced38 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 274877907008 = 0 := by
  exact pivot57 x h

private theorem reduced39 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 549755813952 = 0 := by
  exact value_xor_zero x (pivot58 x h) (reduced7 x h)

private theorem reduced40 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1099511627792 = 0 := by
  exact value_xor_zero x (pivot62 x h) (reduced7 x h)

private theorem reduced41 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2199023255568 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot60 x h) (reduced5 x h)) (reduced40 x h)

private theorem reduced42 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4398046511168 = 0 := by
  exact value_xor_zero x (pivot61 x h) (reduced41 x h)

private theorem reduced43 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 8796093022272 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot59 x h) (reduced40 x h)) (reduced42 x h)

private theorem reduced44 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 17592186044432 = 0 := by
  exact value_xor_zero x (pivot66 x h) (reduced7 x h)

private theorem reduced45 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 35184372088848 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot64 x h) (reduced5 x h)) (reduced44 x h)

private theorem reduced46 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 70368744177728 = 0 := by
  exact value_xor_zero x (pivot65 x h) (reduced45 x h)

private theorem reduced47 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 140737488355392 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot63 x h) (reduced44 x h)) (reduced46 x h)

private theorem reduced48 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 281474976710976 = 0 := by
  exact value_xor_zero x (pivot81 x h) (reduced18 x h)

private theorem reduced49 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 562949953421840 = 0 := by
  exact value_xor_zero x (pivot82 x h) (reduced17 x h)

private theorem reduced50 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1125899906842896 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot83 x h) (reduced10 x h)) (reduced19 x h)

private theorem reduced51 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2251799813685520 = 0 := by
  exact value_xor_zero x (value_xor_zero x (pivot84 x h) (reduced11 x h)) (reduced16 x h)

private theorem reduced52 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4503599627370816 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot75 x h) (reduced1 x h)) (reduced3 x h)) (reduced10 x h)) (reduced11 x h)) (reduced33 x h)) (reduced37 x h)) (reduced38 x h)) (reduced39 x h)

private theorem reduced53 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9007199254741568 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot74 x h) (reduced1 x h)) (reduced2 x h)) (reduced11 x h)) (reduced33 x h)) (reduced35 x h)) (reduced36 x h)) (reduced37 x h)) (reduced52 x h)

private theorem reduced54 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 18014398509482560 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot73 x h) (reduced2 x h)) (reduced10 x h)) (reduced11 x h)) (reduced33 x h)) (reduced34 x h)) (reduced35 x h)) (reduced38 x h)) (reduced52 x h)) (reduced53 x h)

private theorem reduced55 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 36028797018964496 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot72 x h) (reduced2 x h)) (reduced3 x h)) (reduced10 x h)) (reduced32 x h)) (reduced33 x h)) (reduced34 x h)) (reduced37 x h)) (reduced52 x h)) (reduced54 x h)

private theorem reduced56 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 72057594037928272 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot36 x h) (reduced2 x h)) (reduced3 x h)) (reduced41 x h)) (reduced42 x h)) (reduced43 x h)) (reduced48 x h)) (reduced50 x h)) (reduced51 x h)

private theorem reduced57 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 144115188075856384 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot37 x h) (reduced2 x h)) (reduced3 x h)) (reduced40 x h)) (reduced42 x h)) (reduced43 x h)) (reduced49 x h)) (reduced50 x h)) (reduced51 x h)

private theorem reduced58 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 288230376151712256 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot38 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced40 x h)) (reduced41 x h)) (reduced42 x h)) (reduced48 x h)) (reduced49 x h)) (reduced51 x h)

private theorem reduced59 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 576460752303424000 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot39 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced40 x h)) (reduced41 x h)) (reduced43 x h)) (reduced48 x h)) (reduced49 x h)) (reduced50 x h)

private theorem reduced60 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1152921504606847232 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot40 x h) (reduced2 x h)) (reduced3 x h)) (reduced37 x h)) (reduced52 x h)) (reduced54 x h)) (reduced55 x h)

private theorem reduced61 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2305843009213694464 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot41 x h) (reduced2 x h)) (reduced3 x h)) (reduced36 x h)) (reduced53 x h)) (reduced54 x h)) (reduced55 x h)

private theorem reduced62 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4611686018427388240 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot42 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced39 x h)) (reduced52 x h)) (reduced53 x h)) (reduced55 x h)

private theorem reduced63 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9223372036854776064 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot43 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced38 x h)) (reduced52 x h)) (reduced53 x h)) (reduced54 x h)

private theorem reduced64 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 18446744073709551632 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot19 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced36 x h)) (reduced37 x h)) (reduced38 x h)) (reduced40 x h)) (reduced42 x h)) (reduced43 x h)) (reduced45 x h)) (reduced46 x h)) (reduced47 x h)) (reduced49 x h)) (reduced50 x h)) (reduced51 x h)) (reduced54 x h)) (reduced57 x h)) (reduced60 x h)) (reduced61 x h)) (reduced63 x h)

private theorem reduced65 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 36893488147419103248 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot16 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced37 x h)) (reduced38 x h)) (reduced39 x h)) (reduced40 x h)) (reduced41 x h)) (reduced42 x h)) (reduced44 x h)) (reduced46 x h)) (reduced47 x h)) (reduced48 x h)) (reduced49 x h)) (reduced51 x h)) (reduced52 x h)) (reduced58 x h)) (reduced60 x h)) (reduced62 x h)) (reduced63 x h)

private theorem reduced66 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 73786976294838206528 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot18 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced36 x h)) (reduced38 x h)) (reduced39 x h)) (reduced41 x h)) (reduced42 x h)) (reduced43 x h)) (reduced44 x h)) (reduced45 x h)) (reduced46 x h)) (reduced48 x h)) (reduced50 x h)) (reduced51 x h)) (reduced53 x h)) (reduced56 x h)) (reduced61 x h)) (reduced62 x h)) (reduced63 x h)

private theorem reduced67 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 147573952589676412992 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot17 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced36 x h)) (reduced37 x h)) (reduced39 x h)) (reduced40 x h)) (reduced41 x h)) (reduced43 x h)) (reduced44 x h)) (reduced45 x h)) (reduced47 x h)) (reduced48 x h)) (reduced49 x h)) (reduced50 x h)) (reduced55 x h)) (reduced59 x h)) (reduced60 x h)) (reduced61 x h)) (reduced62 x h)

private theorem reduced68 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 295147905179352825856 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot89 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced5 x h)) (reduced10 x h)) (reduced18 x h)) (reduced24 x h)) (reduced26 x h)) (reduced27 x h)) (reduced39 x h)) (reduced44 x h)) (reduced52 x h)) (reduced53 x h)) (reduced55 x h)) (reduced56 x h)) (reduced58 x h)) (reduced59 x h)) (reduced62 x h)

private theorem reduced69 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 590295810358705652560 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot88 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced7 x h)) (reduced10 x h)) (reduced16 x h)) (reduced25 x h)) (reduced26 x h)) (reduced27 x h)) (reduced38 x h)) (reduced46 x h)) (reduced52 x h)) (reduced53 x h)) (reduced54 x h)) (reduced56 x h)) (reduced57 x h)) (reduced58 x h)) (reduced63 x h)

private theorem reduced70 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1180591620717411303504 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot87 x h) (reduced2 x h)) (reduced3 x h)) (reduced7 x h)) (reduced10 x h)) (reduced17 x h)) (reduced18 x h)) (reduced25 x h)) (reduced26 x h)) (reduced37 x h)) (reduced39 x h)) (reduced44 x h)) (reduced47 x h)) (reduced53 x h)) (reduced54 x h)) (reduced56 x h)) (reduced57 x h)) (reduced60 x h)) (reduced62 x h)) (reduced68 x h)

private theorem reduced71 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2361183241434822607616 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot86 x h) (reduced1 x h)) (reduced10 x h)) (reduced11 x h)) (reduced16 x h)) (reduced18 x h)) (reduced19 x h)) (reduced26 x h)) (reduced36 x h)) (reduced38 x h)) (reduced39 x h)) (reduced44 x h)) (reduced45 x h)) (reduced46 x h)) (reduced53 x h)) (reduced56 x h)) (reduced61 x h)) (reduced62 x h)) (reduced63 x h)) (reduced68 x h)) (reduced69 x h)

private theorem reduced72 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4722366482869645214465 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot15 x h) (reduced1 x h)) (reduced3 x h)) (reduced11 x h)) (reduced61 x h)) (reduced62 x h)) (reduced63 x h)) (reduced68 x h)) (reduced69 x h)) (reduced71 x h)

private theorem reduced73 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9444732965739290428161 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot14 x h) (reduced1 x h)) (reduced2 x h)) (reduced11 x h)) (reduced60 x h)) (reduced63 x h)) (reduced69 x h)) (reduced70 x h)) (reduced72 x h)

private theorem reduced74 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 18889465931478580855553 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot13 x h) (reduced1 x h)) (reduced62 x h)) (reduced63 x h)) (reduced68 x h)) (reduced69 x h)) (reduced73 x h)

private theorem reduced75 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 37778931862957161710337 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot12 x h) (reduced10 x h)) (reduced11 x h)) (reduced62 x h)) (reduced68 x h)) (reduced72 x h)) (reduced73 x h)

private theorem reduced76 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 75557863725914323419200 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot71 x h) (reduced2 x h)) (reduced3 x h)) (reduced7 x h)) (reduced11 x h)) (reduced25 x h)) (reduced49 x h)) (reduced50 x h)) (reduced51 x h)) (reduced69 x h)) (reduced70 x h)) (reduced71 x h)

private theorem reduced77 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 151115727451828646839104 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot70 x h) (reduced3 x h)) (reduced10 x h)) (reduced26 x h)) (reduced48 x h)) (reduced50 x h)) (reduced51 x h)) (reduced68 x h)) (reduced69 x h)) (reduced71 x h)

private theorem reduced78 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 302231454903657293676608 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot68 x h) (reduced2 x h)) (reduced5 x h)) (reduced7 x h)) (reduced24 x h)) (reduced25 x h)) (reduced26 x h)) (reduced50 x h)) (reduced71 x h)) (reduced76 x h)) (reduced77 x h)

private theorem reduced79 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 604462909807314587353920 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot69 x h) (reduced7 x h)) (reduced25 x h)) (reduced26 x h)) (reduced27 x h)) (reduced51 x h)) (reduced69 x h)) (reduced76 x h)) (reduced77 x h)

private theorem reduced80 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1208925819614629174706177 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot35 x h) (reduced10 x h)) (reduced37 x h)) (reduced38 x h)) (reduced39 x h)) (reduced52 x h)

private theorem reduced81 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2417851639229258349413121 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot34 x h) (reduced2 x h)) (reduced10 x h)) (reduced36 x h)) (reduced39 x h)) (reduced52 x h)) (reduced54 x h)) (reduced80 x h)

private theorem reduced82 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4835703278458516698824785 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot33 x h) (reduced2 x h)) (reduced3 x h)) (reduced10 x h)) (reduced37 x h)) (reduced52 x h)) (reduced54 x h)) (reduced55 x h)) (reduced80 x h)) (reduced81 x h)

private theorem reduced83 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9671406556917033397650257 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot32 x h) (reduced1 x h)) (reduced3 x h)) (reduced10 x h)) (reduced11 x h)) (reduced39 x h)) (reduced52 x h)) (reduced53 x h)) (reduced55 x h)) (reduced80 x h)) (reduced82 x h)

private theorem reduced84 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 19342813113834066795299585 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot79 x h) (reduced3 x h)) (reduced10 x h)) (reduced16 x h)) (reduced18 x h)) (reduced19 x h)) (reduced36 x h)) (reduced38 x h)) (reduced39 x h)) (reduced53 x h)) (reduced72 x h)) (reduced83 x h)

private theorem reduced85 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 38685626227668133590598401 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot77 x h) (reduced2 x h)) (reduced16 x h)) (reduced17 x h)) (reduced18 x h)) (reduced37 x h)) (reduced38 x h)) (reduced39 x h)) (reduced52 x h)) (reduced75 x h)) (reduced80 x h)

private theorem reduced86 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 77371252455336267181196033 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot78 x h) (reduced1 x h)) (reduced5 x h)) (reduced17 x h)) (reduced18 x h)) (reduced19 x h)) (reduced36 x h)) (reduced37 x h)) (reduced39 x h)) (reduced55 x h)) (reduced73 x h)) (reduced82 x h)

private theorem reduced87 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 154742504910672534362391297 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot80 x h) (reduced7 x h)) (reduced11 x h)) (reduced16 x h)) (reduced17 x h)) (reduced19 x h)) (reduced36 x h)) (reduced37 x h)) (reduced38 x h)) (reduced54 x h)) (reduced74 x h)) (reduced81 x h)

private theorem reduced88 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 309485009821345068724781121 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot8 x h) (reduced5 x h)) (reduced7 x h)) (reduced12 x h)) (reduced50 x h)

private theorem reduced89 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 618970019642690137449562945 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot10 x h) (reduced2 x h)) (reduced5 x h)) (reduced14 x h)) (reduced48 x h)

private theorem reduced90 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 1237940039285380274899124289 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot11 x h) (reduced3 x h)) (reduced5 x h)) (reduced7 x h)) (reduced15 x h)) (reduced49 x h)

private theorem reduced91 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 2475880078570760549798249281 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot9 x h) (reduced1 x h)) (reduced7 x h)) (reduced13 x h)) (reduced51 x h)

private theorem reduced92 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 4951760157141521099596497665 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot3 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced46 x h)) (reduced64 x h)) (reduced65 x h)) (reduced66 x h)) (reduced69 x h)) (reduced72 x h)) (reduced74 x h)) (reduced75 x h)) (reduced76 x h)) (reduced77 x h)) (reduced79 x h)) (reduced80 x h)) (reduced81 x h)) (reduced83 x h)) (reduced91 x h)

private theorem reduced93 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 9903520314283042199192994561 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot1 x h) (reduced46 x h)) (reduced47 x h)) (reduced66 x h)) (reduced67 x h)) (reduced69 x h)) (reduced70 x h)) (reduced72 x h)) (reduced73 x h)) (reduced77 x h)) (reduced78 x h)) (reduced82 x h)) (reduced83 x h)) (reduced90 x h)) (reduced91 x h)) (reduced92 x h)

private theorem reduced94 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 19807040628566084398385988353 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot2 x h) (reduced2 x h)) (reduced3 x h)) (reduced44 x h)) (reduced47 x h)) (reduced64 x h)) (reduced66 x h)) (reduced68 x h)) (reduced70 x h)) (reduced72 x h)) (reduced74 x h)) (reduced76 x h)) (reduced77 x h)) (reduced81 x h)) (reduced83 x h)) (reduced89 x h)) (reduced90 x h)) (reduced93 x h)

private theorem reduced95 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 39614081257132168796771975937 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot0 x h) (reduced1 x h)) (reduced2 x h)) (reduced3 x h)) (reduced44 x h)) (reduced45 x h)) (reduced46 x h)) (reduced66 x h)) (reduced68 x h)) (reduced69 x h)) (reduced71 x h)) (reduced72 x h)) (reduced77 x h)) (reduced83 x h)) (reduced88 x h)) (reduced89 x h)) (reduced91 x h)) (reduced92 x h)) (reduced94 x h)

private theorem reduced96 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 79228162514264337593543951105 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot7 x h) (reduced2 x h)) (reduced3 x h)) (reduced10 x h)) (reduced11 x h)) (reduced38 x h)) (reduced52 x h)) (reduced53 x h)) (reduced54 x h)) (reduced80 x h)) (reduced81 x h)) (reduced83 x h)) (reduced84 x h)) (reduced85 x h)) (reduced87 x h)

private theorem reduced97 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 158456325028528675187087901441 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot6 x h) (reduced1 x h)) (reduced2 x h)) (reduced10 x h)) (reduced36 x h)) (reduced38 x h)) (reduced52 x h)) (reduced55 x h)) (reduced80 x h)) (reduced82 x h)) (reduced85 x h)) (reduced86 x h)) (reduced96 x h)

private theorem reduced98 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 316912650057057350374175802113 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot4 x h) (reduced36 x h)) (reduced37 x h)) (reduced38 x h)) (reduced54 x h)) (reduced81 x h)) (reduced87 x h)) (reduced96 x h)) (reduced97 x h)

private theorem reduced99 (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    value x 633825300114114700748351603457 = 0 := by
  exact value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (value_xor_zero x (pivot5 x h) (reduced1 x h)) (reduced36 x h)) (reduced37 x h)) (reduced39 x h)) (reduced55 x h)) (reduced82 x h)) (reduced86 x h)) (reduced97 x h)) (reduced98 x h)

@[expose] public def freePositions : Fin 5 → Fin 100 := ![0, 4, 6, 8, 9]
@[expose] public def freeIndices : Fin 100 → List (Fin 5) := ![[0], [0], [0], [0], [1], [1], [2], [2], [3], [4], [1, 2, 3], [3], [2, 3], [2, 4], [2, 4], [1, 4], [1], [1], [2], [2], [0, 1], [0, 1], [0, 2], [0, 2], [1], [1], [2], [2], [2, 3], [2, 4], [2, 4], [1, 4], [3], [4], [1, 2, 3], [3], [1], [1], [2], [2], [1], [1], [2], [2], [1], [1], [2], [2], [2, 3], [1, 4], [1, 3], [1, 3], [2, 3], [2, 4], [2, 4], [1, 4], [1, 2, 3], [4], [4], [4], [3], [4], [1, 2, 3], [3], [1], [1], [2], [2], [], [1, 2, 3, 4], [1, 2], [3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [2], [2, 3, 4], [2], [2, 3, 4], [0], [0, 3, 4], [0, 1, 2], [0, 1, 2, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 2], [0, 2, 3, 4], [0, 2], [0, 2, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4], [0, 3, 4]]

@[expose] public def family (p : Fin 5 → ZMod 2) (k : Fin 100) : ZMod 2 :=
  ((freeIndices k).map p).sum

def freePoly (k : Fin 100) : Poly :=
  sumPoly ((freeIndices k).map (fun j => atom (freePositions j)))

set_option maxRecDepth 2048 in
private theorem allRelations (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    ∀ k, value x (atom k ^^^ freePoly k) = 0 := by
  intro k
  fin_cases k
  · exact value_zero x
  · exact reduced1 x h
  · exact reduced2 x h
  · exact reduced3 x h
  · exact value_zero x
  · exact reduced5 x h
  · exact value_zero x
  · exact reduced7 x h
  · exact value_zero x
  · exact value_zero x
  · exact reduced10 x h
  · exact reduced11 x h
  · exact reduced12 x h
  · exact reduced13 x h
  · exact reduced14 x h
  · exact reduced15 x h
  · exact reduced16 x h
  · exact reduced17 x h
  · exact reduced18 x h
  · exact reduced19 x h
  · exact reduced20 x h
  · exact reduced21 x h
  · exact reduced22 x h
  · exact reduced23 x h
  · exact reduced24 x h
  · exact reduced25 x h
  · exact reduced26 x h
  · exact reduced27 x h
  · exact reduced28 x h
  · exact reduced29 x h
  · exact reduced30 x h
  · exact reduced31 x h
  · exact reduced32 x h
  · exact reduced33 x h
  · exact reduced34 x h
  · exact reduced35 x h
  · exact reduced36 x h
  · exact reduced37 x h
  · exact reduced38 x h
  · exact reduced39 x h
  · exact reduced40 x h
  · exact reduced41 x h
  · exact reduced42 x h
  · exact reduced43 x h
  · exact reduced44 x h
  · exact reduced45 x h
  · exact reduced46 x h
  · exact reduced47 x h
  · exact reduced48 x h
  · exact reduced49 x h
  · exact reduced50 x h
  · exact reduced51 x h
  · exact reduced52 x h
  · exact reduced53 x h
  · exact reduced54 x h
  · exact reduced55 x h
  · exact reduced56 x h
  · exact reduced57 x h
  · exact reduced58 x h
  · exact reduced59 x h
  · exact reduced60 x h
  · exact reduced61 x h
  · exact reduced62 x h
  · exact reduced63 x h
  · exact reduced64 x h
  · exact reduced65 x h
  · exact reduced66 x h
  · exact reduced67 x h
  · exact reduced68 x h
  · exact reduced69 x h
  · exact reduced70 x h
  · exact reduced71 x h
  · exact reduced72 x h
  · exact reduced73 x h
  · exact reduced74 x h
  · exact reduced75 x h
  · exact reduced76 x h
  · exact reduced77 x h
  · exact reduced78 x h
  · exact reduced79 x h
  · exact reduced80 x h
  · exact reduced81 x h
  · exact reduced82 x h
  · exact reduced83 x h
  · exact reduced84 x h
  · exact reduced85 x h
  · exact reduced86 x h
  · exact reduced87 x h
  · exact reduced88 x h
  · exact reduced89 x h
  · exact reduced90 x h
  · exact reduced91 x h
  · exact reduced92 x h
  · exact reduced93 x h
  · exact reduced94 x h
  · exact reduced95 x h
  · exact reduced96 x h
  · exact reduced97 x h
  · exact reduced98 x h
  · exact reduced99 x h

public theorem coordinates_from_five (x : Fin 100 → ZMod 2) (h : IsCocycleTable x) :
    x = family (fun j => x (freePositions j)) := by
  funext k
  have hk := value_eq_of_xor_zero x (atom k) (freePoly k) (allRelations x h k)
  rw [value_atom, freePoly, value_sumPoly] at hk
  simp only [List.map_map, Function.comp_def, value_atom] at hk
  exact hk

end Theory.GroupTheory.HeldM22A10.NonsplitAlternatives.StandardExtensions.TwistedCohomology
