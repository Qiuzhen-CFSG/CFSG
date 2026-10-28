module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.EntryEquations

/-!
# Triangular elimination certificates for the four constant roots

Each pivot row is an explicit linear combination of one new commutator entry
and previously proved pivot rows. Characteristic-two ring normalization checks
these short certificates. Reusing the proved intermediate rows avoids expanding
a large certificate repeatedly. No external computation is trusted.

Source: the fixed-root matrices of GLS3 §2.4, checked in `Constants`.
-/

public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
variable {F : Type*} [CommRing F] [CharP F 2]

lemma pivot_17 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_0 A h

lemma pivot_9 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_5 A h

lemma pivot_11 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_7 A h

lemma pivot_4 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_8 A h

lemma pivot_6 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_10 A h

lemma pivot_1 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_18 A h + pivot_17 A h)

lemma pivot_26 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_22 A h

lemma pivot_27 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_23 A h

lemma pivot_20 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_24 A h

lemma pivot_21 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_25 A h

lemma pivot_504 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 17 + A 18 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_28 A h

lemma pivot_505 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_29 A h

lemma pivot_506 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 17 + A 18 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_30 A h

lemma pivot_507 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 17 + A 18 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_31 A h

lemma pivot_508 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_32 A h

lemma pivot_509 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 9 + A 18 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_33 A h

lemma pivot_510 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_34 A h

lemma pivot_511 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 11 + A 18 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_35 A h

lemma pivot_512 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 4 + A 18 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_36 A h

lemma pivot_513 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_37 A h

lemma pivot_514 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 6 + A 18 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_38 A h

lemma pivot_515 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_39 A h

lemma pivot_516 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_40 A h

lemma pivot_517 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_41 A h

lemma pivot_518 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_42 A h

lemma pivot_519 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_43 A h

lemma pivot_520 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_44 A h

lemma pivot_521 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_45 A h

lemma pivot_522 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 1 + A 1 17 + A 18 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_46 A h

lemma pivot_523 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_47 A h

lemma pivot_524 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_48 A h

lemma pivot_525 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_49 A h

lemma pivot_526 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 26 + A 18 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_50 A h

lemma pivot_527 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 27 + A 18 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_51 A h

lemma pivot_528 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 20 + A 18 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_52 A h

lemma pivot_529 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 21 + A 18 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_53 A h

lemma pivot_530 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_54 A h

lemma pivot_531 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_55 A h

lemma pivot_73 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_56 A h

lemma pivot_65 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_61 A h

lemma pivot_67 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_63 A h

lemma pivot_60 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_64 A h

lemma pivot_62 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_66 A h

lemma pivot_57 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_74 A h + pivot_73 A h)

lemma pivot_82 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_78 A h

lemma pivot_83 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_79 A h

lemma pivot_76 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_80 A h

lemma pivot_77 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_81 A h

lemma pivot_101 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_84 A h

lemma pivot_93 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_89 A h

lemma pivot_95 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_91 A h

lemma pivot_88 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_92 A h

lemma pivot_90 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_94 A h

lemma pivot_85 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_102 A h + pivot_101 A h)

lemma pivot_110 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_106 A h

lemma pivot_111 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_107 A h

lemma pivot_104 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_108 A h

lemma pivot_105 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_109 A h

lemma pivot_224 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 17 + A 8 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_112 A h

lemma pivot_225 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_113 A h

lemma pivot_226 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 17 + A 8 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_114 A h

lemma pivot_227 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 17 + A 8 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_115 A h

lemma pivot_228 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_116 A h

lemma pivot_229 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 9 + A 8 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_117 A h

lemma pivot_230 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_118 A h

lemma pivot_231 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 11 + A 8 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_119 A h

lemma pivot_232 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 4 + A 8 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_120 A h

lemma pivot_233 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_121 A h

lemma pivot_234 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 6 + A 8 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_122 A h

lemma pivot_235 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_123 A h

lemma pivot_236 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_124 A h

lemma pivot_237 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_125 A h

lemma pivot_238 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_126 A h

lemma pivot_239 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_127 A h

lemma pivot_240 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_128 A h

lemma pivot_241 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_129 A h

lemma pivot_242 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 1 + A 4 17 + A 8 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_130 A h

lemma pivot_243 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_131 A h

lemma pivot_244 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_132 A h

lemma pivot_245 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_133 A h

lemma pivot_246 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 26 + A 8 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_134 A h

lemma pivot_247 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 27 + A 8 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_135 A h

lemma pivot_248 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 20 + A 8 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_136 A h

lemma pivot_249 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 21 + A 8 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_137 A h

lemma pivot_250 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_138 A h

lemma pivot_251 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_139 A h

lemma pivot_157 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_140 A h

lemma pivot_149 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_145 A h

lemma pivot_151 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_147 A h

lemma pivot_144 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_148 A h

lemma pivot_146 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_150 A h

lemma pivot_141 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_158 A h + pivot_157 A h)

lemma pivot_166 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_162 A h

lemma pivot_167 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_163 A h

lemma pivot_160 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_164 A h

lemma pivot_161 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_165 A h

lemma pivot_280 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 17 + A 10 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_168 A h

lemma pivot_281 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_169 A h

lemma pivot_282 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 17 + A 10 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_170 A h

lemma pivot_283 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 17 + A 10 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_171 A h

lemma pivot_284 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_172 A h

lemma pivot_285 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 9 + A 10 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_173 A h

lemma pivot_286 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_174 A h

lemma pivot_287 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 11 + A 10 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_175 A h

lemma pivot_288 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 4 + A 10 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_176 A h

lemma pivot_289 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_177 A h

lemma pivot_290 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 6 + A 10 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_178 A h

lemma pivot_291 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_179 A h

lemma pivot_292 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_180 A h

lemma pivot_293 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_181 A h

lemma pivot_294 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_182 A h

lemma pivot_295 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_183 A h

lemma pivot_296 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_184 A h

lemma pivot_297 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_185 A h

lemma pivot_298 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 1 + A 6 17 + A 10 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_186 A h

lemma pivot_299 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_187 A h

lemma pivot_300 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_188 A h

lemma pivot_301 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_189 A h

lemma pivot_302 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 26 + A 10 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_190 A h

lemma pivot_303 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 27 + A 10 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_191 A h

lemma pivot_304 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 20 + A 10 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_192 A h

lemma pivot_305 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 21 + A 10 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_193 A h

lemma pivot_306 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_194 A h

lemma pivot_307 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_195 A h

lemma pivot_213 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_196 A h

lemma pivot_205 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_201 A h

lemma pivot_207 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_203 A h

lemma pivot_200 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_204 A h

lemma pivot_202 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_206 A h

lemma pivot_197 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_214 A h + pivot_213 A h)

lemma pivot_222 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_218 A h

lemma pivot_223 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_219 A h

lemma pivot_216 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_220 A h

lemma pivot_217 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_221 A h

lemma pivot_269 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 0 + A 9 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_252 A h

lemma pivot_142 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 0 + A 5 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_254 A h + pivot_269 A h)

lemma pivot_143 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 0 + A 5 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_255 A h + pivot_269 A h)

lemma pivot_261 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 5 + A 9 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_257 A h

lemma pivot_263 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 7 + A 9 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_259 A h

lemma pivot_256 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 8 + A 9 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_260 A h

lemma pivot_258 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 10 + A 9 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_262 A h

lemma pivot_152 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_264 A h

lemma pivot_153 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_265 A h

lemma pivot_154 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_266 A h

lemma pivot_155 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_267 A h

lemma pivot_156 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_268 A h

lemma pivot_253 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 0 + A 5 18 + A 9 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_270 A h + pivot_269 A h)

lemma pivot_159 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_271 A h

lemma pivot_278 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 22 + A 9 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_274 A h

lemma pivot_279 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 23 + A 9 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_275 A h

lemma pivot_272 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 24 + A 9 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_276 A h

lemma pivot_273 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 25 + A 9 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_277 A h

lemma pivot_325 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 + A 11 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_308 A h

lemma pivot_198 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 + A 7 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_310 A h + pivot_325 A h)

lemma pivot_199 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 + A 7 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_311 A h + pivot_325 A h)

lemma pivot_317 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 5 + A 11 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_313 A h

lemma pivot_319 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 7 + A 11 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_315 A h

lemma pivot_312 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 8 + A 11 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_316 A h

lemma pivot_314 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 10 + A 11 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_318 A h

lemma pivot_208 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_320 A h

lemma pivot_209 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_321 A h

lemma pivot_210 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_322 A h

lemma pivot_211 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_323 A h

lemma pivot_212 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_324 A h

lemma pivot_309 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 + A 7 18 + A 11 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_326 A h + pivot_325 A h)

lemma pivot_215 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_327 A h

lemma pivot_334 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 22 + A 11 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_330 A h

lemma pivot_335 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 23 + A 11 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_331 A h

lemma pivot_328 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 24 + A 11 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_332 A h

lemma pivot_329 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 25 + A 11 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_333 A h

lemma pivot_353 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_336 A h

lemma pivot_345 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_341 A h

lemma pivot_347 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_343 A h

lemma pivot_340 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_344 A h

lemma pivot_342 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_346 A h

lemma pivot_337 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_354 A h + pivot_353 A h)

lemma pivot_362 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_358 A h

lemma pivot_363 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_359 A h

lemma pivot_356 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_360 A h

lemma pivot_357 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_361 A h

lemma pivot_381 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_364 A h

lemma pivot_373 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_369 A h

lemma pivot_375 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_371 A h

lemma pivot_368 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_372 A h

lemma pivot_370 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_374 A h

lemma pivot_365 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_382 A h + pivot_381 A h)

lemma pivot_390 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_386 A h

lemma pivot_391 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_387 A h

lemma pivot_384 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_388 A h

lemma pivot_385 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_389 A h

lemma pivot_409 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_392 A h

lemma pivot_401 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_397 A h

lemma pivot_403 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_399 A h

lemma pivot_396 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_400 A h

lemma pivot_398 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_402 A h

lemma pivot_393 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_410 A h + pivot_409 A h)

lemma pivot_418 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_414 A h

lemma pivot_419 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_415 A h

lemma pivot_412 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_416 A h

lemma pivot_413 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_417 A h

lemma pivot_437 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_420 A h

lemma pivot_429 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_425 A h

lemma pivot_431 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_427 A h

lemma pivot_424 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_428 A h

lemma pivot_426 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_430 A h

lemma pivot_421 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_438 A h + pivot_437 A h)

lemma pivot_446 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_442 A h

lemma pivot_447 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_443 A h

lemma pivot_440 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_444 A h

lemma pivot_441 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_445 A h

lemma pivot_465 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_448 A h

lemma pivot_457 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_453 A h

lemma pivot_459 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_455 A h

lemma pivot_452 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_456 A h

lemma pivot_454 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_458 A h

lemma pivot_449 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_466 A h + pivot_465 A h)

lemma pivot_474 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_470 A h

lemma pivot_475 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_471 A h

lemma pivot_468 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_472 A h

lemma pivot_469 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_473 A h

lemma pivot_493 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 1 17 + A 2 0 + A 3 0 + A 17 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_476 A h + pivot_504 A h)

lemma pivot_86 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 2 + A 2 0 + A 2 2 + A 3 0 + A 3 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_478 A h + (pivot_506 A h + pivot_493 A h))

lemma pivot_87 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 3 + A 2 0 + A 2 3 + A 3 0 + A 3 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_479 A h + (pivot_507 A h + pivot_493 A h))

lemma pivot_485 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 + A 1 9 + A 2 5 + A 3 5 + A 17 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_481 A h + pivot_509 A h)

lemma pivot_487 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 + A 1 11 + A 2 7 + A 3 7 + A 17 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_483 A h + pivot_511 A h)

lemma pivot_480 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 1 4 + A 2 8 + A 3 8 + A 17 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_484 A h + pivot_512 A h)

lemma pivot_482 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 1 6 + A 2 10 + A 3 10 + A 17 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_486 A h + pivot_514 A h)

lemma pivot_96 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 12 + A 2 12 + A 3 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_488 A h + pivot_516 A h)

lemma pivot_97 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 13 + A 2 13 + A 3 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_489 A h + pivot_517 A h)

lemma pivot_98 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 14 + A 2 14 + A 3 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_490 A h + pivot_518 A h)

lemma pivot_99 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 15 + A 2 15 + A 3 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_491 A h + pivot_519 A h)

lemma pivot_100 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 16 + A 2 16 + A 3 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_492 A h + pivot_520 A h)

lemma pivot_477 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 18 + A 1 1 + A 2 0 + A 2 18 + A 3 0 + A 3 18 + A 17 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_494 A h + (pivot_522 A h + pivot_493 A h))

lemma pivot_103 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 19 + A 2 19 + A 3 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_495 A h + pivot_523 A h)

lemma pivot_502 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 22 + A 1 26 + A 2 22 + A 3 22 + A 17 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_498 A h + pivot_526 A h)

lemma pivot_503 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 23 + A 1 27 + A 2 23 + A 3 23 + A 17 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_499 A h + pivot_527 A h)

lemma pivot_496 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 + A 1 20 + A 2 24 + A 3 24 + A 17 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_500 A h + pivot_528 A h)

lemma pivot_497 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 25 + A 1 21 + A 2 25 + A 3 25 + A 17 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_501 A h + pivot_529 A h)

lemma pivot_549 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_532 A h

lemma pivot_541 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_537 A h

lemma pivot_543 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_539 A h

lemma pivot_536 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_540 A h

lemma pivot_538 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_542 A h

lemma pivot_533 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_550 A h + pivot_549 A h)

lemma pivot_558 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_554 A h

lemma pivot_559 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_555 A h

lemma pivot_552 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_556 A h

lemma pivot_553 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_557 A h

lemma pivot_672 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 17 + A 24 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_560 A h

lemma pivot_673 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_561 A h

lemma pivot_674 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 17 + A 24 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_562 A h

lemma pivot_675 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 17 + A 24 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_563 A h

lemma pivot_676 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_564 A h

lemma pivot_677 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 9 + A 24 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_565 A h

lemma pivot_678 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_566 A h

lemma pivot_679 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 11 + A 24 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_567 A h

lemma pivot_680 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 4 + A 24 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_568 A h

lemma pivot_681 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_569 A h

lemma pivot_682 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 6 + A 24 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_570 A h

lemma pivot_683 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_571 A h

lemma pivot_684 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_572 A h

lemma pivot_685 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_573 A h

lemma pivot_686 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_574 A h

lemma pivot_687 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_575 A h

lemma pivot_688 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_576 A h

lemma pivot_689 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_577 A h

lemma pivot_690 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 1 + A 20 17 + A 24 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_578 A h

lemma pivot_691 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_579 A h

lemma pivot_692 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_580 A h

lemma pivot_693 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_581 A h

lemma pivot_694 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 26 + A 24 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_582 A h

lemma pivot_695 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 27 + A 24 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_583 A h

lemma pivot_696 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 20 + A 24 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_584 A h

lemma pivot_697 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 21 + A 24 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_585 A h

lemma pivot_698 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_586 A h

lemma pivot_699 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_587 A h

lemma pivot_700 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 17 + A 25 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_588 A h

lemma pivot_701 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_589 A h

lemma pivot_702 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 17 + A 25 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_590 A h

lemma pivot_703 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 17 + A 25 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_591 A h

lemma pivot_704 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_592 A h

lemma pivot_705 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 9 + A 25 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_593 A h

lemma pivot_706 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_594 A h

lemma pivot_707 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 11 + A 25 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_595 A h

lemma pivot_708 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 4 + A 25 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_596 A h

lemma pivot_709 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_597 A h

lemma pivot_710 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 6 + A 25 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_598 A h

lemma pivot_711 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_599 A h

lemma pivot_712 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_600 A h

lemma pivot_713 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_601 A h

lemma pivot_714 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_602 A h

lemma pivot_715 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_603 A h

lemma pivot_716 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_604 A h

lemma pivot_717 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_605 A h

lemma pivot_718 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 1 + A 21 17 + A 25 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_606 A h

lemma pivot_719 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_607 A h

lemma pivot_720 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_608 A h

lemma pivot_721 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_609 A h

lemma pivot_722 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 26 + A 25 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_610 A h

lemma pivot_723 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 27 + A 25 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_611 A h

lemma pivot_724 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 20 + A 25 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_612 A h

lemma pivot_725 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 21 + A 25 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_613 A h

lemma pivot_726 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_614 A h

lemma pivot_727 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_615 A h

lemma pivot_633 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_616 A h

lemma pivot_625 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_621 A h

lemma pivot_627 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_623 A h

lemma pivot_620 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_624 A h

lemma pivot_622 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_626 A h

lemma pivot_617 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_634 A h + pivot_633 A h)

lemma pivot_642 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_638 A h

lemma pivot_643 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_639 A h

lemma pivot_636 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_640 A h

lemma pivot_637 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_641 A h

lemma pivot_661 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_644 A h

lemma pivot_653 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_649 A h

lemma pivot_655 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_651 A h

lemma pivot_648 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_652 A h

lemma pivot_650 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_654 A h

lemma pivot_645 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_662 A h + pivot_661 A h)

lemma pivot_670 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_666 A h

lemma pivot_671 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_667 A h

lemma pivot_664 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_668 A h

lemma pivot_665 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_669 A h

lemma pivot_745 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 0 + A 26 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_728 A h

lemma pivot_618 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 0 + A 22 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_730 A h + pivot_745 A h)

lemma pivot_619 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 0 + A 22 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_731 A h + pivot_745 A h)

lemma pivot_737 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 5 + A 26 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_733 A h

lemma pivot_739 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 7 + A 26 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_735 A h

lemma pivot_732 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 8 + A 26 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_736 A h

lemma pivot_734 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 10 + A 26 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_738 A h

lemma pivot_628 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_740 A h

lemma pivot_629 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_741 A h

lemma pivot_630 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_742 A h

lemma pivot_631 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_743 A h

lemma pivot_632 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_744 A h

lemma pivot_729 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 0 + A 22 18 + A 26 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_746 A h + pivot_745 A h)

lemma pivot_635 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_747 A h

lemma pivot_754 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 22 + A 26 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_750 A h

lemma pivot_755 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 23 + A 26 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_751 A h

lemma pivot_748 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 24 + A 26 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_752 A h

lemma pivot_749 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 25 + A 26 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_753 A h

lemma pivot_773 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 0 + A 27 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_756 A h

lemma pivot_646 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 0 + A 23 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_758 A h + pivot_773 A h)

lemma pivot_647 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 0 + A 23 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_759 A h + pivot_773 A h)

lemma pivot_765 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 5 + A 27 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_761 A h

lemma pivot_767 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 7 + A 27 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_763 A h

lemma pivot_760 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 8 + A 27 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_764 A h

lemma pivot_762 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 10 + A 27 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_766 A h

lemma pivot_656 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_768 A h

lemma pivot_657 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_769 A h

lemma pivot_658 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_770 A h

lemma pivot_659 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_771 A h

lemma pivot_660 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_772 A h

lemma pivot_757 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 0 + A 23 18 + A 27 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_774 A h + pivot_773 A h)

lemma pivot_663 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_775 A h

lemma pivot_782 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 22 + A 27 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_778 A h

lemma pivot_783 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 23 + A 27 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_779 A h

lemma pivot_776 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 24 + A 27 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_780 A h

lemma pivot_777 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 25 + A 27 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_781 A h

lemma pivot_18 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_784 A h

lemma pivot_8 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_788 A h

lemma pivot_10 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_790 A h

lemma pivot_5 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_793 A h

lemma pivot_7 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_795 A h

lemma pivot_24 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_804 A h

lemma pivot_25 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_805 A h

lemma pivot_22 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_810 A h

lemma pivot_23 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_811 A h

lemma pivot_476 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 18 + A 17 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_812 A h

lemma pivot_102 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 18 + A 1 1 + A 2 0 + A 2 18 + A 3 0 + A 3 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_813 A h + pivot_477 A h)

lemma pivot_478 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 18 + A 17 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_814 A h

lemma pivot_479 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 18 + A 17 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_815 A h

lemma pivot_92 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 1 4 + A 1 8 + A 2 8 + A 3 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_816 A h + pivot_480 A h)

lemma pivot_481 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_817 A h

lemma pivot_94 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 1 6 + A 1 10 + A 2 10 + A 3 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_818 A h + pivot_482 A h)

lemma pivot_483 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_819 A h

lemma pivot_484 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_820 A h

lemma pivot_89 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 + A 1 5 + A 1 9 + A 2 5 + A 3 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_821 A h + pivot_485 A h)

lemma pivot_486 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_822 A h

lemma pivot_91 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 + A 1 7 + A 1 11 + A 2 7 + A 3 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_823 A h + pivot_487 A h)

lemma pivot_488 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_824 A h

lemma pivot_489 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_825 A h

lemma pivot_490 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_826 A h

lemma pivot_491 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_827 A h

lemma pivot_492 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_828 A h

lemma pivot_84 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 1 1 + A 1 17 + A 1 18 + A 2 0 + A 3 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_829 A h + pivot_493 A h)

lemma pivot_494 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_830 A h

lemma pivot_495 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_831 A h

lemma pivot_108 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 + A 1 20 + A 1 24 + A 2 24 + A 3 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_832 A h + pivot_496 A h)

lemma pivot_109 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 25 + A 1 21 + A 1 25 + A 2 25 + A 3 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_833 A h + pivot_497 A h)

lemma pivot_498 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_834 A h

lemma pivot_499 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_835 A h

lemma pivot_500 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_836 A h

lemma pivot_501 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_837 A h

lemma pivot_106 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 22 + A 1 22 + A 1 26 + A 2 22 + A 3 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_838 A h + pivot_502 A h)

lemma pivot_107 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 23 + A 1 23 + A 1 27 + A 2 23 + A 3 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_839 A h + pivot_503 A h)

lemma pivot_74 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_840 A h

lemma pivot_64 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_844 A h

lemma pivot_66 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_846 A h

lemma pivot_61 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_849 A h

lemma pivot_63 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_851 A h

lemma pivot_80 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_860 A h

lemma pivot_81 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_861 A h

lemma pivot_78 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_866 A h

lemma pivot_79 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_867 A h

lemma pivot_46 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 18 + A 1 17 + A 1 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_868 A h + pivot_102 A h) + (pivot_84 A h + pivot_74 A h))

lemma pivot_36 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 1 4 + A 1 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_872 A h + (pivot_92 A h + pivot_64 A h))

lemma pivot_38 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 1 6 + A 1 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_874 A h + (pivot_94 A h + pivot_66 A h))

lemma pivot_37 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 + A 1 5 + A 1 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_877 A h + (pivot_89 A h + pivot_61 A h))

lemma pivot_39 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 + A 1 7 + A 1 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_879 A h + (pivot_91 A h + pivot_63 A h))

lemma pivot_52 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 + A 1 20 + A 1 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_888 A h + (pivot_108 A h + pivot_80 A h))

lemma pivot_53 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 25 + A 1 21 + A 1 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_889 A h + (pivot_109 A h + pivot_81 A h))

lemma pivot_54 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 22 + A 1 22 + A 1 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_894 A h + (pivot_106 A h + pivot_78 A h))

lemma pivot_55 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 23 + A 1 23 + A 1 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_895 A h + (pivot_107 A h + pivot_79 A h))

lemma pivot_130 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_896 A h

lemma pivot_120 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_900 A h

lemma pivot_122 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_902 A h

lemma pivot_117 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_905 A h

lemma pivot_119 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_907 A h

lemma pivot_113 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_913 A h + pivot_130 A h)

lemma pivot_136 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_916 A h

lemma pivot_137 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_917 A h

lemma pivot_134 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_922 A h

lemma pivot_135 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_923 A h

lemma pivot_252 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 18 + A 9 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_924 A h

lemma pivot_158 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 0 + A 5 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_925 A h + pivot_253 A h)

lemma pivot_254 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 18 + A 9 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_926 A h

lemma pivot_255 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 18 + A 9 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_927 A h

lemma pivot_257 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_929 A h

lemma pivot_259 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_931 A h

lemma pivot_260 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_932 A h

lemma pivot_262 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_934 A h

lemma pivot_264 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_936 A h

lemma pivot_265 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_937 A h

lemma pivot_266 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_938 A h

lemma pivot_267 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_939 A h

lemma pivot_268 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_940 A h

lemma pivot_270 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_942 A h

lemma pivot_271 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_943 A h

lemma pivot_274 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_946 A h

lemma pivot_275 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_947 A h

lemma pivot_276 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_948 A h

lemma pivot_277 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_949 A h

lemma pivot_186 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_952 A h

lemma pivot_176 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_956 A h

lemma pivot_178 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_958 A h

lemma pivot_173 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_961 A h

lemma pivot_175 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_963 A h

lemma pivot_169 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_969 A h + pivot_186 A h)

lemma pivot_192 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_972 A h

lemma pivot_193 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_973 A h

lemma pivot_190 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_978 A h

lemma pivot_191 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_979 A h

lemma pivot_308 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 18 + A 11 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_980 A h

lemma pivot_214 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 + A 7 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_981 A h + pivot_309 A h)

lemma pivot_310 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 18 + A 11 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_982 A h

lemma pivot_311 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 18 + A 11 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_983 A h

lemma pivot_313 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_985 A h

lemma pivot_315 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_987 A h

lemma pivot_316 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_988 A h

lemma pivot_318 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_990 A h

lemma pivot_320 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_992 A h

lemma pivot_321 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_993 A h

lemma pivot_322 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_994 A h

lemma pivot_323 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_995 A h

lemma pivot_324 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_996 A h

lemma pivot_326 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_998 A h

lemma pivot_327 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_999 A h

lemma pivot_330 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1002 A h

lemma pivot_331 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1003 A h

lemma pivot_332 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1004 A h

lemma pivot_333 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1005 A h

lemma pivot_129 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 0 + A 4 1 + A 4 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1008 A h + pivot_242 A h)

lemma pivot_114 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 0 + A 4 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1010 A h + (pivot_242 A h + pivot_129 A h))

lemma pivot_115 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 0 + A 4 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1011 A h + (pivot_242 A h + pivot_129 A h))

lemma pivot_124 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1020 A h

lemma pivot_125 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1021 A h

lemma pivot_126 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1022 A h

lemma pivot_127 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1023 A h

lemma pivot_128 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1024 A h

lemma pivot_131 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1027 A h

lemma pivot_185 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 0 + A 6 1 + A 6 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1064 A h + pivot_298 A h)

lemma pivot_170 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 0 + A 6 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1066 A h + (pivot_298 A h + pivot_185 A h))

lemma pivot_171 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 0 + A 6 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1067 A h + (pivot_298 A h + pivot_185 A h))

lemma pivot_180 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1076 A h

lemma pivot_181 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1077 A h

lemma pivot_182 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1078 A h

lemma pivot_183 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1079 A h

lemma pivot_184 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1080 A h

lemma pivot_187 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1083 A h

lemma pivot_354 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1120 A h

lemma pivot_344 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1124 A h

lemma pivot_346 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1126 A h

lemma pivot_341 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1129 A h

lemma pivot_343 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1131 A h

lemma pivot_360 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1140 A h

lemma pivot_361 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1141 A h

lemma pivot_358 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1146 A h

lemma pivot_359 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1147 A h

lemma pivot_382 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1148 A h

lemma pivot_372 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1152 A h

lemma pivot_374 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1154 A h

lemma pivot_369 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1157 A h

lemma pivot_371 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1159 A h

lemma pivot_388 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1168 A h

lemma pivot_389 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1169 A h

lemma pivot_386 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1174 A h

lemma pivot_387 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1175 A h

lemma pivot_410 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1176 A h

lemma pivot_400 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1180 A h

lemma pivot_402 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1182 A h

lemma pivot_397 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1185 A h

lemma pivot_399 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1187 A h

lemma pivot_416 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1196 A h

lemma pivot_417 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1197 A h

lemma pivot_414 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1202 A h

lemma pivot_415 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1203 A h

lemma pivot_438 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1204 A h

lemma pivot_428 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1208 A h

lemma pivot_430 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1210 A h

lemma pivot_425 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1213 A h

lemma pivot_427 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1215 A h

lemma pivot_444 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1224 A h

lemma pivot_445 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1225 A h

lemma pivot_442 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1230 A h

lemma pivot_443 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1231 A h

lemma pivot_466 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1232 A h

lemma pivot_456 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1236 A h

lemma pivot_458 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1238 A h

lemma pivot_453 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1241 A h

lemma pivot_455 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1243 A h

lemma pivot_472 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1252 A h

lemma pivot_473 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1253 A h

lemma pivot_470 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1258 A h

lemma pivot_471 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1259 A h

lemma pivot_550 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1316 A h

lemma pivot_540 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1320 A h

lemma pivot_542 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1322 A h

lemma pivot_537 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1325 A h

lemma pivot_539 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1327 A h

lemma pivot_556 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1336 A h

lemma pivot_557 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1337 A h

lemma pivot_554 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1342 A h

lemma pivot_555 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1343 A h

lemma pivot_578 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1344 A h

lemma pivot_568 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1348 A h

lemma pivot_570 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1350 A h

lemma pivot_565 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1353 A h

lemma pivot_567 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1355 A h

lemma pivot_561 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1361 A h + pivot_578 A h)

lemma pivot_584 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1364 A h

lemma pivot_585 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1365 A h

lemma pivot_582 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1370 A h

lemma pivot_583 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1371 A h

lemma pivot_606 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1372 A h

lemma pivot_596 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1376 A h

lemma pivot_598 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1378 A h

lemma pivot_593 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1381 A h

lemma pivot_595 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1383 A h

lemma pivot_589 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1389 A h + pivot_606 A h)

lemma pivot_612 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1392 A h

lemma pivot_613 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1393 A h

lemma pivot_610 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1398 A h

lemma pivot_611 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1399 A h

lemma pivot_728 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 18 + A 26 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1400 A h

lemma pivot_634 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 0 + A 22 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1401 A h + pivot_729 A h)

lemma pivot_730 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 18 + A 26 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1402 A h

lemma pivot_731 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 18 + A 26 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1403 A h

lemma pivot_733 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1405 A h

lemma pivot_735 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1407 A h

lemma pivot_736 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1408 A h

lemma pivot_738 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1410 A h

lemma pivot_740 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1412 A h

lemma pivot_741 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1413 A h

lemma pivot_742 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1414 A h

lemma pivot_743 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1415 A h

lemma pivot_744 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1416 A h

lemma pivot_746 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1418 A h

lemma pivot_747 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1419 A h

lemma pivot_750 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1422 A h

lemma pivot_751 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1423 A h

lemma pivot_752 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1424 A h

lemma pivot_753 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1425 A h

lemma pivot_756 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 18 + A 27 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1428 A h

lemma pivot_662 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 0 + A 23 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1429 A h + pivot_757 A h)

lemma pivot_758 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 18 + A 27 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1430 A h

lemma pivot_759 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 18 + A 27 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1431 A h

lemma pivot_761 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1433 A h

lemma pivot_763 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1435 A h

lemma pivot_764 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1436 A h

lemma pivot_766 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1438 A h

lemma pivot_768 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1440 A h

lemma pivot_769 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1441 A h

lemma pivot_770 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1442 A h

lemma pivot_771 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1443 A h

lemma pivot_772 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1444 A h

lemma pivot_774 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1446 A h

lemma pivot_775 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1447 A h

lemma pivot_778 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1450 A h

lemma pivot_779 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1451 A h

lemma pivot_780 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1452 A h

lemma pivot_781 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1453 A h

lemma pivot_577 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 0 + A 20 1 + A 20 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1456 A h + pivot_690 A h)

lemma pivot_562 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 0 + A 20 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1458 A h + (pivot_690 A h + pivot_577 A h))

lemma pivot_563 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 0 + A 20 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1459 A h + (pivot_690 A h + pivot_577 A h))

lemma pivot_572 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1468 A h

lemma pivot_573 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1469 A h

lemma pivot_574 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1470 A h

lemma pivot_575 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1471 A h

lemma pivot_576 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1472 A h

lemma pivot_579 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1475 A h

lemma pivot_605 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 0 + A 21 1 + A 21 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1484 A h + pivot_718 A h)

lemma pivot_590 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 0 + A 21 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1486 A h + (pivot_718 A h + pivot_605 A h))

lemma pivot_591 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 0 + A 21 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1487 A h + (pivot_718 A h + pivot_605 A h))

lemma pivot_600 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1496 A h

lemma pivot_601 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1497 A h

lemma pivot_602 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1498 A h

lemma pivot_603 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1499 A h

lemma pivot_604 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1500 A h

lemma pivot_607 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1503 A h

lemma pivot_168 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1568 A h

lemma pivot_172 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1572 A h

lemma pivot_174 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 5 + A 6 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1574 A h

lemma pivot_177 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 0 12 + A 0 13 + A 6 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1577 A h

lemma pivot_179 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 14 + A 0 15 + A 0 18 + A 0 19 + A 0 22 + A 0 23 + A 6 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1579 A h

lemma pivot_16 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 0 9 + A 0 12 + A 0 13 + A 0 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1585 A h + (pivot_185 A h + pivot_169 A h)) + (pivot_168 A h + (pivot_21 A h + pivot_20 A h)))

lemma pivot_188 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 0 12 + A 0 16 + A 6 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1588 A h

lemma pivot_189 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 0 13 + A 0 16 + A 6 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1589 A h

lemma pivot_194 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 2 + A 0 25 + A 6 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1594 A h

lemma pivot_195 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 3 + A 0 24 + A 6 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1595 A h

lemma pivot_49 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 + A 0 25 + A 1 5 + A 1 20 + A 1 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1597 A h + (pivot_53 A h + pivot_52 A h))

lemma pivot_33 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 0 + A 1 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1602 A h

lemma pivot_41 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 8 + A 1 12 + A 1 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1605 A h

lemma pivot_45 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 18 + A 1 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1606 A h + pivot_46 A h)

lemma pivot_51 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 10 + A 1 14 + A 1 15 + A 1 18 + A 1 19 + A 1 22 + A 1 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1607 A h

lemma pivot_32 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 1 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1608 A h + pivot_36 A h)

lemma pivot_50 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 10 + A 1 18 + A 1 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1610 A h

lemma pivot_47 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 10 + A 1 14 + A 1 15 + A 1 18 + A 1 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1611 A h + (pivot_51 A h + pivot_50 A h))

lemma pivot_44 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 + A 0 25 + A 1 5 + A 1 8 + A 1 9 + A 1 12 + A 1 13 + A 1 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1613 A h + pivot_49 A h)

lemma pivot_40 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 + A 0 25 + A 1 5 + A 1 8 + A 1 9 + A 1 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1616 A h + (pivot_44 A h + pivot_41 A h))

lemma pivot_48 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 + A 1 2 + A 1 5 + A 1 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1622 A h + (pivot_53 A h + pivot_49 A h))

lemma pivot_31 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 0 + A 1 2 + A 1 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1623 A h + pivot_52 A h) + (pivot_48 A h + pivot_33 A h))

lemma pivot_616 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1624 A h + (pivot_728 A h + pivot_634 A h))

lemma pivot_624 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1628 A h + pivot_732 A h)

lemma pivot_626 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 0 + A 2 5 + A 22 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1630 A h + pivot_734 A h)

lemma pivot_621 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 8 + A 2 12 + A 2 13 + A 22 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1633 A h + pivot_737 A h)

lemma pivot_623 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 10 + A 2 14 + A 2 15 + A 2 18 + A 2 19 + A 2 22 + A 2 23 + A 22 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1635 A h + pivot_739 A h)

lemma pivot_72 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 8 + A 2 9 + A 2 12 + A 2 13 + A 2 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1641 A h + pivot_745 A h) + (pivot_616 A h + (pivot_77 A h + pivot_76 A h)))

lemma pivot_640 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 8 + A 2 12 + A 2 16 + A 22 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1644 A h + pivot_748 A h)

lemma pivot_641 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 8 + A 2 13 + A 2 16 + A 22 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1645 A h + pivot_749 A h)

lemma pivot_638 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 2 + A 2 25 + A 22 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1650 A h + pivot_754 A h)

lemma pivot_639 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 3 + A 2 24 + A 22 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1651 A h + pivot_755 A h)

lemma pivot_644 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1652 A h + (pivot_756 A h + pivot_662 A h))

lemma pivot_652 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1656 A h + pivot_760 A h)

lemma pivot_654 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 0 + A 3 5 + A 23 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1658 A h + pivot_762 A h)

lemma pivot_649 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 8 + A 3 12 + A 3 13 + A 23 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1661 A h + pivot_765 A h)

lemma pivot_651 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 10 + A 3 14 + A 3 15 + A 3 18 + A 3 19 + A 3 22 + A 3 23 + A 23 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1663 A h + pivot_767 A h)

lemma pivot_668 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 8 + A 3 12 + A 3 16 + A 23 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1672 A h + pivot_776 A h)

lemma pivot_669 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 8 + A 3 13 + A 3 16 + A 23 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1673 A h + pivot_777 A h)

lemma pivot_666 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 2 + A 3 25 + A 23 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1678 A h + pivot_782 A h)

lemma pivot_667 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 3 + A 3 24 + A 23 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1679 A h + pivot_783 A h)

lemma pivot_112 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1686 A h + pivot_117 A h)

lemma pivot_133 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 8 + A 4 9 + A 4 12 + A 4 13 + A 4 16 + A 4 20 + A 4 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1697 A h

lemma pivot_28 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1708 A h + pivot_168 A h)

lemma pivot_165 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 1 + A 5 5 + A 5 24 + A 5 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1709 A h + pivot_169 A h)

lemma pivot_30 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1710 A h + (pivot_170 A h + pivot_168 A h))

lemma pivot_145 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 5 + A 1 6 + A 5 0 + A 5 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1714 A h + pivot_174 A h)

lemma pivot_35 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1715 A h + pivot_175 A h)

lemma pivot_148 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 0 12 + A 0 13 + A 1 9 + A 5 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1717 A h + pivot_177 A h) + (pivot_153 A h + pivot_152 A h))

lemma pivot_140 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 10 + A 5 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1718 A h + (pivot_178 A h + pivot_158 A h))

lemma pivot_163 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 14 + A 0 15 + A 0 18 + A 0 19 + A 0 22 + A 0 23 + A 1 11 + A 5 10 + A 5 14 + A 5 15 + A 5 18 + A 5 19 + A 5 22 + A 5 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1719 A h + pivot_179 A h)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_13 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 + A 0 12 + A 0 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1720 A h + pivot_180 A h) + (pivot_148 A h + (pivot_40 A h + pivot_36 A h))) + ((pivot_33 A h + pivot_32 A h) + (pivot_28 A h + (pivot_25 A h + pivot_24 A h))))

lemma pivot_162 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 14 + A 5 10 + A 5 18 + A 5 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1722 A h + pivot_182 A h)

lemma pivot_150 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 14 + A 0 15 + A 0 18 + A 0 19 + A 0 22 + A 0 23 + A 1 11 + A 1 14 + A 1 15 + A 5 0 + A 5 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1723 A h + pivot_183 A h) + (pivot_163 A h + pivot_162 A h)) + ((pivot_159 A h + pivot_158 A h) + (pivot_155 A h + pivot_154 A h)))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_12 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 + A 0 8 + A 0 9 + A 0 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1728 A h + pivot_188 A h) + (pivot_156 A h + (pivot_152 A h + pivot_148 A h))) + ((pivot_48 A h + pivot_37 A h) + (pivot_30 A h + (pivot_24 A h + pivot_16 A h))))

lemma pivot_164 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 2 + A 0 25 + A 1 1 + A 1 26 + A 5 2 + A 5 5 + A 5 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1734 A h + (pivot_194 A h + pivot_165 A h))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_29 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 2 + A 0 3 + A 0 5 + A 0 10 + A 0 22 + A 0 23 + A 0 24 + A 0 25 + A 1 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1735 A h + (pivot_195 A h + pivot_164 A h)) + (pivot_145 A h + (pivot_143 A h + pivot_142 A h))) + ((pivot_140 A h + (pivot_55 A h + pivot_54 A h)) + (pivot_51 A h + (pivot_47 A h + pivot_38 A h))))

lemma pivot_221 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 5 + A 7 24 + A 7 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1765 A h

lemma pivot_201 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 + A 7 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1770 A h

lemma pivot_204 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1773 A h + (pivot_209 A h + pivot_208 A h))

lemma pivot_196 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1774 A h + pivot_214 A h)

lemma pivot_219 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 10 + A 7 14 + A 7 15 + A 7 18 + A 7 19 + A 7 22 + A 7 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1775 A h

lemma pivot_218 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 10 + A 7 18 + A 7 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1778 A h

lemma pivot_206 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 + A 7 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1779 A h + (pivot_219 A h + pivot_218 A h)) + ((pivot_215 A h + pivot_214 A h) + (pivot_211 A h + pivot_210 A h)))

lemma pivot_220 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 2 + A 7 5 + A 7 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1790 A h + pivot_221 A h)

lemma pivot_588 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 0 + A 12 0 + A 13 0 + A 16 0 + A 17 0 + A 20 0 + A 21 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1792 A h

lemma pivot_450 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 0 + A 9 2 + A 12 0 + A 12 2 + A 13 0 + A 13 2 + A 16 0 + A 16 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1794 A h + (pivot_590 A h + pivot_588 A h)) + (pivot_562 A h + (pivot_478 A h + pivot_476 A h)))

lemma pivot_451 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 0 + A 9 3 + A 12 0 + A 12 3 + A 13 0 + A 13 3 + A 16 0 + A 16 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1795 A h + (pivot_591 A h + pivot_588 A h)) + (pivot_563 A h + (pivot_479 A h + pivot_476 A h)))

lemma pivot_592 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 4 + A 12 4 + A 13 4 + A 16 4 + A 17 4 + A 20 4 + A 21 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1796 A h

lemma pivot_594 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 0 + A 8 5 + A 9 6 + A 12 6 + A 13 6 + A 16 6 + A 17 6 + A 20 6 + A 21 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1798 A h

lemma pivot_597 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 8 + A 8 12 + A 8 13 + A 9 9 + A 12 9 + A 13 9 + A 16 9 + A 17 9 + A 20 9 + A 21 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1801 A h

lemma pivot_599 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 10 + A 8 14 + A 8 15 + A 8 18 + A 8 19 + A 8 22 + A 8 23 + A 9 11 + A 12 11 + A 13 11 + A 16 11 + A 17 11 + A 20 11 + A 21 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1803 A h

lemma pivot_460 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 8 + A 9 12 + A 12 12 + A 13 12 + A 16 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1804 A h + pivot_600 A h) + (pivot_572 A h + pivot_488 A h))

lemma pivot_461 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 8 + A 9 13 + A 12 13 + A 13 13 + A 16 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1805 A h + pivot_601 A h) + (pivot_573 A h + pivot_489 A h))

lemma pivot_462 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 10 + A 8 18 + A 8 22 + A 9 14 + A 12 14 + A 13 14 + A 16 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1806 A h + pivot_602 A h) + (pivot_574 A h + pivot_490 A h))

lemma pivot_463 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 10 + A 8 18 + A 8 23 + A 9 15 + A 12 15 + A 13 15 + A 16 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1807 A h + pivot_603 A h) + (pivot_575 A h + pivot_491 A h))

lemma pivot_464 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 8 + A 9 16 + A 12 16 + A 13 16 + A 16 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1808 A h + pivot_604 A h) + (pivot_576 A h + pivot_492 A h))

lemma pivot_448 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 1 17 + A 1 18 + A 2 0 + A 3 0 + A 8 8 + A 8 9 + A 8 12 + A 8 13 + A 8 16 + A 8 20 + A 8 21 + A 9 0 + A 9 17 + A 12 0 + A 12 17 + A 13 0 + A 13 17 + A 16 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1809 A h + pivot_605 A h) + (pivot_589 A h + pivot_588 A h)) + ((pivot_577 A h + pivot_561 A h) + (pivot_493 A h + (pivot_476 A h + pivot_465 A h))))

lemma pivot_467 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 18 + A 8 22 + A 8 23 + A 9 19 + A 12 19 + A 13 19 + A 16 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1811 A h + pivot_607 A h) + (pivot_579 A h + pivot_495 A h))

lemma pivot_608 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 8 + A 8 12 + A 8 16 + A 9 20 + A 12 20 + A 13 20 + A 16 20 + A 17 20 + A 20 20 + A 21 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1812 A h

lemma pivot_609 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 8 + A 8 13 + A 8 16 + A 9 21 + A 12 21 + A 13 21 + A 16 21 + A 17 21 + A 20 21 + A 21 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1813 A h

lemma pivot_614 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 2 + A 8 25 + A 9 26 + A 12 26 + A 13 26 + A 16 26 + A 17 26 + A 20 26 + A 21 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1818 A h

lemma pivot_615 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 3 + A 8 24 + A 9 27 + A 12 27 + A 13 27 + A 16 27 + A 17 27 + A 20 27 + A 21 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1819 A h

lemma pivot_420 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 0 + A 14 0 + A 15 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1848 A h

lemma pivot_422 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 2 + A 14 2 + A 15 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1850 A h

lemma pivot_423 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 3 + A 14 3 + A 15 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1851 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_203 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 1 + A 6 6 + A 6 17 + A 6 26 + A 6 27 + A 7 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1859 A h + pivot_431 A h) + (pivot_403 A h + (pivot_319 A h + pivot_303 A h))) + ((pivot_302 A h + (pivot_299 A h + pivot_298 A h)) + (pivot_295 A h + (pivot_294 A h + pivot_290 A h))))

lemma pivot_432 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 8 + A 11 12 + A 14 12 + A 15 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1860 A h

lemma pivot_433 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 8 + A 11 13 + A 14 13 + A 15 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1861 A h

lemma pivot_434 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 10 + A 10 18 + A 10 22 + A 11 14 + A 14 14 + A 15 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1862 A h

lemma pivot_435 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 10 + A 10 18 + A 10 23 + A 11 15 + A 14 15 + A 15 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1863 A h

lemma pivot_436 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 8 + A 11 16 + A 14 16 + A 15 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1864 A h

lemma pivot_439 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 18 + A 10 22 + A 10 23 + A 11 19 + A 14 19 + A 15 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1867 A h

lemma pivot_560 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 0 + A 17 0 + A 20 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1904 A h

lemma pivot_564 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 4 + A 17 4 + A 20 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1908 A h

lemma pivot_566 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 6 + A 12 0 + A 12 5 + A 17 6 + A 20 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1910 A h

lemma pivot_569 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 9 + A 12 8 + A 12 12 + A 12 13 + A 17 9 + A 20 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1913 A h

lemma pivot_571 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 11 + A 12 10 + A 12 14 + A 12 15 + A 12 18 + A 12 19 + A 12 22 + A 12 23 + A 17 11 + A 20 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1915 A h

lemma pivot_352 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 1 17 + A 1 18 + A 2 0 + A 3 0 + A 9 0 + A 9 17 + A 12 8 + A 12 9 + A 12 12 + A 12 13 + A 12 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1921 A h + pivot_577 A h) + (pivot_561 A h + pivot_560 A h)) + ((pivot_493 A h + pivot_476 A h) + (pivot_357 A h + pivot_356 A h)))

lemma pivot_580 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 20 + A 12 8 + A 12 12 + A 12 16 + A 17 20 + A 20 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1924 A h

lemma pivot_581 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 21 + A 12 8 + A 12 13 + A 12 16 + A 17 21 + A 20 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1925 A h

lemma pivot_586 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 26 + A 12 2 + A 12 25 + A 17 26 + A 20 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1930 A h

lemma pivot_587 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 27 + A 12 3 + A 12 24 + A 17 27 + A 20 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1931 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_116 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 1 10 + A 1 17 + A 2 0 + A 3 0 + A 4 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_1932 A h + pivot_588 A h) + (pivot_560 A h + pivot_476 A h)) + ((pivot_448 A h + pivot_381 A h) + (pivot_353 A h + pivot_269 A h))) + (((pivot_245 A h + pivot_244 A h) + (pivot_240 A h + pivot_237 A h)) + ((pivot_236 A h + pivot_233 A h) + (pivot_232 A h + pivot_140 A h))))

lemma pivot_364 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 1 6 + A 2 10 + A 3 10 + A 8 0 + A 8 5 + A 9 6 + A 12 0 + A 12 5 + A 12 6 + A 13 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1938 A h + (pivot_594 A h + pivot_566 A h)) + ((pivot_482 A h + pivot_454 A h) + (pivot_370 A h + pivot_369 A h)))

lemma pivot_377 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 + A 1 9 + A 2 5 + A 3 5 + A 8 8 + A 8 12 + A 8 13 + A 9 9 + A 12 8 + A 12 9 + A 12 12 + A 12 13 + A 13 8 + A 13 9 + A 13 12 + A 13 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1941 A h + pivot_597 A h) + (pivot_569 A h + (pivot_485 A h + pivot_457 A h)))

lemma pivot_383 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 + A 1 11 + A 2 7 + A 3 7 + A 8 10 + A 8 14 + A 8 15 + A 8 18 + A 8 19 + A 8 22 + A 8 23 + A 9 11 + A 12 10 + A 12 11 + A 12 14 + A 12 15 + A 12 18 + A 12 19 + A 12 22 + A 12 23 + A 13 10 + A 13 11 + A 13 14 + A 13 15 + A 13 18 + A 13 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1943 A h + (pivot_599 A h + pivot_571 A h)) + ((pivot_487 A h + pivot_459 A h) + (pivot_387 A h + pivot_386 A h)))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_380 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 18 + A 8 8 + A 8 9 + A 8 12 + A 8 13 + A 8 16 + A 8 20 + A 8 21 + A 9 0 + A 12 17 + A 13 8 + A 13 9 + A 13 12 + A 13 13 + A 13 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1949 A h + pivot_605 A h) + (pivot_589 A h + (pivot_588 A h + pivot_560 A h))) + ((pivot_493 A h + pivot_448 A h) + (pivot_385 A h + (pivot_384 A h + pivot_381 A h))))

lemma pivot_376 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 + A 0 24 + A 1 9 + A 1 18 + A 1 20 + A 2 5 + A 2 24 + A 3 5 + A 3 24 + A 8 8 + A 8 9 + A 8 12 + A 8 20 + A 8 21 + A 9 0 + A 9 9 + A 9 20 + A 12 9 + A 12 13 + A 12 16 + A 12 17 + A 12 20 + A 13 8 + A 13 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_1952 A h + pivot_608 A h) + (pivot_580 A h + pivot_496 A h)) + ((pivot_468 A h + pivot_384 A h) + (pivot_380 A h + pivot_377 A h)))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_34 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 1 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_1953 A h + (pivot_609 A h + pivot_581 A h)) + ((pivot_497 A h + pivot_469 A h) + (pivot_385 A h + pivot_380 A h))) + (((pivot_376 A h + pivot_373 A h) + (pivot_372 A h + pivot_357 A h)) + ((pivot_356 A h + pivot_345 A h) + (pivot_344 A h + pivot_273 A h)))) + (((pivot_272 A h + (pivot_261 A h + pivot_232 A h)) + ((pivot_165 A h + pivot_116 A h) + (pivot_109 A h + pivot_108 A h))) + (((pivot_89 A h + pivot_84 A h) + (pivot_53 A h + pivot_52 A h)) + ((pivot_49 A h + pivot_46 A h) + (pivot_45 A h + pivot_38 A h)))))

lemma pivot_366 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 22 + A 1 26 + A 2 22 + A 3 22 + A 8 2 + A 8 25 + A 9 26 + A 12 2 + A 12 25 + A 12 26 + A 13 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1958 A h + (pivot_614 A h + pivot_586 A h)) + ((pivot_502 A h + pivot_474 A h) + (pivot_390 A h + pivot_389 A h)))

lemma pivot_367 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 23 + A 1 27 + A 2 23 + A 3 23 + A 8 3 + A 8 24 + A 9 27 + A 12 3 + A 12 24 + A 12 27 + A 13 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_1959 A h + (pivot_615 A h + pivot_587 A h)) + ((pivot_503 A h + pivot_475 A h) + (pivot_391 A h + pivot_388 A h)))

lemma pivot_392 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 6 + A 14 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1966 A h + pivot_397 A h)

lemma pivot_405 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 9 + A 14 8 + A 14 12 + A 14 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_1969 A h

lemma pivot_411 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 11 + A 14 10 + A 14 14 + A 14 15 + A 14 18 + A 14 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1971 A h + (pivot_415 A h + pivot_414 A h))

lemma pivot_408 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 17 + A 14 8 + A 14 9 + A 14 12 + A 14 13 + A 14 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1977 A h + (pivot_413 A h + pivot_412 A h))

lemma pivot_404 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 9 + A 11 17 + A 11 20 + A 14 8 + A 14 9 + A 14 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1980 A h + (pivot_408 A h + pivot_405 A h))

lemma pivot_394 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 26 + A 14 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1986 A h + pivot_417 A h)

lemma pivot_395 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 27 + A 14 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_1987 A h + pivot_416 A h)

lemma pivot_532 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 0 + A 11 0 + A 14 0 + A 15 0 + A 19 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2072 A h + (pivot_644 A h + pivot_616 A h))

lemma pivot_534 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 2 + A 11 2 + A 14 2 + A 15 2 + A 19 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_2074 A h + pivot_646 A h) + (pivot_644 A h + (pivot_618 A h + pivot_616 A h)))

lemma pivot_535 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 3 + A 11 3 + A 14 3 + A 15 3 + A 19 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_2075 A h + pivot_647 A h) + (pivot_644 A h + (pivot_619 A h + pivot_616 A h)))

lemma pivot_544 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 12 + A 11 12 + A 14 12 + A 15 12 + A 18 8 + A 19 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2084 A h + (pivot_656 A h + pivot_628 A h))

lemma pivot_545 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 13 + A 11 13 + A 14 13 + A 15 13 + A 18 8 + A 19 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2085 A h + (pivot_657 A h + pivot_629 A h))

lemma pivot_546 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 14 + A 11 14 + A 14 14 + A 15 14 + A 18 10 + A 18 18 + A 18 22 + A 19 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2086 A h + (pivot_658 A h + pivot_630 A h))

lemma pivot_547 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 15 + A 11 15 + A 14 15 + A 15 15 + A 18 10 + A 18 18 + A 18 23 + A 19 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2087 A h + (pivot_659 A h + pivot_631 A h))

lemma pivot_548 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 16 + A 11 16 + A 14 16 + A 15 16 + A 18 8 + A 19 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2088 A h + (pivot_660 A h + pivot_632 A h))

lemma pivot_551 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 19 + A 11 19 + A 14 19 + A 15 19 + A 18 18 + A 18 22 + A 18 23 + A 19 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2091 A h + (pivot_663 A h + pivot_635 A h))

lemma pivot_69 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 8 + A 2 12 + A 2 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2190 A h + pivot_621 A h) + (pivot_616 A h + pivot_538 A h)) + ((pivot_398 A h + pivot_314 A h) + (pivot_206 A h + pivot_196 A h)))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_59 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 2 + A 0 3 + A 0 5 + A 0 24 + A 0 25 + A 2 0 + A 2 2 + A 2 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_2195 A h + pivot_639 A h) + (pivot_638 A h + (pivot_635 A h + pivot_634 A h))) + ((pivot_631 A h + pivot_630 A h) + (pivot_626 A h + (pivot_616 A h + pivot_543 A h)))) + (((pivot_403 A h + pivot_319 A h) + (pivot_203 A h + (pivot_195 A h + pivot_194 A h))) + ((pivot_185 A h + (pivot_174 A h + pivot_168 A h)) + (pivot_81 A h + (pivot_80 A h + pivot_61 A h)))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_406 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 1 + A 1 6 + A 1 17 + A 1 26 + A 2 0 + A 2 2 + A 2 5 + A 2 25 + A 10 10 + A 10 14 + A 10 18 + A 10 22 + A 11 14 + A 14 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2198 A h + pivot_638 A h) + (pivot_634 A h + (pivot_626 A h + pivot_616 A h))) + ((pivot_546 A h + pivot_526 A h) + (pivot_522 A h + (pivot_514 A h + pivot_434 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_407 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 1 + A 1 6 + A 1 17 + A 1 27 + A 2 0 + A 2 3 + A 2 5 + A 2 24 + A 10 10 + A 10 15 + A 10 18 + A 10 23 + A 11 15 + A 14 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2199 A h + pivot_639 A h) + (pivot_634 A h + (pivot_626 A h + pivot_616 A h))) + ((pivot_547 A h + pivot_527 A h) + (pivot_522 A h + (pivot_514 A h + pivot_435 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_68 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 9 + A 2 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2210 A h + pivot_641 A h) + (pivot_618 A h + (pivot_616 A h + pivot_558 A h))) + ((pivot_418 A h + (pivot_334 A h + pivot_218 A h)) + (pivot_214 A h + (pivot_206 A h + pivot_72 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_349 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 + A 1 6 + A 1 9 + A 1 18 + A 2 5 + A 3 0 + A 9 0 + A 9 9 + A 12 8 + A 12 12 + A 12 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2246 A h + pivot_762 A h) + (pivot_677 A h + (pivot_672 A h + pivot_654 A h))) + ((pivot_577 A h + (pivot_569 A h + pivot_561 A h)) + (pivot_560 A h + (pivot_485 A h + pivot_476 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_339 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 22 + A 0 23 + A 1 6 + A 1 11 + A 1 18 + A 1 26 + A 1 27 + A 2 10 + A 2 22 + A 2 23 + A 3 14 + A 3 15 + A 3 18 + A 3 19 + A 9 0 + A 9 6 + A 9 26 + A 9 27 + A 12 0 + A 12 2 + A 12 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_2251 A h + pivot_767 A h) + (pivot_695 A h + (pivot_694 A h + pivot_691 A h))) + ((pivot_690 A h + (pivot_687 A h + pivot_686 A h)) + (pivot_682 A h + (pivot_651 A h + pivot_587 A h)))) + (((pivot_586 A h + pivot_577 A h) + (pivot_566 A h + (pivot_560 A h + pivot_503 A h))) + ((pivot_502 A h + (pivot_482 A h + pivot_476 A h)) + (pivot_361 A h + (pivot_360 A h + pivot_341 A h)))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_338 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 22 + A 1 6 + A 1 14 + A 1 18 + A 1 26 + A 2 10 + A 2 22 + A 3 10 + A 3 22 + A 9 0 + A 9 6 + A 9 26 + A 12 0 + A 12 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2254 A h + (pivot_770 A h + pivot_694 A h)) + ((pivot_690 A h + pivot_682 A h) + (pivot_586 A h + pivot_577 A h))) + ((pivot_566 A h + (pivot_560 A h + pivot_502 A h)) + ((pivot_482 A h + pivot_476 A h) + (pivot_361 A h + pivot_341 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_336 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 1 6 + A 1 11 + A 1 14 + A 1 15 + A 1 18 + A 2 10 + A 3 14 + A 3 15 + A 3 18 + A 3 19 + A 3 22 + A 3 23 + A 9 0 + A 9 6 + A 12 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_2255 A h + pivot_771 A h) + (pivot_695 A h + pivot_690 A h)) + ((pivot_682 A h + pivot_587 A h) + (pivot_577 A h + pivot_566 A h))) + (((pivot_560 A h + pivot_503 A h) + (pivot_482 A h + pivot_476 A h)) + ((pivot_360 A h + pivot_341 A h) + (pivot_339 A h + pivot_338 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_348 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 25 + A 1 17 + A 1 21 + A 1 26 + A 2 0 + A 2 25 + A 3 0 + A 3 2 + A 9 17 + A 9 21 + A 12 9 + A 12 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2266 A h + (pivot_782 A h + pivot_697 A h)) + (pivot_674 A h + (pivot_666 A h + pivot_581 A h))) + ((pivot_577 A h + (pivot_561 A h + pivot_560 A h)) + (pivot_497 A h + (pivot_476 A h + pivot_352 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_132 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 0 + A 0 10 + A 0 22 + A 1 6 + A 1 14 + A 1 17 + A 1 26 + A 2 0 + A 2 10 + A 2 22 + A 3 0 + A 3 10 + A 3 22 + A 4 4 + A 4 8 + A 4 12 + A 4 13 + A 4 16 + A 4 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((((equation_2282 A h + pivot_742 A h) + (pivot_722 A h + (pivot_718 A h + pivot_710 A h))) + ((pivot_614 A h + pivot_605 A h) + (pivot_594 A h + (pivot_588 A h + pivot_586 A h)))) + (((pivot_566 A h + pivot_560 A h) + (pivot_474 A h + (pivot_454 A h + pivot_448 A h))) + ((pivot_390 A h + pivot_381 A h) + (pivot_370 A h + (pivot_362 A h + pivot_361 A h))))) + ((((pivot_353 A h + pivot_342 A h) + (pivot_341 A h + (pivot_338 A h + pivot_278 A h))) + ((pivot_269 A h + pivot_258 A h) + (pivot_249 A h + (pivot_245 A h + pivot_244 A h)))) + (((pivot_240 A h + pivot_237 A h) + (pivot_236 A h + (pivot_233 A h + pivot_232 A h))) + ((pivot_229 A h + (pivot_226 A h + pivot_224 A h)) + (pivot_162 A h + (pivot_158 A h + pivot_133 A h))))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_121 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 22 + A 0 23 + A 1 14 + A 1 15 + A 1 26 + A 1 27 + A 2 22 + A 2 23 + A 3 22 + A 3 23 + A 4 8 + A 4 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((((equation_2283 A h + (pivot_743 A h + pivot_723 A h)) + (pivot_718 A h + (pivot_710 A h + pivot_615 A h))) + ((pivot_605 A h + (pivot_594 A h + pivot_588 A h)) + (pivot_587 A h + (pivot_566 A h + pivot_560 A h)))) + (((pivot_475 A h + (pivot_454 A h + pivot_448 A h)) + (pivot_391 A h + (pivot_381 A h + pivot_370 A h))) + ((pivot_363 A h + (pivot_360 A h + pivot_353 A h)) + ((pivot_342 A h + pivot_341 A h) + (pivot_339 A h + pivot_338 A h))))) + ((((pivot_336 A h + (pivot_279 A h + pivot_269 A h)) + (pivot_258 A h + (pivot_248 A h + pivot_245 A h))) + ((pivot_244 A h + (pivot_240 A h + pivot_237 A h)) + (pivot_236 A h + (pivot_233 A h + pivot_232 A h)))) + (((pivot_229 A h + (pivot_227 A h + pivot_224 A h)) + (pivot_163 A h + (pivot_162 A h + pivot_159 A h))) + ((pivot_155 A h + (pivot_154 A h + pivot_150 A h)) + ((pivot_132 A h + pivot_128 A h) + (pivot_125 A h + pivot_124 A h))))))

lemma pivot_147 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_2359 A h

lemma pivot_43 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 11 + A 0 18 + A 0 19 + A 0 22 + A 0 23 + A 1 10 + A 1 11 + A 1 14 + A 1 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2362 A h + (pivot_150 A h + pivot_140 A h))

lemma pivot_19 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 11 + A 0 14 + A 0 15 + A 0 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_2370 A h + (pivot_158 A h + pivot_140 A h)) + ((pivot_38 A h + pivot_34 A h) + (pivot_23 A h + pivot_22 A h)))

lemma pivot_42 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 15 + A 0 19 + A 1 10 + A 1 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_2374 A h + pivot_162 A h) + (pivot_158 A h + (pivot_150 A h + pivot_43 A h)))

lemma pivot_15 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 14 + A 0 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2390 A h + pivot_43 A h) + (pivot_38 A h + pivot_34 A h)) + ((pivot_23 A h + pivot_22 A h) + (pivot_19 A h + pivot_18 A h)))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_14 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 + A 0 11 + A 0 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2402 A h + (pivot_47 A h + pivot_46 A h)) + (pivot_45 A h + (pivot_43 A h + pivot_42 A h))) + ((pivot_38 A h + (pivot_34 A h + pivot_23 A h)) + (pivot_22 A h + (pivot_18 A h + pivot_15 A h))))

lemma pivot_355 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 10 + A 8 14 + A 8 15 + A 8 18 + A 8 19 + A 8 22 + A 8 23 + A 12 10 + A 12 11 + A 12 14 + A 12 15 + A 12 18 + A 12 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((equation_2415 A h + pivot_707 A h) + (pivot_599 A h + pivot_571 A h)) + ((pivot_459 A h + pivot_375 A h) + (pivot_359 A h + pivot_358 A h)))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_75 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 6 + A 1 14 + A 1 15 + A 1 17 + A 1 26 + A 1 27 + A 2 10 + A 2 11 + A 2 18 + A 2 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_2418 A h + (pivot_710 A h + pivot_594 A h)) + (pivot_566 A h + (pivot_454 A h + pivot_370 A h))) + ((pivot_342 A h + (pivot_341 A h + pivot_336 A h)) + ((pivot_258 A h + pivot_252 A h) + (pivot_229 A h + pivot_224 A h)))) + (((pivot_158 A h + (pivot_150 A h + pivot_129 A h)) + ((pivot_121 A h + pivot_120 A h) + (pivot_113 A h + pivot_112 A h))) + ((pivot_103 A h + (pivot_102 A h + pivot_99 A h)) + ((pivot_98 A h + pivot_84 A h) + (pivot_79 A h + pivot_78 A h)))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_71 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 6 + A 1 10 + A 1 14 + A 1 15 + A 1 17 + A 1 18 + A 1 26 + A 1 27 + A 2 14 + A 2 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_2426 A h + pivot_718 A h) + (pivot_605 A h + (pivot_588 A h + pivot_560 A h))) + ((pivot_448 A h + (pivot_381 A h + pivot_353 A h)) + (pivot_269 A h + (pivot_252 A h + pivot_245 A h)))) + (((pivot_244 A h + (pivot_240 A h + pivot_237 A h)) + (pivot_236 A h + (pivot_233 A h + pivot_232 A h))) + ((pivot_158 A h + (pivot_116 A h + pivot_79 A h)) + (pivot_78 A h + (pivot_75 A h + pivot_74 A h)))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_70 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 14 + A 2 10 + A 2 11 + A 2 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((((equation_2430 A h + pivot_722 A h) + (pivot_614 A h + pivot_586 A h)) + ((pivot_474 A h + pivot_390 A h) + (pivot_362 A h + pivot_361 A h))) + (((pivot_338 A h + pivot_336 A h) + (pivot_278 A h + pivot_249 A h)) + ((pivot_226 A h + pivot_162 A h) + (pivot_158 A h + pivot_150 A h)))) + ((((pivot_133 A h + pivot_132 A h) + (pivot_129 A h + pivot_121 A h)) + ((pivot_120 A h + pivot_116 A h) + (pivot_113 A h + pivot_112 A h))) + (((pivot_103 A h + pivot_102 A h) + (pivot_99 A h + pivot_98 A h)) + ((pivot_84 A h + pivot_79 A h) + (pivot_78 A h + (pivot_74 A h + pivot_71 A h))))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
lemma pivot_139 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 + A 1 11 + A 2 7 + A 3 7 + A 4 1 + A 4 6 + A 4 17 + A 4 26 + A 4 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((equation_2443 A h + pivot_679 A h) + (pivot_571 A h + pivot_487 A h)) + ((pivot_359 A h + pivot_358 A h) + (pivot_355 A h + pivot_347 A h))) + (((pivot_263 A h + pivot_247 A h) + (pivot_246 A h + pivot_243 A h)) + ((pivot_242 A h + pivot_239 A h) + (pivot_238 A h + (pivot_234 A h + pivot_147 A h)))))

lemma pivot_118 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 0 + A 4 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_2469 A h

lemma pivot_123 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2474 A h + (pivot_127 A h + pivot_126 A h))

lemma pivot_138 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 + A 1 11 + A 2 7 + A 3 7 + A 4 1 + A 4 3 + A 4 6 + A 4 17 + A 4 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (equation_2488 A h + pivot_139 A h)

lemma pivot_378 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 14 + A 9 11 + A 12 14 + A 13 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_2618 A h

lemma pivot_379 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 15 + A 9 11 + A 12 15 + A 13 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_2619 A h

lemma pivot_351 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 10 + A 12 11 + A 12 14 + A 12 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    equation_2698 A h

lemma pivot_350 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 14 + A 8 15 + A 8 18 + A 8 19 + A 8 23 + A 12 10 + A 12 11 + A 12 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((equation_2710 A h + pivot_355 A h) + (pivot_354 A h + pivot_351 A h))

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
