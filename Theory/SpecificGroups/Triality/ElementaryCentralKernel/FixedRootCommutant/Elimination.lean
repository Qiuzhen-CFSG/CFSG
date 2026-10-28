module
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.Triangular
public import Theory.SpecificGroups.Triality.ElementaryCentralKernel.FixedRootCommutant.NormalForm

/-!
# The five-parameter constant-root commutant

Back substitution in the checked triangular equations leaves the five Cartan
entries (0,0), (0,2), (0,3), (2,0), and (2,2). Each substitution is checked by
characteristic-two ring normalization. The resulting coordinate identities
assemble to the explicit normal form on the full Geck lattice.

Source: the fixed-root parametrizations of GLS3 §2.4.
-/

public section
namespace Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
variable {F : Type*} [CommRing F] [CharP F 2]

private lemma coordinate_1 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 1 = 0 := by
  exact pivot_1 A h

private lemma coordinate_4 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 4 = 0 := by
  exact pivot_4 A h

private lemma coordinate_5 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 5 = 0 := by
  exact pivot_5 A h

private lemma coordinate_6 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 6 = 0 := by
  exact pivot_6 A h

private lemma coordinate_7 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 7 = 0 := by
  exact pivot_7 A h

private lemma coordinate_8 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 8 = 0 := by
  exact pivot_8 A h

private lemma coordinate_9 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 9 = 0 := by
  exact pivot_9 A h

private lemma coordinate_10 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 10 = 0 := by
  exact pivot_10 A h

private lemma coordinate_11 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 11 = 0 := by
  exact pivot_11 A h

private lemma coordinate_12 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_12 A h + coordinate_5 A h) + (coordinate_8 A h + coordinate_9 A h))

private lemma coordinate_13 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_13 A h + (coordinate_8 A h + coordinate_12 A h))

private lemma coordinate_14 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_14 A h + (coordinate_10 A h + coordinate_11 A h))

private lemma coordinate_15 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_15 A h + coordinate_14 A h)

private lemma coordinate_16 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_16 A h + coordinate_8 A h) + (coordinate_9 A h + (coordinate_12 A h + coordinate_13 A h)))

private lemma coordinate_17 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 17 = 0 := by
  exact pivot_17 A h

private lemma coordinate_18 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 18 = 0 := by
  exact pivot_18 A h

private lemma coordinate_19 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_19 A h + coordinate_10 A h) + (coordinate_11 A h + (coordinate_14 A h + coordinate_15 A h)))

private lemma coordinate_20 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 20 = 0 := by
  exact pivot_20 A h

private lemma coordinate_21 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 21 = 0 := by
  exact pivot_21 A h

private lemma coordinate_22 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 22 = 0 := by
  exact pivot_22 A h

private lemma coordinate_23 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 23 = 0 := by
  exact pivot_23 A h

private lemma coordinate_24 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 24 = 0 := by
  exact pivot_24 A h

private lemma coordinate_25 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 25 = 0 := by
  exact pivot_25 A h

private lemma coordinate_26 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 26 = 0 := by
  exact pivot_26 A h

private lemma coordinate_27 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 0 27 = 0 := by
  exact pivot_27 A h

private lemma coordinate_28 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 0 = 0 := by
  exact pivot_28 A h

private lemma coordinate_29 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 1 = A 0 0 + A 0 2 + A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_29 A h + (coordinate_5 A h + coordinate_10 A h)) + ((coordinate_22 A h + coordinate_23 A h) + (coordinate_24 A h + coordinate_25 A h)))

private lemma coordinate_30 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 2 = 0 := by
  exact pivot_30 A h

private lemma coordinate_31 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_31 A h + (coordinate_28 A h + coordinate_30 A h))

private lemma coordinate_32 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_32 A h + coordinate_8 A h)

private lemma coordinate_33 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_33 A h + coordinate_28 A h)

private lemma coordinate_34 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_34 A h + coordinate_10 A h)

private lemma coordinate_35 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 7 = 0 := by
  exact pivot_35 A h

private lemma coordinate_36 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_36 A h + (coordinate_8 A h + coordinate_32 A h))

private lemma coordinate_37 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_37 A h + (coordinate_5 A h + coordinate_33 A h))

private lemma coordinate_38 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_38 A h + (coordinate_10 A h + coordinate_34 A h))

private lemma coordinate_39 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_39 A h + (coordinate_7 A h + coordinate_35 A h))

private lemma coordinate_40 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_40 A h + (coordinate_24 A h + coordinate_25 A h)) + (coordinate_33 A h + (coordinate_36 A h + coordinate_37 A h)))

private lemma coordinate_41 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_41 A h + (coordinate_36 A h + coordinate_40 A h))

private lemma coordinate_42 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_42 A h + coordinate_15 A h) + (coordinate_19 A h + coordinate_38 A h))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_43 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_43 A h + coordinate_10 A h) + (coordinate_11 A h + (coordinate_18 A h + coordinate_19 A h))) + ((coordinate_22 A h + coordinate_23 A h) + (coordinate_38 A h + (coordinate_39 A h + coordinate_42 A h))))

private lemma coordinate_44 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_44 A h + coordinate_24 A h) + (coordinate_25 A h + coordinate_33 A h)) + ((coordinate_36 A h + coordinate_37 A h) + (coordinate_40 A h + coordinate_41 A h)))

private lemma coordinate_45 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_45 A h + coordinate_18 A h)

private lemma coordinate_46 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_46 A h + (coordinate_18 A h + coordinate_45 A h))

private lemma coordinate_47 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_47 A h + coordinate_38 A h) + (coordinate_42 A h + (coordinate_43 A h + coordinate_46 A h)))

private lemma coordinate_48 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_48 A h + coordinate_24 A h) + (coordinate_30 A h + coordinate_33 A h))

private lemma coordinate_49 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_49 A h + coordinate_24 A h) + (coordinate_25 A h + (coordinate_33 A h + coordinate_48 A h)))

private lemma coordinate_50 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_50 A h + (coordinate_38 A h + coordinate_46 A h))

private lemma coordinate_51 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_51 A h + (coordinate_38 A h + coordinate_42 A h)) + ((coordinate_43 A h + coordinate_46 A h) + (coordinate_47 A h + coordinate_50 A h)))

private lemma coordinate_52 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_52 A h + (coordinate_24 A h + coordinate_48 A h))

private lemma coordinate_53 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_53 A h + (coordinate_25 A h + coordinate_49 A h))

private lemma coordinate_54 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_54 A h + (coordinate_22 A h + coordinate_50 A h))

private lemma coordinate_55 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 1 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_55 A h + (coordinate_23 A h + coordinate_51 A h))

private lemma coordinate_57 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 1 = 0 := by
  exact pivot_57 A h

private lemma coordinate_59 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 3 = A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_59 A h + coordinate_5 A h) + (coordinate_24 A h + coordinate_25 A h))

private lemma coordinate_60 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 4 = 0 := by
  exact pivot_60 A h

private lemma coordinate_61 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 5 = 0 := by
  exact pivot_61 A h

private lemma coordinate_62 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 6 = 0 := by
  exact pivot_62 A h

private lemma coordinate_63 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 7 = 0 := by
  exact pivot_63 A h

private lemma coordinate_64 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 8 = 0 := by
  exact pivot_64 A h

private lemma coordinate_65 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 9 = 0 := by
  exact pivot_65 A h

private lemma coordinate_66 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 10 = 0 := by
  exact pivot_66 A h

private lemma coordinate_67 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 11 = 0 := by
  exact pivot_67 A h

private lemma coordinate_68 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_68 A h + coordinate_65 A h)

private lemma coordinate_69 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_69 A h + (coordinate_64 A h + coordinate_68 A h))

private lemma coordinate_70 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_70 A h + coordinate_42 A h) + (coordinate_66 A h + coordinate_67 A h))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_71 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_71 A h + coordinate_34 A h) + (coordinate_38 A h + (coordinate_42 A h + coordinate_43 A h))) + ((coordinate_45 A h + coordinate_46 A h) + (coordinate_54 A h + (coordinate_55 A h + coordinate_70 A h))))

private lemma coordinate_72 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_72 A h + coordinate_64 A h) + (coordinate_65 A h + (coordinate_68 A h + coordinate_69 A h)))

private lemma coordinate_73 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 17 = 0 := by
  exact pivot_73 A h

private lemma coordinate_74 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 18 = 0 := by
  exact pivot_74 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_75 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_75 A h + coordinate_34 A h) + (coordinate_42 A h + (coordinate_43 A h + coordinate_45 A h))) + ((coordinate_54 A h + coordinate_55 A h) + (coordinate_66 A h + (coordinate_67 A h + coordinate_74 A h))))

private lemma coordinate_76 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 20 = 0 := by
  exact pivot_76 A h

private lemma coordinate_77 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 21 = 0 := by
  exact pivot_77 A h

private lemma coordinate_78 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 22 = 0 := by
  exact pivot_78 A h

private lemma coordinate_79 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 23 = 0 := by
  exact pivot_79 A h

private lemma coordinate_80 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 24 = 0 := by
  exact pivot_80 A h

private lemma coordinate_81 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 25 = 0 := by
  exact pivot_81 A h

private lemma coordinate_82 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 26 = 0 := by
  exact pivot_82 A h

private lemma coordinate_83 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 2 27 = 0 := by
  exact pivot_83 A h

private lemma coordinate_84 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 0 = A 0 2 + A 0 3 + A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_84 A h + coordinate_29 A h) + (coordinate_45 A h + coordinate_46 A h))

private lemma coordinate_85 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 1 = 0 := by
  exact pivot_85 A h

private lemma coordinate_86 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 2 = A 0 0 + A 0 3 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_86 A h + coordinate_84 A h)

private lemma coordinate_87 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 3 = A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_87 A h + (coordinate_59 A h + coordinate_84 A h))

private lemma coordinate_88 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 4 = 0 := by
  exact pivot_88 A h

private lemma coordinate_89 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_89 A h + coordinate_5 A h) + (coordinate_33 A h + (coordinate_37 A h + coordinate_61 A h)))

private lemma coordinate_90 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 6 = 0 := by
  exact pivot_90 A h

private lemma coordinate_91 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_91 A h + coordinate_7 A h) + (coordinate_35 A h + (coordinate_39 A h + coordinate_63 A h)))

private lemma coordinate_92 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_92 A h + coordinate_8 A h) + (coordinate_32 A h + (coordinate_36 A h + coordinate_64 A h)))

private lemma coordinate_93 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 9 = 0 := by
  exact pivot_93 A h

private lemma coordinate_94 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_94 A h + coordinate_10 A h) + (coordinate_34 A h + (coordinate_38 A h + coordinate_66 A h)))

private lemma coordinate_95 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 11 = 0 := by
  exact pivot_95 A h

private lemma coordinate_96 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_96 A h + (coordinate_12 A h + coordinate_68 A h))

private lemma coordinate_97 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_97 A h + (coordinate_13 A h + coordinate_69 A h))

private lemma coordinate_98 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_98 A h + (coordinate_14 A h + coordinate_70 A h))

private lemma coordinate_99 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_99 A h + (coordinate_15 A h + coordinate_71 A h))

private lemma coordinate_100 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_100 A h + (coordinate_16 A h + coordinate_72 A h))

private lemma coordinate_101 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 17 = 0 := by
  exact pivot_101 A h

private lemma coordinate_102 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_102 A h + coordinate_18 A h) + (coordinate_29 A h + (coordinate_74 A h + coordinate_84 A h)))

private lemma coordinate_103 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_103 A h + (coordinate_19 A h + coordinate_75 A h))

private lemma coordinate_104 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 20 = 0 := by
  exact pivot_104 A h

private lemma coordinate_105 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 21 = 0 := by
  exact pivot_105 A h

private lemma coordinate_106 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_106 A h + coordinate_22 A h) + (coordinate_50 A h + (coordinate_54 A h + coordinate_78 A h)))

private lemma coordinate_107 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_107 A h + coordinate_23 A h) + (coordinate_51 A h + (coordinate_55 A h + coordinate_79 A h)))

private lemma coordinate_108 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_108 A h + coordinate_24 A h) + (coordinate_48 A h + (coordinate_52 A h + coordinate_80 A h)))

private lemma coordinate_109 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_109 A h + coordinate_25 A h) + (coordinate_49 A h + (coordinate_53 A h + coordinate_81 A h)))

private lemma coordinate_110 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 26 = 0 := by
  exact pivot_110 A h

private lemma coordinate_111 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 3 27 = 0 := by
  exact pivot_111 A h

private lemma coordinate_112 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 0 = 0 := by
  exact pivot_112 A h

private lemma coordinate_113 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 1 = 0 := by
  exact pivot_113 A h

private lemma coordinate_114 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_114 A h + coordinate_112 A h)

private lemma coordinate_115 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_115 A h + coordinate_112 A h)

private lemma coordinate_116 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 4 = A 0 0 + A 0 2 + A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_116 A h + coordinate_38 A h) + (coordinate_45 A h + coordinate_84 A h))

private lemma coordinate_117 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 5 = 0 := by
  exact pivot_117 A h

private lemma coordinate_118 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_118 A h + coordinate_112 A h)

private lemma coordinate_119 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 7 = 0 := by
  exact pivot_119 A h

private lemma coordinate_120 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 8 = 0 := by
  exact pivot_120 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_121 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_121 A h + (coordinate_22 A h + coordinate_23 A h)) + (coordinate_42 A h + (coordinate_43 A h + coordinate_54 A h))) + ((coordinate_55 A h + (coordinate_78 A h + coordinate_79 A h)) + (coordinate_106 A h + (coordinate_107 A h + coordinate_120 A h))))

private lemma coordinate_122 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 10 = 0 := by
  exact pivot_122 A h

private lemma coordinate_123 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 11 = 0 := by
  exact pivot_123 A h

private lemma coordinate_124 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 12 = 0 := by
  exact pivot_124 A h

private lemma coordinate_125 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 13 = 0 := by
  exact pivot_125 A h

private lemma coordinate_126 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 14 = 0 := by
  exact pivot_126 A h

private lemma coordinate_127 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 15 = 0 := by
  exact pivot_127 A h

private lemma coordinate_128 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 16 = 0 := by
  exact pivot_128 A h

private lemma coordinate_129 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_129 A h + (coordinate_112 A h + coordinate_113 A h))

private lemma coordinate_130 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 18 = 0 := by
  exact pivot_130 A h

private lemma coordinate_131 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 19 = 0 := by
  exact pivot_131 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_132 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((pivot_132 A h + coordinate_10 A h) + (coordinate_22 A h + coordinate_34 A h)) + ((coordinate_42 A h + coordinate_45 A h) + (coordinate_54 A h + coordinate_66 A h))) + (((coordinate_78 A h + coordinate_84 A h) + (coordinate_94 A h + coordinate_106 A h)) + ((coordinate_116 A h + coordinate_120 A h) + (coordinate_124 A h + (coordinate_125 A h + coordinate_128 A h)))))

private lemma coordinate_133 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_133 A h + (coordinate_120 A h + coordinate_121 A h)) + ((coordinate_124 A h + coordinate_125 A h) + (coordinate_128 A h + coordinate_132 A h)))

private lemma coordinate_134 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 22 = 0 := by
  exact pivot_134 A h

private lemma coordinate_135 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 23 = 0 := by
  exact pivot_135 A h

private lemma coordinate_136 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 24 = 0 := by
  exact pivot_136 A h

private lemma coordinate_137 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 25 = 0 := by
  exact pivot_137 A h

private lemma coordinate_138 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_138 A h + coordinate_7 A h) + (coordinate_39 A h + coordinate_63 A h)) + ((coordinate_91 A h + coordinate_113 A h) + (coordinate_115 A h + (coordinate_118 A h + coordinate_129 A h))))

private lemma coordinate_139 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 4 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_139 A h + coordinate_7 A h) + (coordinate_39 A h + coordinate_63 A h)) + ((coordinate_91 A h + coordinate_113 A h) + (coordinate_118 A h + (coordinate_129 A h + coordinate_138 A h))))

private lemma coordinate_140 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_140 A h + coordinate_38 A h)

private lemma coordinate_141 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 1 = 0 := by
  exact pivot_141 A h

private lemma coordinate_142 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_142 A h + coordinate_140 A h)

private lemma coordinate_143 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_143 A h + coordinate_140 A h)

private lemma coordinate_144 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 4 = 0 := by
  exact pivot_144 A h

private lemma coordinate_145 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 5 = A 0 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_145 A h + coordinate_5 A h) + (coordinate_34 A h + coordinate_140 A h))

private lemma coordinate_146 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 6 = 0 := by
  exact pivot_146 A h

private lemma coordinate_147 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 7 = 0 := by
  exact pivot_147 A h

private lemma coordinate_148 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_148 A h + coordinate_8 A h) + (coordinate_12 A h + (coordinate_13 A h + coordinate_37 A h)))

private lemma coordinate_149 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 9 = 0 := by
  exact pivot_149 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_150 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_150 A h + (coordinate_10 A h + coordinate_14 A h)) + (coordinate_15 A h + (coordinate_18 A h + coordinate_19 A h))) + ((coordinate_22 A h + (coordinate_23 A h + coordinate_39 A h)) + (coordinate_42 A h + (coordinate_43 A h + coordinate_140 A h))))

private lemma coordinate_151 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 11 = 0 := by
  exact pivot_151 A h

private lemma coordinate_152 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 12 = 0 := by
  exact pivot_152 A h

private lemma coordinate_153 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 13 = 0 := by
  exact pivot_153 A h

private lemma coordinate_154 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 14 = 0 := by
  exact pivot_154 A h

private lemma coordinate_155 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 15 = 0 := by
  exact pivot_155 A h

private lemma coordinate_156 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 16 = 0 := by
  exact pivot_156 A h

private lemma coordinate_157 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 17 = 0 := by
  exact pivot_157 A h

private lemma coordinate_158 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_158 A h + coordinate_140 A h)

private lemma coordinate_159 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 19 = 0 := by
  exact pivot_159 A h

private lemma coordinate_160 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 20 = 0 := by
  exact pivot_160 A h

private lemma coordinate_161 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 21 = 0 := by
  exact pivot_161 A h

private lemma coordinate_162 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_162 A h + coordinate_42 A h) + (coordinate_150 A h + coordinate_158 A h))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_163 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_163 A h + (coordinate_10 A h + coordinate_14 A h)) + ((coordinate_15 A h + coordinate_18 A h) + (coordinate_19 A h + coordinate_22 A h))) + (((coordinate_23 A h + coordinate_39 A h) + (coordinate_150 A h + coordinate_154 A h)) + ((coordinate_155 A h + coordinate_158 A h) + (coordinate_159 A h + coordinate_162 A h))))

private lemma coordinate_164 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 24 = A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_164 A h + (coordinate_25 A h + coordinate_29 A h)) + (coordinate_54 A h + (coordinate_142 A h + coordinate_145 A h)))

private lemma coordinate_165 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 25 = A 0 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_165 A h + coordinate_29 A h) + (coordinate_145 A h + coordinate_164 A h))

private lemma coordinate_166 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 26 = 0 := by
  exact pivot_166 A h

private lemma coordinate_167 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 5 27 = 0 := by
  exact pivot_167 A h

private lemma coordinate_168 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 0 = 0 := by
  exact pivot_168 A h

private lemma coordinate_169 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 1 = 0 := by
  exact pivot_169 A h

private lemma coordinate_170 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_170 A h + coordinate_168 A h)

private lemma coordinate_171 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_171 A h + coordinate_168 A h)

private lemma coordinate_172 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 4 = 0 := by
  exact pivot_172 A h

private lemma coordinate_173 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 5 = 0 := by
  exact pivot_173 A h

private lemma coordinate_174 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 6 = A 0 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_174 A h + coordinate_5 A h)

private lemma coordinate_175 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 7 = 0 := by
  exact pivot_175 A h

private lemma coordinate_176 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 8 = 0 := by
  exact pivot_176 A h

private lemma coordinate_177 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_177 A h + coordinate_8 A h) + (coordinate_12 A h + coordinate_13 A h))

private lemma coordinate_178 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 10 = 0 := by
  exact pivot_178 A h

private lemma coordinate_179 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_179 A h + coordinate_10 A h) + (coordinate_14 A h + coordinate_15 A h)) + ((coordinate_18 A h + coordinate_19 A h) + (coordinate_22 A h + coordinate_23 A h)))

private lemma coordinate_180 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 12 = 0 := by
  exact pivot_180 A h

private lemma coordinate_181 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 13 = 0 := by
  exact pivot_181 A h

private lemma coordinate_182 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 14 = 0 := by
  exact pivot_182 A h

private lemma coordinate_183 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 15 = 0 := by
  exact pivot_183 A h

private lemma coordinate_184 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 16 = 0 := by
  exact pivot_184 A h

private lemma coordinate_185 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_185 A h + (coordinate_168 A h + coordinate_169 A h))

private lemma coordinate_186 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 18 = 0 := by
  exact pivot_186 A h

private lemma coordinate_187 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 19 = 0 := by
  exact pivot_187 A h

private lemma coordinate_188 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_188 A h + coordinate_8 A h) + (coordinate_12 A h + coordinate_16 A h))

private lemma coordinate_189 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_189 A h + coordinate_8 A h) + (coordinate_13 A h + coordinate_16 A h))

private lemma coordinate_190 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 22 = 0 := by
  exact pivot_190 A h

private lemma coordinate_191 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 23 = 0 := by
  exact pivot_191 A h

private lemma coordinate_192 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 24 = 0 := by
  exact pivot_192 A h

private lemma coordinate_193 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 25 = 0 := by
  exact pivot_193 A h

private lemma coordinate_194 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 26 = A 0 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_194 A h + coordinate_25 A h)

private lemma coordinate_195 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 6 27 = A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_195 A h + coordinate_24 A h)

private lemma coordinate_196 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 0 = 0 := by
  exact pivot_196 A h

private lemma coordinate_197 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 1 = 0 := by
  exact pivot_197 A h

private lemma coordinate_198 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_198 A h + coordinate_196 A h)

private lemma coordinate_199 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_199 A h + coordinate_196 A h)

private lemma coordinate_200 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 4 = 0 := by
  exact pivot_200 A h

private lemma coordinate_201 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_201 A h + coordinate_196 A h)

private lemma coordinate_202 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 6 = 0 := by
  exact pivot_202 A h

private lemma coordinate_203 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 7 = A 0 0 + A 0 2 + A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_203 A h + (coordinate_169 A h + coordinate_174 A h)) + (coordinate_185 A h + (coordinate_194 A h + coordinate_195 A h)))

private lemma coordinate_204 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 8 = 0 := by
  exact pivot_204 A h

private lemma coordinate_205 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 9 = 0 := by
  exact pivot_205 A h

private lemma coordinate_206 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_206 A h + coordinate_196 A h)

private lemma coordinate_207 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 11 = 0 := by
  exact pivot_207 A h

private lemma coordinate_208 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 12 = 0 := by
  exact pivot_208 A h

private lemma coordinate_209 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 13 = 0 := by
  exact pivot_209 A h

private lemma coordinate_210 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 14 = 0 := by
  exact pivot_210 A h

private lemma coordinate_211 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 15 = 0 := by
  exact pivot_211 A h

private lemma coordinate_212 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 16 = 0 := by
  exact pivot_212 A h

private lemma coordinate_213 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 17 = 0 := by
  exact pivot_213 A h

private lemma coordinate_214 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_214 A h + coordinate_196 A h)

private lemma coordinate_215 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 19 = 0 := by
  exact pivot_215 A h

private lemma coordinate_216 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 20 = 0 := by
  exact pivot_216 A h

private lemma coordinate_217 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 21 = 0 := by
  exact pivot_217 A h

private lemma coordinate_218 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_218 A h + (coordinate_206 A h + coordinate_214 A h))

private lemma coordinate_219 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_219 A h + (coordinate_206 A h + coordinate_210 A h)) + ((coordinate_211 A h + coordinate_214 A h) + (coordinate_215 A h + coordinate_218 A h)))

private lemma coordinate_220 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_220 A h + (coordinate_198 A h + coordinate_201 A h))

private lemma coordinate_221 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_221 A h + (coordinate_201 A h + coordinate_220 A h))

private lemma coordinate_222 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 26 = 0 := by
  exact pivot_222 A h

private lemma coordinate_223 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 7 27 = 0 := by
  exact pivot_223 A h

private lemma coordinate_224 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_224 A h + coordinate_129 A h)

private lemma coordinate_225 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 1 = 0 := by
  exact pivot_225 A h

private lemma coordinate_226 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_226 A h + coordinate_129 A h)

private lemma coordinate_227 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_227 A h + coordinate_129 A h)

private lemma coordinate_228 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 4 = 0 := by
  exact pivot_228 A h

private lemma coordinate_229 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_229 A h + coordinate_121 A h)

private lemma coordinate_230 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 6 = 0 := by
  exact pivot_230 A h

private lemma coordinate_231 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_231 A h + coordinate_123 A h)

private lemma coordinate_232 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 8 = A 0 0 + A 0 2 + A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_232 A h + coordinate_116 A h)

private lemma coordinate_233 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 9 = 0 := by
  exact pivot_233 A h

private lemma coordinate_234 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_234 A h + coordinate_118 A h)

private lemma coordinate_235 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 11 = 0 := by
  exact pivot_235 A h

private lemma coordinate_236 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 12 = 0 := by
  exact pivot_236 A h

private lemma coordinate_237 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 13 = 0 := by
  exact pivot_237 A h

private lemma coordinate_238 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 14 = 0 := by
  exact pivot_238 A h

private lemma coordinate_239 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 15 = 0 := by
  exact pivot_239 A h

private lemma coordinate_240 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 16 = 0 := by
  exact pivot_240 A h

private lemma coordinate_241 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 17 = 0 := by
  exact pivot_241 A h

private lemma coordinate_242 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_242 A h + (coordinate_113 A h + coordinate_129 A h))

private lemma coordinate_243 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 19 = 0 := by
  exact pivot_243 A h

private lemma coordinate_244 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 20 = 0 := by
  exact pivot_244 A h

private lemma coordinate_245 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 21 = 0 := by
  exact pivot_245 A h

private lemma coordinate_246 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_246 A h + coordinate_138 A h)

private lemma coordinate_247 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_247 A h + coordinate_139 A h)

private lemma coordinate_248 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_248 A h + coordinate_132 A h)

private lemma coordinate_249 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_249 A h + coordinate_133 A h)

private lemma coordinate_250 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 26 = 0 := by
  exact pivot_250 A h

private lemma coordinate_251 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 8 27 = 0 := by
  exact pivot_251 A h

private lemma coordinate_252 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_252 A h + coordinate_158 A h)

private lemma coordinate_253 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_253 A h + (coordinate_140 A h + coordinate_158 A h))

private lemma coordinate_254 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_254 A h + coordinate_158 A h)

private lemma coordinate_255 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_255 A h + coordinate_158 A h)

private lemma coordinate_256 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_256 A h + coordinate_148 A h)

private lemma coordinate_257 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 5 = 0 := by
  exact pivot_257 A h

private lemma coordinate_258 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_258 A h + coordinate_150 A h)

private lemma coordinate_259 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 7 = 0 := by
  exact pivot_259 A h

private lemma coordinate_260 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 8 = 0 := by
  exact pivot_260 A h

private lemma coordinate_261 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 9 = A 0 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_261 A h + coordinate_145 A h)

private lemma coordinate_262 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 10 = 0 := by
  exact pivot_262 A h

private lemma coordinate_263 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_263 A h + coordinate_147 A h)

private lemma coordinate_264 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 12 = 0 := by
  exact pivot_264 A h

private lemma coordinate_265 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 13 = 0 := by
  exact pivot_265 A h

private lemma coordinate_266 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 14 = 0 := by
  exact pivot_266 A h

private lemma coordinate_267 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 15 = 0 := by
  exact pivot_267 A h

private lemma coordinate_268 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 16 = 0 := by
  exact pivot_268 A h

private lemma coordinate_269 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_269 A h + coordinate_140 A h)

private lemma coordinate_270 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 18 = 0 := by
  exact pivot_270 A h

private lemma coordinate_271 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 19 = 0 := by
  exact pivot_271 A h

private lemma coordinate_272 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 20 = A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_272 A h + coordinate_164 A h)

private lemma coordinate_273 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 21 = A 0 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_273 A h + coordinate_165 A h)

private lemma coordinate_274 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 22 = 0 := by
  exact pivot_274 A h

private lemma coordinate_275 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 23 = 0 := by
  exact pivot_275 A h

private lemma coordinate_276 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 24 = 0 := by
  exact pivot_276 A h

private lemma coordinate_277 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 25 = 0 := by
  exact pivot_277 A h

private lemma coordinate_278 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_278 A h + coordinate_162 A h)

private lemma coordinate_279 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 9 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_279 A h + coordinate_163 A h)

private lemma coordinate_280 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_280 A h + coordinate_185 A h)

private lemma coordinate_281 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 1 = 0 := by
  exact pivot_281 A h

private lemma coordinate_282 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_282 A h + coordinate_185 A h)

private lemma coordinate_283 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_283 A h + coordinate_185 A h)

private lemma coordinate_284 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 4 = 0 := by
  exact pivot_284 A h

private lemma coordinate_285 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_285 A h + coordinate_177 A h)

private lemma coordinate_286 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 6 = 0 := by
  exact pivot_286 A h

private lemma coordinate_287 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_287 A h + coordinate_179 A h)

private lemma coordinate_288 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_288 A h + coordinate_172 A h)

private lemma coordinate_289 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 9 = 0 := by
  exact pivot_289 A h

private lemma coordinate_290 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 10 = A 0 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_290 A h + coordinate_174 A h)

private lemma coordinate_291 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 11 = 0 := by
  exact pivot_291 A h

private lemma coordinate_292 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 12 = 0 := by
  exact pivot_292 A h

private lemma coordinate_293 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 13 = 0 := by
  exact pivot_293 A h

private lemma coordinate_294 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 14 = 0 := by
  exact pivot_294 A h

private lemma coordinate_295 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 15 = 0 := by
  exact pivot_295 A h

private lemma coordinate_296 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 16 = 0 := by
  exact pivot_296 A h

private lemma coordinate_297 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 17 = 0 := by
  exact pivot_297 A h

private lemma coordinate_298 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_298 A h + (coordinate_169 A h + coordinate_185 A h))

private lemma coordinate_299 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 19 = 0 := by
  exact pivot_299 A h

private lemma coordinate_300 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 20 = 0 := by
  exact pivot_300 A h

private lemma coordinate_301 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 21 = 0 := by
  exact pivot_301 A h

private lemma coordinate_302 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 22 = A 0 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_302 A h + coordinate_194 A h)

private lemma coordinate_303 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 23 = A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_303 A h + coordinate_195 A h)

private lemma coordinate_304 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_304 A h + coordinate_188 A h)

private lemma coordinate_305 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_305 A h + coordinate_189 A h)

private lemma coordinate_306 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 26 = 0 := by
  exact pivot_306 A h

private lemma coordinate_307 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 10 27 = 0 := by
  exact pivot_307 A h

private lemma coordinate_308 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_308 A h + coordinate_214 A h)

private lemma coordinate_309 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_309 A h + (coordinate_196 A h + coordinate_214 A h))

private lemma coordinate_310 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_310 A h + coordinate_214 A h)

private lemma coordinate_311 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_311 A h + coordinate_214 A h)

private lemma coordinate_312 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_312 A h + coordinate_204 A h)

private lemma coordinate_313 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 5 = 0 := by
  exact pivot_313 A h

private lemma coordinate_314 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_314 A h + coordinate_206 A h)

private lemma coordinate_315 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 7 = 0 := by
  exact pivot_315 A h

private lemma coordinate_316 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 8 = 0 := by
  exact pivot_316 A h

private lemma coordinate_317 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_317 A h + coordinate_201 A h)

private lemma coordinate_318 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 10 = 0 := by
  exact pivot_318 A h

private lemma coordinate_319 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 11 = A 0 0 + A 0 2 + A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_319 A h + coordinate_203 A h)

private lemma coordinate_320 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 12 = 0 := by
  exact pivot_320 A h

private lemma coordinate_321 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 13 = 0 := by
  exact pivot_321 A h

private lemma coordinate_322 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 14 = 0 := by
  exact pivot_322 A h

private lemma coordinate_323 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 15 = 0 := by
  exact pivot_323 A h

private lemma coordinate_324 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 16 = 0 := by
  exact pivot_324 A h

private lemma coordinate_325 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_325 A h + coordinate_196 A h)

private lemma coordinate_326 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 18 = 0 := by
  exact pivot_326 A h

private lemma coordinate_327 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 19 = 0 := by
  exact pivot_327 A h

private lemma coordinate_328 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_328 A h + coordinate_220 A h)

private lemma coordinate_329 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_329 A h + coordinate_221 A h)

private lemma coordinate_330 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 22 = 0 := by
  exact pivot_330 A h

private lemma coordinate_331 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 23 = 0 := by
  exact pivot_331 A h

private lemma coordinate_332 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 24 = 0 := by
  exact pivot_332 A h

private lemma coordinate_333 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 25 = 0 := by
  exact pivot_333 A h

private lemma coordinate_334 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_334 A h + coordinate_218 A h)

private lemma coordinate_335 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 11 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_335 A h + coordinate_219 A h)

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_336 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((pivot_336 A h + coordinate_10 A h) + (coordinate_34 A h + coordinate_39 A h)) + ((coordinate_42 A h + coordinate_43 A h) + (coordinate_46 A h + coordinate_66 A h))) + (((coordinate_98 A h + coordinate_99 A h) + (coordinate_102 A h + coordinate_103 A h)) + ((coordinate_106 A h + coordinate_107 A h) + (coordinate_252 A h + coordinate_258 A h))))

private lemma coordinate_337 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 1 = 0 := by
  exact pivot_337 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_338 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_338 A h + (coordinate_10 A h + coordinate_22 A h)) + ((coordinate_34 A h + coordinate_42 A h) + (coordinate_46 A h + coordinate_54 A h))) + (((coordinate_66 A h + coordinate_78 A h) + (coordinate_94 A h + coordinate_106 A h)) + ((coordinate_252 A h + coordinate_258 A h) + (coordinate_278 A h + coordinate_336 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_339 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((pivot_339 A h + coordinate_10 A h) + (coordinate_22 A h + (coordinate_23 A h + coordinate_34 A h))) + ((coordinate_39 A h + (coordinate_46 A h + coordinate_54 A h)) + (coordinate_55 A h + (coordinate_66 A h + coordinate_78 A h)))) + (((coordinate_79 A h + coordinate_98 A h) + (coordinate_99 A h + (coordinate_102 A h + coordinate_103 A h))) + ((coordinate_252 A h + (coordinate_258 A h + coordinate_278 A h)) + (coordinate_279 A h + (coordinate_336 A h + coordinate_338 A h)))))

private lemma coordinate_340 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 4 = 0 := by
  exact pivot_340 A h

private lemma coordinate_341 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 5 = 0 := by
  exact pivot_341 A h

private lemma coordinate_342 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 6 = 0 := by
  exact pivot_342 A h

private lemma coordinate_343 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 7 = 0 := by
  exact pivot_343 A h

private lemma coordinate_344 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 8 = 0 := by
  exact pivot_344 A h

private lemma coordinate_345 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 9 = 0 := by
  exact pivot_345 A h

private lemma coordinate_346 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 10 = 0 := by
  exact pivot_346 A h

private lemma coordinate_347 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 11 = 0 := by
  exact pivot_347 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_348 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 12 = A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_348 A h + coordinate_25 A h) + (coordinate_45 A h + (coordinate_49 A h + coordinate_54 A h))) + ((coordinate_81 A h + (coordinate_84 A h + coordinate_86 A h)) + (coordinate_269 A h + (coordinate_273 A h + coordinate_345 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_349 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 13 = A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_349 A h + coordinate_5 A h) + (coordinate_34 A h + (coordinate_37 A h + coordinate_46 A h))) + ((coordinate_61 A h + (coordinate_84 A h + coordinate_252 A h)) + (coordinate_261 A h + (coordinate_344 A h + coordinate_348 A h))))

private lemma coordinate_350 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_350 A h + coordinate_238 A h) + (coordinate_239 A h + coordinate_242 A h)) + ((coordinate_243 A h + coordinate_247 A h) + (coordinate_346 A h + coordinate_347 A h)))

private lemma coordinate_351 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_351 A h + coordinate_234 A h) + (coordinate_347 A h + coordinate_350 A h))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_352 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 16 = A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_352 A h + coordinate_45 A h) + (coordinate_46 A h + (coordinate_84 A h + coordinate_252 A h))) + ((coordinate_269 A h + coordinate_344 A h) + (coordinate_345 A h + (coordinate_348 A h + coordinate_349 A h))))

private lemma coordinate_353 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 17 = 0 := by
  exact pivot_353 A h

private lemma coordinate_354 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 18 = 0 := by
  exact pivot_354 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_355 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_355 A h + (coordinate_234 A h + coordinate_238 A h)) + (coordinate_239 A h + (coordinate_242 A h + coordinate_243 A h))) + ((coordinate_246 A h + (coordinate_247 A h + coordinate_346 A h)) + ((coordinate_347 A h + coordinate_350 A h) + (coordinate_351 A h + coordinate_354 A h))))

private lemma coordinate_356 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 20 = 0 := by
  exact pivot_356 A h

private lemma coordinate_357 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 21 = 0 := by
  exact pivot_357 A h

private lemma coordinate_358 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 22 = 0 := by
  exact pivot_358 A h

private lemma coordinate_359 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 23 = 0 := by
  exact pivot_359 A h

private lemma coordinate_360 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 24 = 0 := by
  exact pivot_360 A h

private lemma coordinate_361 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 25 = 0 := by
  exact pivot_361 A h

private lemma coordinate_362 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 26 = 0 := by
  exact pivot_362 A h

private lemma coordinate_363 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 12 27 = 0 := by
  exact pivot_363 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_364 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_364 A h + coordinate_10 A h) + (coordinate_34 A h + (coordinate_66 A h + coordinate_94 A h))) + ((coordinate_224 A h + (coordinate_229 A h + coordinate_258 A h)) + (coordinate_336 A h + (coordinate_341 A h + coordinate_342 A h))))

private lemma coordinate_365 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 1 = 0 := by
  exact pivot_365 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_366 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_366 A h + coordinate_22 A h) + (coordinate_54 A h + (coordinate_78 A h + coordinate_106 A h))) + ((coordinate_226 A h + (coordinate_249 A h + coordinate_278 A h)) + (coordinate_338 A h + (coordinate_361 A h + coordinate_362 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_367 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_367 A h + coordinate_23 A h) + (coordinate_55 A h + (coordinate_79 A h + coordinate_107 A h))) + ((coordinate_227 A h + (coordinate_248 A h + coordinate_279 A h)) + (coordinate_339 A h + (coordinate_360 A h + coordinate_363 A h))))

private lemma coordinate_368 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 4 = 0 := by
  exact pivot_368 A h

private lemma coordinate_369 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 5 = 0 := by
  exact pivot_369 A h

private lemma coordinate_370 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 6 = 0 := by
  exact pivot_370 A h

private lemma coordinate_371 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 7 = 0 := by
  exact pivot_371 A h

private lemma coordinate_372 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 8 = 0 := by
  exact pivot_372 A h

private lemma coordinate_373 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 9 = 0 := by
  exact pivot_373 A h

private lemma coordinate_374 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 10 = 0 := by
  exact pivot_374 A h

private lemma coordinate_375 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 11 = 0 := by
  exact pivot_375 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_376 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 12 = A 0 0 + A 0 3 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((pivot_376 A h + (coordinate_5 A h + coordinate_24 A h)) + (coordinate_37 A h + (coordinate_46 A h + coordinate_48 A h))) + ((coordinate_61 A h + (coordinate_80 A h + coordinate_89 A h)) + (coordinate_108 A h + (coordinate_232 A h + coordinate_233 A h)))) + (((coordinate_236 A h + (coordinate_244 A h + coordinate_245 A h)) + (coordinate_252 A h + (coordinate_261 A h + coordinate_272 A h))) + ((coordinate_345 A h + (coordinate_349 A h + coordinate_352 A h)) + (coordinate_353 A h + (coordinate_356 A h + coordinate_372 A h)))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_377 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 13 = A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((pivot_377 A h + coordinate_5 A h) + (coordinate_37 A h + coordinate_61 A h)) + ((coordinate_89 A h + coordinate_232 A h) + (coordinate_236 A h + coordinate_237 A h))) + (((coordinate_261 A h + coordinate_344 A h) + (coordinate_345 A h + coordinate_348 A h)) + ((coordinate_349 A h + coordinate_372 A h) + (coordinate_373 A h + coordinate_376 A h))))

private lemma coordinate_378 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_378 A h + coordinate_238 A h) + (coordinate_263 A h + coordinate_350 A h))

private lemma coordinate_379 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_379 A h + coordinate_239 A h) + (coordinate_263 A h + coordinate_351 A h))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_380 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 16 = A 0 2 + A 0 3 + A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_380 A h + (coordinate_46 A h + coordinate_232 A h)) + ((coordinate_233 A h + coordinate_236 A h) + (coordinate_237 A h + coordinate_240 A h))) + (((coordinate_244 A h + coordinate_245 A h) + (coordinate_252 A h + coordinate_353 A h)) + ((coordinate_372 A h + coordinate_373 A h) + (coordinate_376 A h + coordinate_377 A h))))

private lemma coordinate_381 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 17 = 0 := by
  exact pivot_381 A h

private lemma coordinate_382 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 18 = 0 := by
  exact pivot_382 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_383 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((pivot_383 A h + (coordinate_7 A h + coordinate_39 A h)) + (coordinate_63 A h + (coordinate_91 A h + coordinate_234 A h))) + ((coordinate_238 A h + (coordinate_239 A h + coordinate_242 A h)) + ((coordinate_243 A h + coordinate_246 A h) + (coordinate_247 A h + coordinate_263 A h)))) + (((coordinate_346 A h + (coordinate_347 A h + coordinate_350 A h)) + (coordinate_351 A h + (coordinate_354 A h + coordinate_355 A h))) + ((coordinate_358 A h + (coordinate_359 A h + coordinate_374 A h)) + ((coordinate_375 A h + coordinate_378 A h) + (coordinate_379 A h + coordinate_382 A h)))))

private lemma coordinate_384 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 20 = 0 := by
  exact pivot_384 A h

private lemma coordinate_385 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 21 = 0 := by
  exact pivot_385 A h

private lemma coordinate_386 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 22 = 0 := by
  exact pivot_386 A h

private lemma coordinate_387 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 23 = 0 := by
  exact pivot_387 A h

private lemma coordinate_388 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 24 = 0 := by
  exact pivot_388 A h

private lemma coordinate_389 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 25 = 0 := by
  exact pivot_389 A h

private lemma coordinate_390 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 26 = 0 := by
  exact pivot_390 A h

private lemma coordinate_391 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 13 27 = 0 := by
  exact pivot_391 A h

private lemma coordinate_392 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_392 A h + coordinate_314 A h)

private lemma coordinate_393 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 1 = 0 := by
  exact pivot_393 A h

private lemma coordinate_394 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_394 A h + coordinate_334 A h)

private lemma coordinate_395 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_395 A h + coordinate_335 A h)

private lemma coordinate_396 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 4 = 0 := by
  exact pivot_396 A h

private lemma coordinate_397 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 5 = 0 := by
  exact pivot_397 A h

private lemma coordinate_398 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 6 = 0 := by
  exact pivot_398 A h

private lemma coordinate_399 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 7 = 0 := by
  exact pivot_399 A h

private lemma coordinate_400 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 8 = 0 := by
  exact pivot_400 A h

private lemma coordinate_401 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 9 = 0 := by
  exact pivot_401 A h

private lemma coordinate_402 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 10 = 0 := by
  exact pivot_402 A h

private lemma coordinate_403 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 11 = 0 := by
  exact pivot_403 A h

private lemma coordinate_404 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_404 A h + (coordinate_317 A h + coordinate_325 A h)) + (coordinate_328 A h + (coordinate_400 A h + coordinate_401 A h)))

private lemma coordinate_405 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_405 A h + coordinate_317 A h) + (coordinate_400 A h + coordinate_404 A h))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_406 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 14 = A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_406 A h + (coordinate_29 A h + coordinate_34 A h)) + (coordinate_45 A h + (coordinate_54 A h + coordinate_61 A h))) + ((coordinate_81 A h + (coordinate_290 A h + coordinate_294 A h)) + (coordinate_298 A h + (coordinate_302 A h + coordinate_322 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_407 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 15 = A 0 0 + A 0 3 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_407 A h + (coordinate_29 A h + coordinate_34 A h)) + (coordinate_45 A h + (coordinate_55 A h + coordinate_59 A h))) + ((coordinate_61 A h + (coordinate_80 A h + coordinate_290 A h)) + ((coordinate_295 A h + coordinate_298 A h) + (coordinate_303 A h + coordinate_323 A h))))

private lemma coordinate_408 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_408 A h + (coordinate_325 A h + coordinate_400 A h)) + (coordinate_401 A h + (coordinate_404 A h + coordinate_405 A h)))

private lemma coordinate_409 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 17 = 0 := by
  exact pivot_409 A h

private lemma coordinate_410 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 18 = 0 := by
  exact pivot_410 A h

private lemma coordinate_411 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 19 = A 0 2 + A 0 3 + A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_411 A h + (coordinate_319 A h + coordinate_402 A h)) + (coordinate_406 A h + (coordinate_407 A h + coordinate_410 A h)))

private lemma coordinate_412 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 20 = 0 := by
  exact pivot_412 A h

private lemma coordinate_413 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 21 = 0 := by
  exact pivot_413 A h

private lemma coordinate_414 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 22 = 0 := by
  exact pivot_414 A h

private lemma coordinate_415 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 23 = 0 := by
  exact pivot_415 A h

private lemma coordinate_416 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 24 = 0 := by
  exact pivot_416 A h

private lemma coordinate_417 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 25 = 0 := by
  exact pivot_417 A h

private lemma coordinate_418 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 26 = 0 := by
  exact pivot_418 A h

private lemma coordinate_419 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 14 27 = 0 := by
  exact pivot_419 A h

private lemma coordinate_420 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_420 A h + (coordinate_308 A h + coordinate_392 A h))

private lemma coordinate_421 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 1 = 0 := by
  exact pivot_421 A h

private lemma coordinate_422 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_422 A h + (coordinate_310 A h + coordinate_394 A h))

private lemma coordinate_423 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_423 A h + (coordinate_311 A h + coordinate_395 A h))

private lemma coordinate_424 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 4 = 0 := by
  exact pivot_424 A h

private lemma coordinate_425 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 5 = 0 := by
  exact pivot_425 A h

private lemma coordinate_426 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 6 = 0 := by
  exact pivot_426 A h

private lemma coordinate_427 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 7 = 0 := by
  exact pivot_427 A h

private lemma coordinate_428 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 8 = 0 := by
  exact pivot_428 A h

private lemma coordinate_429 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 9 = 0 := by
  exact pivot_429 A h

private lemma coordinate_430 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 10 = 0 := by
  exact pivot_430 A h

private lemma coordinate_431 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 11 = 0 := by
  exact pivot_431 A h

private lemma coordinate_432 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_432 A h + coordinate_288 A h) + (coordinate_320 A h + coordinate_404 A h))

private lemma coordinate_433 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_433 A h + coordinate_288 A h) + (coordinate_321 A h + coordinate_405 A h))

private lemma coordinate_434 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 14 = A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_434 A h + (coordinate_290 A h + coordinate_298 A h)) + (coordinate_302 A h + (coordinate_322 A h + coordinate_406 A h)))

private lemma coordinate_435 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 15 = A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_435 A h + (coordinate_290 A h + coordinate_298 A h)) + (coordinate_303 A h + (coordinate_323 A h + coordinate_407 A h)))

private lemma coordinate_436 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_436 A h + coordinate_288 A h) + (coordinate_324 A h + coordinate_408 A h))

private lemma coordinate_437 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 17 = 0 := by
  exact pivot_437 A h

private lemma coordinate_438 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 18 = 0 := by
  exact pivot_438 A h

private lemma coordinate_439 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 19 = A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_439 A h + (coordinate_298 A h + coordinate_302 A h)) + (coordinate_303 A h + (coordinate_327 A h + coordinate_411 A h)))

private lemma coordinate_440 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 20 = 0 := by
  exact pivot_440 A h

private lemma coordinate_441 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 21 = 0 := by
  exact pivot_441 A h

private lemma coordinate_442 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 22 = 0 := by
  exact pivot_442 A h

private lemma coordinate_443 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 23 = 0 := by
  exact pivot_443 A h

private lemma coordinate_444 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 24 = 0 := by
  exact pivot_444 A h

private lemma coordinate_445 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 25 = 0 := by
  exact pivot_445 A h

private lemma coordinate_446 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 26 = 0 := by
  exact pivot_446 A h

private lemma coordinate_447 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 15 27 = 0 := by
  exact pivot_447 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_448 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((((pivot_448 A h + coordinate_45 A h) + (coordinate_46 A h + coordinate_84 A h)) + ((coordinate_232 A h + coordinate_233 A h) + (coordinate_236 A h + coordinate_237 A h))) + (((coordinate_240 A h + coordinate_244 A h) + (coordinate_245 A h + coordinate_252 A h)) + ((coordinate_269 A h + coordinate_336 A h) + (coordinate_353 A h + (coordinate_364 A h + coordinate_381 A h)))))

private lemma coordinate_449 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 1 = 0 := by
  exact pivot_449 A h

private lemma coordinate_450 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_450 A h + coordinate_252 A h) + (coordinate_254 A h + coordinate_336 A h)) + ((coordinate_338 A h + coordinate_364 A h) + (coordinate_366 A h + coordinate_448 A h)))

private lemma coordinate_451 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_451 A h + coordinate_252 A h) + (coordinate_255 A h + coordinate_336 A h)) + ((coordinate_339 A h + coordinate_364 A h) + (coordinate_367 A h + coordinate_448 A h)))

private lemma coordinate_452 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 4 = 0 := by
  exact pivot_452 A h

private lemma coordinate_453 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 5 = 0 := by
  exact pivot_453 A h

private lemma coordinate_454 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 6 = 0 := by
  exact pivot_454 A h

private lemma coordinate_455 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 7 = 0 := by
  exact pivot_455 A h

private lemma coordinate_456 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 8 = 0 := by
  exact pivot_456 A h

private lemma coordinate_457 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 9 = 0 := by
  exact pivot_457 A h

private lemma coordinate_458 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 10 = 0 := by
  exact pivot_458 A h

private lemma coordinate_459 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 11 = 0 := by
  exact pivot_459 A h

private lemma coordinate_460 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 12 = A 0 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_460 A h + coordinate_232 A h) + (coordinate_264 A h + (coordinate_348 A h + coordinate_376 A h)))

private lemma coordinate_461 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 13 = A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_461 A h + coordinate_232 A h) + (coordinate_265 A h + (coordinate_349 A h + coordinate_377 A h)))

private lemma coordinate_462 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 14 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_462 A h + (coordinate_234 A h + coordinate_242 A h)) + ((coordinate_246 A h + coordinate_266 A h) + (coordinate_350 A h + coordinate_378 A h)))

private lemma coordinate_463 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 15 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_463 A h + (coordinate_234 A h + coordinate_242 A h)) + ((coordinate_247 A h + coordinate_267 A h) + (coordinate_351 A h + coordinate_379 A h)))

private lemma coordinate_464 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 16 = A 0 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_464 A h + coordinate_232 A h) + (coordinate_268 A h + (coordinate_352 A h + coordinate_380 A h)))

private lemma coordinate_465 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 17 = 0 := by
  exact pivot_465 A h

private lemma coordinate_466 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 18 = 0 := by
  exact pivot_466 A h

private lemma coordinate_467 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 19 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_467 A h + (coordinate_242 A h + coordinate_246 A h)) + ((coordinate_247 A h + coordinate_271 A h) + (coordinate_355 A h + coordinate_383 A h)))

private lemma coordinate_468 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 20 = 0 := by
  exact pivot_468 A h

private lemma coordinate_469 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 21 = 0 := by
  exact pivot_469 A h

private lemma coordinate_470 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 22 = 0 := by
  exact pivot_470 A h

private lemma coordinate_471 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 23 = 0 := by
  exact pivot_471 A h

private lemma coordinate_472 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 24 = 0 := by
  exact pivot_472 A h

private lemma coordinate_473 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 25 = 0 := by
  exact pivot_473 A h

private lemma coordinate_474 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 26 = 0 := by
  exact pivot_474 A h

private lemma coordinate_475 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 16 27 = 0 := by
  exact pivot_475 A h

private lemma coordinate_476 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_476 A h + coordinate_46 A h)

private lemma coordinate_477 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_477 A h + (coordinate_18 A h + coordinate_29 A h)) + (coordinate_74 A h + (coordinate_84 A h + coordinate_102 A h)))

private lemma coordinate_478 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_478 A h + coordinate_46 A h)

private lemma coordinate_479 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_479 A h + coordinate_46 A h)

private lemma coordinate_480 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_480 A h + coordinate_8 A h) + (coordinate_32 A h + (coordinate_64 A h + coordinate_92 A h)))

private lemma coordinate_481 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 5 = 0 := by
  exact pivot_481 A h

private lemma coordinate_482 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_482 A h + coordinate_10 A h) + (coordinate_34 A h + (coordinate_66 A h + coordinate_94 A h)))

private lemma coordinate_483 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 7 = 0 := by
  exact pivot_483 A h

private lemma coordinate_484 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 8 = 0 := by
  exact pivot_484 A h

private lemma coordinate_485 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_485 A h + coordinate_5 A h) + (coordinate_37 A h + (coordinate_61 A h + coordinate_89 A h)))

private lemma coordinate_486 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 10 = 0 := by
  exact pivot_486 A h

private lemma coordinate_487 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_487 A h + coordinate_7 A h) + (coordinate_39 A h + (coordinate_63 A h + coordinate_91 A h)))

private lemma coordinate_488 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 12 = 0 := by
  exact pivot_488 A h

private lemma coordinate_489 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 13 = 0 := by
  exact pivot_489 A h

private lemma coordinate_490 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 14 = 0 := by
  exact pivot_490 A h

private lemma coordinate_491 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 15 = 0 := by
  exact pivot_491 A h

private lemma coordinate_492 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 16 = 0 := by
  exact pivot_492 A h

private lemma coordinate_493 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 17 = A 0 0 + A 0 2 + A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_493 A h + (coordinate_45 A h + coordinate_84 A h))

private lemma coordinate_494 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 18 = 0 := by
  exact pivot_494 A h

private lemma coordinate_495 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 19 = 0 := by
  exact pivot_495 A h

private lemma coordinate_496 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_496 A h + coordinate_24 A h) + (coordinate_48 A h + (coordinate_80 A h + coordinate_108 A h)))

private lemma coordinate_497 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_497 A h + coordinate_25 A h) + (coordinate_49 A h + (coordinate_81 A h + coordinate_109 A h)))

private lemma coordinate_498 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 22 = 0 := by
  exact pivot_498 A h

private lemma coordinate_499 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 23 = 0 := by
  exact pivot_499 A h

private lemma coordinate_500 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 24 = 0 := by
  exact pivot_500 A h

private lemma coordinate_501 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 25 = 0 := by
  exact pivot_501 A h

private lemma coordinate_502 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_502 A h + coordinate_22 A h) + (coordinate_54 A h + (coordinate_78 A h + coordinate_106 A h)))

private lemma coordinate_503 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 17 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_503 A h + coordinate_23 A h) + (coordinate_55 A h + (coordinate_79 A h + coordinate_107 A h)))

private lemma coordinate_504 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_504 A h + coordinate_45 A h)

private lemma coordinate_505 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 1 = 0 := by
  exact pivot_505 A h

private lemma coordinate_506 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_506 A h + coordinate_45 A h)

private lemma coordinate_507 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_507 A h + coordinate_45 A h)

private lemma coordinate_508 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 4 = 0 := by
  exact pivot_508 A h

private lemma coordinate_509 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_509 A h + coordinate_37 A h)

private lemma coordinate_510 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 6 = 0 := by
  exact pivot_510 A h

private lemma coordinate_511 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_511 A h + coordinate_39 A h)

private lemma coordinate_512 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_512 A h + coordinate_32 A h)

private lemma coordinate_513 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 9 = 0 := by
  exact pivot_513 A h

private lemma coordinate_514 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_514 A h + coordinate_34 A h)

private lemma coordinate_515 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 11 = 0 := by
  exact pivot_515 A h

private lemma coordinate_516 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 12 = 0 := by
  exact pivot_516 A h

private lemma coordinate_517 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 13 = 0 := by
  exact pivot_517 A h

private lemma coordinate_518 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 14 = 0 := by
  exact pivot_518 A h

private lemma coordinate_519 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 15 = 0 := by
  exact pivot_519 A h

private lemma coordinate_520 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 16 = 0 := by
  exact pivot_520 A h

private lemma coordinate_521 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 17 = 0 := by
  exact pivot_521 A h

private lemma coordinate_522 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 18 = A 0 0 + A 0 2 + A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_522 A h + (coordinate_29 A h + coordinate_45 A h))

private lemma coordinate_523 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 19 = 0 := by
  exact pivot_523 A h

private lemma coordinate_524 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 20 = 0 := by
  exact pivot_524 A h

private lemma coordinate_525 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 21 = 0 := by
  exact pivot_525 A h

private lemma coordinate_526 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_526 A h + coordinate_54 A h)

private lemma coordinate_527 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_527 A h + coordinate_55 A h)

private lemma coordinate_528 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_528 A h + coordinate_48 A h)

private lemma coordinate_529 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_529 A h + coordinate_49 A h)

private lemma coordinate_530 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 26 = 0 := by
  exact pivot_530 A h

private lemma coordinate_531 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 18 27 = 0 := by
  exact pivot_531 A h

private lemma coordinate_532 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_532 A h + coordinate_280 A h) + (coordinate_308 A h + (coordinate_392 A h + coordinate_420 A h)))

private lemma coordinate_533 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 1 = 0 := by
  exact pivot_533 A h

private lemma coordinate_534 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_534 A h + coordinate_282 A h) + (coordinate_310 A h + (coordinate_394 A h + coordinate_422 A h)))

private lemma coordinate_535 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_535 A h + coordinate_283 A h) + (coordinate_311 A h + (coordinate_395 A h + coordinate_423 A h)))

private lemma coordinate_536 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 4 = 0 := by
  exact pivot_536 A h

private lemma coordinate_537 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 5 = 0 := by
  exact pivot_537 A h

private lemma coordinate_538 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 6 = 0 := by
  exact pivot_538 A h

private lemma coordinate_539 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 7 = 0 := by
  exact pivot_539 A h

private lemma coordinate_540 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 8 = 0 := by
  exact pivot_540 A h

private lemma coordinate_541 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 9 = 0 := by
  exact pivot_541 A h

private lemma coordinate_542 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 10 = 0 := by
  exact pivot_542 A h

private lemma coordinate_543 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 11 = 0 := by
  exact pivot_543 A h

private lemma coordinate_544 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 12 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_544 A h + (coordinate_292 A h + coordinate_320 A h)) + (coordinate_404 A h + (coordinate_432 A h + coordinate_512 A h)))

private lemma coordinate_545 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 13 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_545 A h + (coordinate_293 A h + coordinate_321 A h)) + (coordinate_405 A h + (coordinate_433 A h + coordinate_512 A h)))

private lemma coordinate_546 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 14 = A 0 3 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_546 A h + coordinate_294 A h) + (coordinate_322 A h + coordinate_406 A h)) + ((coordinate_434 A h + coordinate_514 A h) + (coordinate_522 A h + coordinate_526 A h)))

private lemma coordinate_547 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 15 = A 0 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_547 A h + coordinate_295 A h) + (coordinate_323 A h + coordinate_407 A h)) + ((coordinate_435 A h + coordinate_514 A h) + (coordinate_522 A h + coordinate_527 A h)))

private lemma coordinate_548 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 16 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_548 A h + (coordinate_296 A h + coordinate_324 A h)) + (coordinate_408 A h + (coordinate_436 A h + coordinate_512 A h)))

private lemma coordinate_549 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 17 = 0 := by
  exact pivot_549 A h

private lemma coordinate_550 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 18 = 0 := by
  exact pivot_550 A h

private lemma coordinate_551 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 19 = A 0 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_551 A h + coordinate_299 A h) + (coordinate_327 A h + coordinate_411 A h)) + ((coordinate_439 A h + coordinate_522 A h) + (coordinate_526 A h + coordinate_527 A h)))

private lemma coordinate_552 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 20 = 0 := by
  exact pivot_552 A h

private lemma coordinate_553 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 21 = 0 := by
  exact pivot_553 A h

private lemma coordinate_554 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 22 = 0 := by
  exact pivot_554 A h

private lemma coordinate_555 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 23 = 0 := by
  exact pivot_555 A h

private lemma coordinate_556 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 24 = 0 := by
  exact pivot_556 A h

private lemma coordinate_557 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 25 = 0 := by
  exact pivot_557 A h

private lemma coordinate_558 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 26 = 0 := by
  exact pivot_558 A h

private lemma coordinate_559 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 19 27 = 0 := by
  exact pivot_559 A h

private lemma coordinate_560 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_560 A h + (coordinate_252 A h + coordinate_476 A h))

private lemma coordinate_561 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 1 = 0 := by
  exact pivot_561 A h

private lemma coordinate_562 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_562 A h + coordinate_560 A h)

private lemma coordinate_563 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_563 A h + coordinate_560 A h)

private lemma coordinate_564 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_564 A h + (coordinate_256 A h + coordinate_480 A h))

private lemma coordinate_565 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 5 = 0 := by
  exact pivot_565 A h

private lemma coordinate_566 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_566 A h + coordinate_258 A h) + (coordinate_336 A h + (coordinate_341 A h + coordinate_482 A h)))

private lemma coordinate_567 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 7 = 0 := by
  exact pivot_567 A h

private lemma coordinate_568 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 8 = 0 := by
  exact pivot_568 A h

private lemma coordinate_569 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 9 = A 0 2 + A 0 3 + A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_569 A h + (coordinate_261 A h + coordinate_344 A h)) + (coordinate_348 A h + (coordinate_349 A h + coordinate_485 A h)))

private lemma coordinate_570 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 10 = 0 := by
  exact pivot_570 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_571 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_571 A h + coordinate_263 A h) + (coordinate_346 A h + (coordinate_350 A h + coordinate_351 A h))) + ((coordinate_354 A h + coordinate_355 A h) + (coordinate_358 A h + (coordinate_359 A h + coordinate_487 A h))))

private lemma coordinate_572 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 12 = 0 := by
  exact pivot_572 A h

private lemma coordinate_573 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 13 = 0 := by
  exact pivot_573 A h

private lemma coordinate_574 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 14 = 0 := by
  exact pivot_574 A h

private lemma coordinate_575 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 15 = 0 := by
  exact pivot_575 A h

private lemma coordinate_576 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 16 = 0 := by
  exact pivot_576 A h

private lemma coordinate_577 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_577 A h + (coordinate_560 A h + coordinate_561 A h))

private lemma coordinate_578 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 18 = 0 := by
  exact pivot_578 A h

private lemma coordinate_579 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 19 = 0 := by
  exact pivot_579 A h

private lemma coordinate_580 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 20 = A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_580 A h + (coordinate_272 A h + coordinate_344 A h)) + (coordinate_348 A h + (coordinate_352 A h + coordinate_496 A h)))

private lemma coordinate_581 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 21 = A 0 0 + A 0 3 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_581 A h + (coordinate_273 A h + coordinate_344 A h)) + (coordinate_349 A h + (coordinate_352 A h + coordinate_497 A h)))

private lemma coordinate_582 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 22 = 0 := by
  exact pivot_582 A h

private lemma coordinate_583 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 23 = 0 := by
  exact pivot_583 A h

private lemma coordinate_584 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 24 = 0 := by
  exact pivot_584 A h

private lemma coordinate_585 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 25 = 0 := by
  exact pivot_585 A h

private lemma coordinate_586 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_586 A h + coordinate_278 A h) + (coordinate_338 A h + (coordinate_361 A h + coordinate_502 A h)))

private lemma coordinate_587 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 20 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_587 A h + coordinate_279 A h) + (coordinate_339 A h + (coordinate_360 A h + coordinate_503 A h)))

private lemma coordinate_588 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_588 A h + (coordinate_252 A h + coordinate_336 A h)) + ((coordinate_364 A h + coordinate_448 A h) + (coordinate_476 A h + coordinate_560 A h)))

private lemma coordinate_589 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 1 = 0 := by
  exact pivot_589 A h

private lemma coordinate_590 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_590 A h + coordinate_588 A h)

private lemma coordinate_591 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_591 A h + coordinate_588 A h)

private lemma coordinate_592 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_592 A h + (coordinate_256 A h + coordinate_340 A h)) + ((coordinate_368 A h + coordinate_452 A h) + (coordinate_480 A h + coordinate_564 A h)))

private lemma coordinate_593 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 5 = 0 := by
  exact pivot_593 A h

private lemma coordinate_594 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 6 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_594 A h + coordinate_224 A h) + (coordinate_229 A h + coordinate_258 A h)) + ((coordinate_342 A h + coordinate_370 A h) + (coordinate_454 A h + (coordinate_482 A h + coordinate_566 A h))))

private lemma coordinate_595 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 7 = 0 := by
  exact pivot_595 A h

private lemma coordinate_596 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 8 = 0 := by
  exact pivot_596 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_597 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 9 = A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_597 A h + coordinate_232 A h) + (coordinate_236 A h + (coordinate_237 A h + coordinate_261 A h))) + ((coordinate_345 A h + coordinate_373 A h) + (coordinate_457 A h + (coordinate_485 A h + coordinate_569 A h))))

private lemma coordinate_598 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 10 = 0 := by
  exact pivot_598 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_599 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_599 A h + (coordinate_234 A h + coordinate_238 A h)) + ((coordinate_239 A h + coordinate_242 A h) + (coordinate_243 A h + coordinate_246 A h))) + ((coordinate_247 A h + (coordinate_263 A h + coordinate_347 A h)) + ((coordinate_375 A h + coordinate_459 A h) + (coordinate_487 A h + coordinate_571 A h))))

private lemma coordinate_600 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 12 = 0 := by
  exact pivot_600 A h

private lemma coordinate_601 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 13 = 0 := by
  exact pivot_601 A h

private lemma coordinate_602 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 14 = 0 := by
  exact pivot_602 A h

private lemma coordinate_603 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 15 = 0 := by
  exact pivot_603 A h

private lemma coordinate_604 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 16 = 0 := by
  exact pivot_604 A h

private lemma coordinate_605 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_605 A h + (coordinate_588 A h + coordinate_589 A h))

private lemma coordinate_606 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 18 = 0 := by
  exact pivot_606 A h

private lemma coordinate_607 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 19 = 0 := by
  exact pivot_607 A h

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_608 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 20 = A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_608 A h + coordinate_232 A h) + (coordinate_236 A h + (coordinate_240 A h + coordinate_272 A h))) + ((coordinate_356 A h + coordinate_384 A h) + (coordinate_468 A h + (coordinate_496 A h + coordinate_580 A h))))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
private lemma coordinate_609 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 21 = A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_609 A h + coordinate_232 A h) + (coordinate_237 A h + (coordinate_240 A h + coordinate_273 A h))) + ((coordinate_357 A h + coordinate_385 A h) + (coordinate_469 A h + (coordinate_497 A h + coordinate_581 A h))))

private lemma coordinate_610 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 22 = 0 := by
  exact pivot_610 A h

private lemma coordinate_611 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 23 = 0 := by
  exact pivot_611 A h

private lemma coordinate_612 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 24 = 0 := by
  exact pivot_612 A h

private lemma coordinate_613 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 25 = 0 := by
  exact pivot_613 A h

private lemma coordinate_614 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 26 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_614 A h + coordinate_226 A h) + (coordinate_249 A h + coordinate_278 A h)) + ((coordinate_362 A h + coordinate_390 A h) + (coordinate_474 A h + (coordinate_502 A h + coordinate_586 A h))))

private lemma coordinate_615 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 21 27 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_615 A h + coordinate_227 A h) + (coordinate_248 A h + coordinate_279 A h)) + ((coordinate_363 A h + coordinate_391 A h) + (coordinate_475 A h + (coordinate_503 A h + coordinate_587 A h))))

private lemma coordinate_616 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 0 = 0 := by
  exact pivot_616 A h

private lemma coordinate_617 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 1 = 0 := by
  exact pivot_617 A h

private lemma coordinate_618 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_618 A h + coordinate_616 A h)

private lemma coordinate_619 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_619 A h + coordinate_616 A h)

private lemma coordinate_620 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 4 = 0 := by
  exact pivot_620 A h

private lemma coordinate_621 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_621 A h + coordinate_64 A h) + (coordinate_68 A h + coordinate_69 A h))

private lemma coordinate_622 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 6 = 0 := by
  exact pivot_622 A h

private lemma coordinate_623 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_623 A h + coordinate_66 A h) + (coordinate_70 A h + coordinate_71 A h)) + ((coordinate_74 A h + coordinate_75 A h) + (coordinate_78 A h + coordinate_79 A h)))

private lemma coordinate_624 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 8 = 0 := by
  exact pivot_624 A h

private lemma coordinate_625 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 9 = 0 := by
  exact pivot_625 A h

private lemma coordinate_626 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 10 = A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_626 A h + coordinate_61 A h)

private lemma coordinate_627 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 11 = 0 := by
  exact pivot_627 A h

private lemma coordinate_628 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 12 = 0 := by
  exact pivot_628 A h

private lemma coordinate_629 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 13 = 0 := by
  exact pivot_629 A h

private lemma coordinate_630 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 14 = 0 := by
  exact pivot_630 A h

private lemma coordinate_631 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 15 = 0 := by
  exact pivot_631 A h

private lemma coordinate_632 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 16 = 0 := by
  exact pivot_632 A h

private lemma coordinate_633 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 17 = 0 := by
  exact pivot_633 A h

private lemma coordinate_634 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_634 A h + coordinate_616 A h)

private lemma coordinate_635 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 19 = 0 := by
  exact pivot_635 A h

private lemma coordinate_636 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 20 = 0 := by
  exact pivot_636 A h

private lemma coordinate_637 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 21 = 0 := by
  exact pivot_637 A h

private lemma coordinate_638 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 22 = A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_638 A h + coordinate_81 A h)

private lemma coordinate_639 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 23 = A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_639 A h + (coordinate_59 A h + coordinate_80 A h))

private lemma coordinate_640 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_640 A h + coordinate_64 A h) + (coordinate_68 A h + coordinate_72 A h))

private lemma coordinate_641 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_641 A h + coordinate_64 A h) + (coordinate_69 A h + coordinate_72 A h))

private lemma coordinate_642 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 26 = 0 := by
  exact pivot_642 A h

private lemma coordinate_643 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 22 27 = 0 := by
  exact pivot_643 A h

private lemma coordinate_644 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 0 = 0 := by
  exact pivot_644 A h

private lemma coordinate_645 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 1 = 0 := by
  exact pivot_645 A h

private lemma coordinate_646 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_646 A h + coordinate_644 A h)

private lemma coordinate_647 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_647 A h + coordinate_644 A h)

private lemma coordinate_648 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 4 = 0 := by
  exact pivot_648 A h

private lemma coordinate_649 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 5 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_649 A h + coordinate_92 A h) + (coordinate_96 A h + coordinate_97 A h))

private lemma coordinate_650 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 6 = 0 := by
  exact pivot_650 A h

private lemma coordinate_651 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (((pivot_651 A h + coordinate_94 A h) + (coordinate_98 A h + coordinate_99 A h)) + ((coordinate_102 A h + coordinate_103 A h) + (coordinate_106 A h + coordinate_107 A h)))

private lemma coordinate_652 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 8 = 0 := by
  exact pivot_652 A h

private lemma coordinate_653 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 9 = 0 := by
  exact pivot_653 A h

private lemma coordinate_654 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 10 = A 0 2 + A 0 3 + A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_654 A h + (coordinate_84 A h + coordinate_89 A h))

private lemma coordinate_655 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 11 = 0 := by
  exact pivot_655 A h

private lemma coordinate_656 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 12 = 0 := by
  exact pivot_656 A h

private lemma coordinate_657 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 13 = 0 := by
  exact pivot_657 A h

private lemma coordinate_658 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 14 = 0 := by
  exact pivot_658 A h

private lemma coordinate_659 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 15 = 0 := by
  exact pivot_659 A h

private lemma coordinate_660 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 16 = 0 := by
  exact pivot_660 A h

private lemma coordinate_661 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 17 = 0 := by
  exact pivot_661 A h

private lemma coordinate_662 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_662 A h + coordinate_644 A h)

private lemma coordinate_663 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 19 = 0 := by
  exact pivot_663 A h

private lemma coordinate_664 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 20 = 0 := by
  exact pivot_664 A h

private lemma coordinate_665 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 21 = 0 := by
  exact pivot_665 A h

private lemma coordinate_666 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 22 = A 0 0 + A 0 3 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_666 A h + (coordinate_86 A h + coordinate_109 A h))

private lemma coordinate_667 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 23 = A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_667 A h + (coordinate_87 A h + coordinate_108 A h))

private lemma coordinate_668 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 24 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_668 A h + coordinate_92 A h) + (coordinate_96 A h + coordinate_100 A h))

private lemma coordinate_669 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 25 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    ((pivot_669 A h + coordinate_92 A h) + (coordinate_97 A h + coordinate_100 A h))

private lemma coordinate_670 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 26 = 0 := by
  exact pivot_670 A h

private lemma coordinate_671 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 23 27 = 0 := by
  exact pivot_671 A h

private lemma coordinate_672 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_672 A h + coordinate_577 A h)

private lemma coordinate_673 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 1 = 0 := by
  exact pivot_673 A h

private lemma coordinate_674 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_674 A h + coordinate_577 A h)

private lemma coordinate_675 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_675 A h + coordinate_577 A h)

private lemma coordinate_676 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 4 = 0 := by
  exact pivot_676 A h

private lemma coordinate_677 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 5 = A 0 2 + A 0 3 + A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_677 A h + coordinate_569 A h)

private lemma coordinate_678 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 6 = 0 := by
  exact pivot_678 A h

private lemma coordinate_679 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_679 A h + coordinate_571 A h)

private lemma coordinate_680 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_680 A h + coordinate_564 A h)

private lemma coordinate_681 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 9 = 0 := by
  exact pivot_681 A h

private lemma coordinate_682 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_682 A h + coordinate_566 A h)

private lemma coordinate_683 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 11 = 0 := by
  exact pivot_683 A h

private lemma coordinate_684 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 12 = 0 := by
  exact pivot_684 A h

private lemma coordinate_685 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 13 = 0 := by
  exact pivot_685 A h

private lemma coordinate_686 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 14 = 0 := by
  exact pivot_686 A h

private lemma coordinate_687 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 15 = 0 := by
  exact pivot_687 A h

private lemma coordinate_688 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 16 = 0 := by
  exact pivot_688 A h

private lemma coordinate_689 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 17 = 0 := by
  exact pivot_689 A h

private lemma coordinate_690 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_690 A h + (coordinate_561 A h + coordinate_577 A h))

private lemma coordinate_691 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 19 = 0 := by
  exact pivot_691 A h

private lemma coordinate_692 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 20 = 0 := by
  exact pivot_692 A h

private lemma coordinate_693 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 21 = 0 := by
  exact pivot_693 A h

private lemma coordinate_694 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_694 A h + coordinate_586 A h)

private lemma coordinate_695 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_695 A h + coordinate_587 A h)

private lemma coordinate_696 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 24 = A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_696 A h + coordinate_580 A h)

private lemma coordinate_697 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 25 = A 0 0 + A 0 3 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_697 A h + coordinate_581 A h)

private lemma coordinate_698 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 26 = 0 := by
  exact pivot_698 A h

private lemma coordinate_699 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 24 27 = 0 := by
  exact pivot_699 A h

private lemma coordinate_700 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_700 A h + coordinate_605 A h)

private lemma coordinate_701 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 1 = 0 := by
  exact pivot_701 A h

private lemma coordinate_702 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_702 A h + coordinate_605 A h)

private lemma coordinate_703 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_703 A h + coordinate_605 A h)

private lemma coordinate_704 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 4 = 0 := by
  exact pivot_704 A h

private lemma coordinate_705 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 5 = A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_705 A h + coordinate_597 A h)

private lemma coordinate_706 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 6 = 0 := by
  exact pivot_706 A h

private lemma coordinate_707 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 7 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_707 A h + coordinate_599 A h)

private lemma coordinate_708 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 8 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_708 A h + coordinate_592 A h)

private lemma coordinate_709 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 9 = 0 := by
  exact pivot_709 A h

private lemma coordinate_710 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 10 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_710 A h + coordinate_594 A h)

private lemma coordinate_711 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 11 = 0 := by
  exact pivot_711 A h

private lemma coordinate_712 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 12 = 0 := by
  exact pivot_712 A h

private lemma coordinate_713 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 13 = 0 := by
  exact pivot_713 A h

private lemma coordinate_714 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 14 = 0 := by
  exact pivot_714 A h

private lemma coordinate_715 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 15 = 0 := by
  exact pivot_715 A h

private lemma coordinate_716 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 16 = 0 := by
  exact pivot_716 A h

private lemma coordinate_717 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 17 = 0 := by
  exact pivot_717 A h

private lemma coordinate_718 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 18 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_718 A h + (coordinate_589 A h + coordinate_605 A h))

private lemma coordinate_719 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 19 = 0 := by
  exact pivot_719 A h

private lemma coordinate_720 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 20 = 0 := by
  exact pivot_720 A h

private lemma coordinate_721 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 21 = 0 := by
  exact pivot_721 A h

private lemma coordinate_722 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 22 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_722 A h + coordinate_614 A h)

private lemma coordinate_723 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 23 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_723 A h + coordinate_615 A h)

private lemma coordinate_724 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 24 = A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_724 A h + coordinate_608 A h)

private lemma coordinate_725 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 25 = A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_725 A h + coordinate_609 A h)

private lemma coordinate_726 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 26 = 0 := by
  exact pivot_726 A h

private lemma coordinate_727 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 25 27 = 0 := by
  exact pivot_727 A h

private lemma coordinate_728 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_728 A h + coordinate_634 A h)

private lemma coordinate_729 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_729 A h + (coordinate_616 A h + coordinate_634 A h))

private lemma coordinate_730 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_730 A h + coordinate_634 A h)

private lemma coordinate_731 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_731 A h + coordinate_634 A h)

private lemma coordinate_732 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_732 A h + coordinate_624 A h)

private lemma coordinate_733 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 5 = 0 := by
  exact pivot_733 A h

private lemma coordinate_734 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 6 = A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_734 A h + coordinate_626 A h)

private lemma coordinate_735 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 7 = 0 := by
  exact pivot_735 A h

private lemma coordinate_736 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 8 = 0 := by
  exact pivot_736 A h

private lemma coordinate_737 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_737 A h + coordinate_621 A h)

private lemma coordinate_738 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 10 = 0 := by
  exact pivot_738 A h

private lemma coordinate_739 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_739 A h + coordinate_623 A h)

private lemma coordinate_740 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 12 = 0 := by
  exact pivot_740 A h

private lemma coordinate_741 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 13 = 0 := by
  exact pivot_741 A h

private lemma coordinate_742 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 14 = 0 := by
  exact pivot_742 A h

private lemma coordinate_743 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 15 = 0 := by
  exact pivot_743 A h

private lemma coordinate_744 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 16 = 0 := by
  exact pivot_744 A h

private lemma coordinate_745 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_745 A h + coordinate_616 A h)

private lemma coordinate_746 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 18 = 0 := by
  exact pivot_746 A h

private lemma coordinate_747 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 19 = 0 := by
  exact pivot_747 A h

private lemma coordinate_748 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_748 A h + coordinate_640 A h)

private lemma coordinate_749 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_749 A h + coordinate_641 A h)

private lemma coordinate_750 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 22 = 0 := by
  exact pivot_750 A h

private lemma coordinate_751 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 23 = 0 := by
  exact pivot_751 A h

private lemma coordinate_752 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 24 = 0 := by
  exact pivot_752 A h

private lemma coordinate_753 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 25 = 0 := by
  exact pivot_753 A h

private lemma coordinate_754 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 26 = A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_754 A h + coordinate_638 A h)

private lemma coordinate_755 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 26 27 = A 0 0 + A 0 2 + A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_755 A h + coordinate_639 A h)

private lemma coordinate_756 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 0 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_756 A h + coordinate_662 A h)

private lemma coordinate_757 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 1 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_757 A h + (coordinate_644 A h + coordinate_662 A h))

private lemma coordinate_758 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 2 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_758 A h + coordinate_662 A h)

private lemma coordinate_759 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 3 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_759 A h + coordinate_662 A h)

private lemma coordinate_760 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 4 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_760 A h + coordinate_652 A h)

private lemma coordinate_761 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 5 = 0 := by
  exact pivot_761 A h

private lemma coordinate_762 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 6 = A 0 2 + A 0 3 + A 2 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_762 A h + coordinate_654 A h)

private lemma coordinate_763 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 7 = 0 := by
  exact pivot_763 A h

private lemma coordinate_764 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 8 = 0 := by
  exact pivot_764 A h

private lemma coordinate_765 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 9 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_765 A h + coordinate_649 A h)

private lemma coordinate_766 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 10 = 0 := by
  exact pivot_766 A h

private lemma coordinate_767 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 11 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_767 A h + coordinate_651 A h)

private lemma coordinate_768 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 12 = 0 := by
  exact pivot_768 A h

private lemma coordinate_769 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 13 = 0 := by
  exact pivot_769 A h

private lemma coordinate_770 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 14 = 0 := by
  exact pivot_770 A h

private lemma coordinate_771 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 15 = 0 := by
  exact pivot_771 A h

private lemma coordinate_772 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 16 = 0 := by
  exact pivot_772 A h

private lemma coordinate_773 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 17 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_773 A h + coordinate_644 A h)

private lemma coordinate_774 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 18 = 0 := by
  exact pivot_774 A h

private lemma coordinate_775 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 19 = 0 := by
  exact pivot_775 A h

private lemma coordinate_776 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 20 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_776 A h + coordinate_668 A h)

private lemma coordinate_777 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 21 = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_777 A h + coordinate_669 A h)

private lemma coordinate_778 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 22 = 0 := by
  exact pivot_778 A h

private lemma coordinate_779 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 23 = 0 := by
  exact pivot_779 A h

private lemma coordinate_780 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 24 = 0 := by
  exact pivot_780 A h

private lemma coordinate_781 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 25 = 0 := by
  exact pivot_781 A h

private lemma coordinate_782 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 26 = A 0 0 + A 0 3 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_782 A h + coordinate_666 A h)

private lemma coordinate_783 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A 27 27 = A 0 3 + A 2 0 + A 2 2 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.ofNat_eq_mod (R := F)]))
    (pivot_783 A h + coordinate_667 A h)

private lemma normalForm_row_0 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 0 c = normalForm A 0 c := by
  intro c
  fin_cases c
  · rfl
  · exact coordinate_1 A h
  · rfl
  · rfl
  · exact coordinate_4 A h
  · exact coordinate_5 A h
  · exact coordinate_6 A h
  · exact coordinate_7 A h
  · exact coordinate_8 A h
  · exact coordinate_9 A h
  · exact coordinate_10 A h
  · exact coordinate_11 A h
  · exact coordinate_12 A h
  · exact coordinate_13 A h
  · exact coordinate_14 A h
  · exact coordinate_15 A h
  · exact coordinate_16 A h
  · exact coordinate_17 A h
  · exact coordinate_18 A h
  · exact coordinate_19 A h
  · exact coordinate_20 A h
  · exact coordinate_21 A h
  · exact coordinate_22 A h
  · exact coordinate_23 A h
  · exact coordinate_24 A h
  · exact coordinate_25 A h
  · exact coordinate_26 A h
  · exact coordinate_27 A h

private lemma normalForm_row_1 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 1 c = normalForm A 1 c := by
  intro c
  fin_cases c
  · exact coordinate_28 A h
  · exact coordinate_29 A h
  · exact coordinate_30 A h
  · exact coordinate_31 A h
  · exact coordinate_32 A h
  · exact coordinate_33 A h
  · exact coordinate_34 A h
  · exact coordinate_35 A h
  · exact coordinate_36 A h
  · exact coordinate_37 A h
  · exact coordinate_38 A h
  · exact coordinate_39 A h
  · exact coordinate_40 A h
  · exact coordinate_41 A h
  · exact coordinate_42 A h
  · exact coordinate_43 A h
  · exact coordinate_44 A h
  · exact coordinate_45 A h
  · exact coordinate_46 A h
  · exact coordinate_47 A h
  · exact coordinate_48 A h
  · exact coordinate_49 A h
  · exact coordinate_50 A h
  · exact coordinate_51 A h
  · exact coordinate_52 A h
  · exact coordinate_53 A h
  · exact coordinate_54 A h
  · exact coordinate_55 A h

private lemma normalForm_row_2 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 2 c = normalForm A 2 c := by
  intro c
  fin_cases c
  · rfl
  · exact coordinate_57 A h
  · rfl
  · exact coordinate_59 A h
  · exact coordinate_60 A h
  · exact coordinate_61 A h
  · exact coordinate_62 A h
  · exact coordinate_63 A h
  · exact coordinate_64 A h
  · exact coordinate_65 A h
  · exact coordinate_66 A h
  · exact coordinate_67 A h
  · exact coordinate_68 A h
  · exact coordinate_69 A h
  · exact coordinate_70 A h
  · exact coordinate_71 A h
  · exact coordinate_72 A h
  · exact coordinate_73 A h
  · exact coordinate_74 A h
  · exact coordinate_75 A h
  · exact coordinate_76 A h
  · exact coordinate_77 A h
  · exact coordinate_78 A h
  · exact coordinate_79 A h
  · exact coordinate_80 A h
  · exact coordinate_81 A h
  · exact coordinate_82 A h
  · exact coordinate_83 A h

private lemma normalForm_row_3 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 3 c = normalForm A 3 c := by
  intro c
  fin_cases c
  · exact coordinate_84 A h
  · exact coordinate_85 A h
  · exact coordinate_86 A h
  · exact coordinate_87 A h
  · exact coordinate_88 A h
  · exact coordinate_89 A h
  · exact coordinate_90 A h
  · exact coordinate_91 A h
  · exact coordinate_92 A h
  · exact coordinate_93 A h
  · exact coordinate_94 A h
  · exact coordinate_95 A h
  · exact coordinate_96 A h
  · exact coordinate_97 A h
  · exact coordinate_98 A h
  · exact coordinate_99 A h
  · exact coordinate_100 A h
  · exact coordinate_101 A h
  · exact coordinate_102 A h
  · exact coordinate_103 A h
  · exact coordinate_104 A h
  · exact coordinate_105 A h
  · exact coordinate_106 A h
  · exact coordinate_107 A h
  · exact coordinate_108 A h
  · exact coordinate_109 A h
  · exact coordinate_110 A h
  · exact coordinate_111 A h

private lemma normalForm_row_4 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 4 c = normalForm A 4 c := by
  intro c
  fin_cases c
  · exact coordinate_112 A h
  · exact coordinate_113 A h
  · exact coordinate_114 A h
  · exact coordinate_115 A h
  · exact coordinate_116 A h
  · exact coordinate_117 A h
  · exact coordinate_118 A h
  · exact coordinate_119 A h
  · exact coordinate_120 A h
  · exact coordinate_121 A h
  · exact coordinate_122 A h
  · exact coordinate_123 A h
  · exact coordinate_124 A h
  · exact coordinate_125 A h
  · exact coordinate_126 A h
  · exact coordinate_127 A h
  · exact coordinate_128 A h
  · exact coordinate_129 A h
  · exact coordinate_130 A h
  · exact coordinate_131 A h
  · exact coordinate_132 A h
  · exact coordinate_133 A h
  · exact coordinate_134 A h
  · exact coordinate_135 A h
  · exact coordinate_136 A h
  · exact coordinate_137 A h
  · exact coordinate_138 A h
  · exact coordinate_139 A h

private lemma normalForm_row_5 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 5 c = normalForm A 5 c := by
  intro c
  fin_cases c
  · exact coordinate_140 A h
  · exact coordinate_141 A h
  · exact coordinate_142 A h
  · exact coordinate_143 A h
  · exact coordinate_144 A h
  · exact coordinate_145 A h
  · exact coordinate_146 A h
  · exact coordinate_147 A h
  · exact coordinate_148 A h
  · exact coordinate_149 A h
  · exact coordinate_150 A h
  · exact coordinate_151 A h
  · exact coordinate_152 A h
  · exact coordinate_153 A h
  · exact coordinate_154 A h
  · exact coordinate_155 A h
  · exact coordinate_156 A h
  · exact coordinate_157 A h
  · exact coordinate_158 A h
  · exact coordinate_159 A h
  · exact coordinate_160 A h
  · exact coordinate_161 A h
  · exact coordinate_162 A h
  · exact coordinate_163 A h
  · exact coordinate_164 A h
  · exact coordinate_165 A h
  · exact coordinate_166 A h
  · exact coordinate_167 A h

private lemma normalForm_row_6 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 6 c = normalForm A 6 c := by
  intro c
  fin_cases c
  · exact coordinate_168 A h
  · exact coordinate_169 A h
  · exact coordinate_170 A h
  · exact coordinate_171 A h
  · exact coordinate_172 A h
  · exact coordinate_173 A h
  · exact coordinate_174 A h
  · exact coordinate_175 A h
  · exact coordinate_176 A h
  · exact coordinate_177 A h
  · exact coordinate_178 A h
  · exact coordinate_179 A h
  · exact coordinate_180 A h
  · exact coordinate_181 A h
  · exact coordinate_182 A h
  · exact coordinate_183 A h
  · exact coordinate_184 A h
  · exact coordinate_185 A h
  · exact coordinate_186 A h
  · exact coordinate_187 A h
  · exact coordinate_188 A h
  · exact coordinate_189 A h
  · exact coordinate_190 A h
  · exact coordinate_191 A h
  · exact coordinate_192 A h
  · exact coordinate_193 A h
  · exact coordinate_194 A h
  · exact coordinate_195 A h

private lemma normalForm_row_7 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 7 c = normalForm A 7 c := by
  intro c
  fin_cases c
  · exact coordinate_196 A h
  · exact coordinate_197 A h
  · exact coordinate_198 A h
  · exact coordinate_199 A h
  · exact coordinate_200 A h
  · exact coordinate_201 A h
  · exact coordinate_202 A h
  · exact coordinate_203 A h
  · exact coordinate_204 A h
  · exact coordinate_205 A h
  · exact coordinate_206 A h
  · exact coordinate_207 A h
  · exact coordinate_208 A h
  · exact coordinate_209 A h
  · exact coordinate_210 A h
  · exact coordinate_211 A h
  · exact coordinate_212 A h
  · exact coordinate_213 A h
  · exact coordinate_214 A h
  · exact coordinate_215 A h
  · exact coordinate_216 A h
  · exact coordinate_217 A h
  · exact coordinate_218 A h
  · exact coordinate_219 A h
  · exact coordinate_220 A h
  · exact coordinate_221 A h
  · exact coordinate_222 A h
  · exact coordinate_223 A h

private lemma normalForm_row_8 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 8 c = normalForm A 8 c := by
  intro c
  fin_cases c
  · exact coordinate_224 A h
  · exact coordinate_225 A h
  · exact coordinate_226 A h
  · exact coordinate_227 A h
  · exact coordinate_228 A h
  · exact coordinate_229 A h
  · exact coordinate_230 A h
  · exact coordinate_231 A h
  · exact coordinate_232 A h
  · exact coordinate_233 A h
  · exact coordinate_234 A h
  · exact coordinate_235 A h
  · exact coordinate_236 A h
  · exact coordinate_237 A h
  · exact coordinate_238 A h
  · exact coordinate_239 A h
  · exact coordinate_240 A h
  · exact coordinate_241 A h
  · exact coordinate_242 A h
  · exact coordinate_243 A h
  · exact coordinate_244 A h
  · exact coordinate_245 A h
  · exact coordinate_246 A h
  · exact coordinate_247 A h
  · exact coordinate_248 A h
  · exact coordinate_249 A h
  · exact coordinate_250 A h
  · exact coordinate_251 A h

private lemma normalForm_row_9 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 9 c = normalForm A 9 c := by
  intro c
  fin_cases c
  · exact coordinate_252 A h
  · exact coordinate_253 A h
  · exact coordinate_254 A h
  · exact coordinate_255 A h
  · exact coordinate_256 A h
  · exact coordinate_257 A h
  · exact coordinate_258 A h
  · exact coordinate_259 A h
  · exact coordinate_260 A h
  · exact coordinate_261 A h
  · exact coordinate_262 A h
  · exact coordinate_263 A h
  · exact coordinate_264 A h
  · exact coordinate_265 A h
  · exact coordinate_266 A h
  · exact coordinate_267 A h
  · exact coordinate_268 A h
  · exact coordinate_269 A h
  · exact coordinate_270 A h
  · exact coordinate_271 A h
  · exact coordinate_272 A h
  · exact coordinate_273 A h
  · exact coordinate_274 A h
  · exact coordinate_275 A h
  · exact coordinate_276 A h
  · exact coordinate_277 A h
  · exact coordinate_278 A h
  · exact coordinate_279 A h

private lemma normalForm_row_10 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 10 c = normalForm A 10 c := by
  intro c
  fin_cases c
  · exact coordinate_280 A h
  · exact coordinate_281 A h
  · exact coordinate_282 A h
  · exact coordinate_283 A h
  · exact coordinate_284 A h
  · exact coordinate_285 A h
  · exact coordinate_286 A h
  · exact coordinate_287 A h
  · exact coordinate_288 A h
  · exact coordinate_289 A h
  · exact coordinate_290 A h
  · exact coordinate_291 A h
  · exact coordinate_292 A h
  · exact coordinate_293 A h
  · exact coordinate_294 A h
  · exact coordinate_295 A h
  · exact coordinate_296 A h
  · exact coordinate_297 A h
  · exact coordinate_298 A h
  · exact coordinate_299 A h
  · exact coordinate_300 A h
  · exact coordinate_301 A h
  · exact coordinate_302 A h
  · exact coordinate_303 A h
  · exact coordinate_304 A h
  · exact coordinate_305 A h
  · exact coordinate_306 A h
  · exact coordinate_307 A h

private lemma normalForm_row_11 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 11 c = normalForm A 11 c := by
  intro c
  fin_cases c
  · exact coordinate_308 A h
  · exact coordinate_309 A h
  · exact coordinate_310 A h
  · exact coordinate_311 A h
  · exact coordinate_312 A h
  · exact coordinate_313 A h
  · exact coordinate_314 A h
  · exact coordinate_315 A h
  · exact coordinate_316 A h
  · exact coordinate_317 A h
  · exact coordinate_318 A h
  · exact coordinate_319 A h
  · exact coordinate_320 A h
  · exact coordinate_321 A h
  · exact coordinate_322 A h
  · exact coordinate_323 A h
  · exact coordinate_324 A h
  · exact coordinate_325 A h
  · exact coordinate_326 A h
  · exact coordinate_327 A h
  · exact coordinate_328 A h
  · exact coordinate_329 A h
  · exact coordinate_330 A h
  · exact coordinate_331 A h
  · exact coordinate_332 A h
  · exact coordinate_333 A h
  · exact coordinate_334 A h
  · exact coordinate_335 A h

private lemma normalForm_row_12 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 12 c = normalForm A 12 c := by
  intro c
  fin_cases c
  · exact coordinate_336 A h
  · exact coordinate_337 A h
  · exact coordinate_338 A h
  · exact coordinate_339 A h
  · exact coordinate_340 A h
  · exact coordinate_341 A h
  · exact coordinate_342 A h
  · exact coordinate_343 A h
  · exact coordinate_344 A h
  · exact coordinate_345 A h
  · exact coordinate_346 A h
  · exact coordinate_347 A h
  · exact coordinate_348 A h
  · exact coordinate_349 A h
  · exact coordinate_350 A h
  · exact coordinate_351 A h
  · exact coordinate_352 A h
  · exact coordinate_353 A h
  · exact coordinate_354 A h
  · exact coordinate_355 A h
  · exact coordinate_356 A h
  · exact coordinate_357 A h
  · exact coordinate_358 A h
  · exact coordinate_359 A h
  · exact coordinate_360 A h
  · exact coordinate_361 A h
  · exact coordinate_362 A h
  · exact coordinate_363 A h

private lemma normalForm_row_13 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 13 c = normalForm A 13 c := by
  intro c
  fin_cases c
  · exact coordinate_364 A h
  · exact coordinate_365 A h
  · exact coordinate_366 A h
  · exact coordinate_367 A h
  · exact coordinate_368 A h
  · exact coordinate_369 A h
  · exact coordinate_370 A h
  · exact coordinate_371 A h
  · exact coordinate_372 A h
  · exact coordinate_373 A h
  · exact coordinate_374 A h
  · exact coordinate_375 A h
  · exact coordinate_376 A h
  · exact coordinate_377 A h
  · exact coordinate_378 A h
  · exact coordinate_379 A h
  · exact coordinate_380 A h
  · exact coordinate_381 A h
  · exact coordinate_382 A h
  · exact coordinate_383 A h
  · exact coordinate_384 A h
  · exact coordinate_385 A h
  · exact coordinate_386 A h
  · exact coordinate_387 A h
  · exact coordinate_388 A h
  · exact coordinate_389 A h
  · exact coordinate_390 A h
  · exact coordinate_391 A h

private lemma normalForm_row_14 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 14 c = normalForm A 14 c := by
  intro c
  fin_cases c
  · exact coordinate_392 A h
  · exact coordinate_393 A h
  · exact coordinate_394 A h
  · exact coordinate_395 A h
  · exact coordinate_396 A h
  · exact coordinate_397 A h
  · exact coordinate_398 A h
  · exact coordinate_399 A h
  · exact coordinate_400 A h
  · exact coordinate_401 A h
  · exact coordinate_402 A h
  · exact coordinate_403 A h
  · exact coordinate_404 A h
  · exact coordinate_405 A h
  · exact coordinate_406 A h
  · exact coordinate_407 A h
  · exact coordinate_408 A h
  · exact coordinate_409 A h
  · exact coordinate_410 A h
  · exact coordinate_411 A h
  · exact coordinate_412 A h
  · exact coordinate_413 A h
  · exact coordinate_414 A h
  · exact coordinate_415 A h
  · exact coordinate_416 A h
  · exact coordinate_417 A h
  · exact coordinate_418 A h
  · exact coordinate_419 A h

private lemma normalForm_row_15 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 15 c = normalForm A 15 c := by
  intro c
  fin_cases c
  · exact coordinate_420 A h
  · exact coordinate_421 A h
  · exact coordinate_422 A h
  · exact coordinate_423 A h
  · exact coordinate_424 A h
  · exact coordinate_425 A h
  · exact coordinate_426 A h
  · exact coordinate_427 A h
  · exact coordinate_428 A h
  · exact coordinate_429 A h
  · exact coordinate_430 A h
  · exact coordinate_431 A h
  · exact coordinate_432 A h
  · exact coordinate_433 A h
  · exact coordinate_434 A h
  · exact coordinate_435 A h
  · exact coordinate_436 A h
  · exact coordinate_437 A h
  · exact coordinate_438 A h
  · exact coordinate_439 A h
  · exact coordinate_440 A h
  · exact coordinate_441 A h
  · exact coordinate_442 A h
  · exact coordinate_443 A h
  · exact coordinate_444 A h
  · exact coordinate_445 A h
  · exact coordinate_446 A h
  · exact coordinate_447 A h

private lemma normalForm_row_16 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 16 c = normalForm A 16 c := by
  intro c
  fin_cases c
  · exact coordinate_448 A h
  · exact coordinate_449 A h
  · exact coordinate_450 A h
  · exact coordinate_451 A h
  · exact coordinate_452 A h
  · exact coordinate_453 A h
  · exact coordinate_454 A h
  · exact coordinate_455 A h
  · exact coordinate_456 A h
  · exact coordinate_457 A h
  · exact coordinate_458 A h
  · exact coordinate_459 A h
  · exact coordinate_460 A h
  · exact coordinate_461 A h
  · exact coordinate_462 A h
  · exact coordinate_463 A h
  · exact coordinate_464 A h
  · exact coordinate_465 A h
  · exact coordinate_466 A h
  · exact coordinate_467 A h
  · exact coordinate_468 A h
  · exact coordinate_469 A h
  · exact coordinate_470 A h
  · exact coordinate_471 A h
  · exact coordinate_472 A h
  · exact coordinate_473 A h
  · exact coordinate_474 A h
  · exact coordinate_475 A h

private lemma normalForm_row_17 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 17 c = normalForm A 17 c := by
  intro c
  fin_cases c
  · exact coordinate_476 A h
  · exact coordinate_477 A h
  · exact coordinate_478 A h
  · exact coordinate_479 A h
  · exact coordinate_480 A h
  · exact coordinate_481 A h
  · exact coordinate_482 A h
  · exact coordinate_483 A h
  · exact coordinate_484 A h
  · exact coordinate_485 A h
  · exact coordinate_486 A h
  · exact coordinate_487 A h
  · exact coordinate_488 A h
  · exact coordinate_489 A h
  · exact coordinate_490 A h
  · exact coordinate_491 A h
  · exact coordinate_492 A h
  · exact coordinate_493 A h
  · exact coordinate_494 A h
  · exact coordinate_495 A h
  · exact coordinate_496 A h
  · exact coordinate_497 A h
  · exact coordinate_498 A h
  · exact coordinate_499 A h
  · exact coordinate_500 A h
  · exact coordinate_501 A h
  · exact coordinate_502 A h
  · exact coordinate_503 A h

private lemma normalForm_row_18 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 18 c = normalForm A 18 c := by
  intro c
  fin_cases c
  · exact coordinate_504 A h
  · exact coordinate_505 A h
  · exact coordinate_506 A h
  · exact coordinate_507 A h
  · exact coordinate_508 A h
  · exact coordinate_509 A h
  · exact coordinate_510 A h
  · exact coordinate_511 A h
  · exact coordinate_512 A h
  · exact coordinate_513 A h
  · exact coordinate_514 A h
  · exact coordinate_515 A h
  · exact coordinate_516 A h
  · exact coordinate_517 A h
  · exact coordinate_518 A h
  · exact coordinate_519 A h
  · exact coordinate_520 A h
  · exact coordinate_521 A h
  · exact coordinate_522 A h
  · exact coordinate_523 A h
  · exact coordinate_524 A h
  · exact coordinate_525 A h
  · exact coordinate_526 A h
  · exact coordinate_527 A h
  · exact coordinate_528 A h
  · exact coordinate_529 A h
  · exact coordinate_530 A h
  · exact coordinate_531 A h

private lemma normalForm_row_19 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 19 c = normalForm A 19 c := by
  intro c
  fin_cases c
  · exact coordinate_532 A h
  · exact coordinate_533 A h
  · exact coordinate_534 A h
  · exact coordinate_535 A h
  · exact coordinate_536 A h
  · exact coordinate_537 A h
  · exact coordinate_538 A h
  · exact coordinate_539 A h
  · exact coordinate_540 A h
  · exact coordinate_541 A h
  · exact coordinate_542 A h
  · exact coordinate_543 A h
  · exact coordinate_544 A h
  · exact coordinate_545 A h
  · exact coordinate_546 A h
  · exact coordinate_547 A h
  · exact coordinate_548 A h
  · exact coordinate_549 A h
  · exact coordinate_550 A h
  · exact coordinate_551 A h
  · exact coordinate_552 A h
  · exact coordinate_553 A h
  · exact coordinate_554 A h
  · exact coordinate_555 A h
  · exact coordinate_556 A h
  · exact coordinate_557 A h
  · exact coordinate_558 A h
  · exact coordinate_559 A h

private lemma normalForm_row_20 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 20 c = normalForm A 20 c := by
  intro c
  fin_cases c
  · exact coordinate_560 A h
  · exact coordinate_561 A h
  · exact coordinate_562 A h
  · exact coordinate_563 A h
  · exact coordinate_564 A h
  · exact coordinate_565 A h
  · exact coordinate_566 A h
  · exact coordinate_567 A h
  · exact coordinate_568 A h
  · exact coordinate_569 A h
  · exact coordinate_570 A h
  · exact coordinate_571 A h
  · exact coordinate_572 A h
  · exact coordinate_573 A h
  · exact coordinate_574 A h
  · exact coordinate_575 A h
  · exact coordinate_576 A h
  · exact coordinate_577 A h
  · exact coordinate_578 A h
  · exact coordinate_579 A h
  · exact coordinate_580 A h
  · exact coordinate_581 A h
  · exact coordinate_582 A h
  · exact coordinate_583 A h
  · exact coordinate_584 A h
  · exact coordinate_585 A h
  · exact coordinate_586 A h
  · exact coordinate_587 A h

private lemma normalForm_row_21 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 21 c = normalForm A 21 c := by
  intro c
  fin_cases c
  · exact coordinate_588 A h
  · exact coordinate_589 A h
  · exact coordinate_590 A h
  · exact coordinate_591 A h
  · exact coordinate_592 A h
  · exact coordinate_593 A h
  · exact coordinate_594 A h
  · exact coordinate_595 A h
  · exact coordinate_596 A h
  · exact coordinate_597 A h
  · exact coordinate_598 A h
  · exact coordinate_599 A h
  · exact coordinate_600 A h
  · exact coordinate_601 A h
  · exact coordinate_602 A h
  · exact coordinate_603 A h
  · exact coordinate_604 A h
  · exact coordinate_605 A h
  · exact coordinate_606 A h
  · exact coordinate_607 A h
  · exact coordinate_608 A h
  · exact coordinate_609 A h
  · exact coordinate_610 A h
  · exact coordinate_611 A h
  · exact coordinate_612 A h
  · exact coordinate_613 A h
  · exact coordinate_614 A h
  · exact coordinate_615 A h

private lemma normalForm_row_22 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 22 c = normalForm A 22 c := by
  intro c
  fin_cases c
  · exact coordinate_616 A h
  · exact coordinate_617 A h
  · exact coordinate_618 A h
  · exact coordinate_619 A h
  · exact coordinate_620 A h
  · exact coordinate_621 A h
  · exact coordinate_622 A h
  · exact coordinate_623 A h
  · exact coordinate_624 A h
  · exact coordinate_625 A h
  · exact coordinate_626 A h
  · exact coordinate_627 A h
  · exact coordinate_628 A h
  · exact coordinate_629 A h
  · exact coordinate_630 A h
  · exact coordinate_631 A h
  · exact coordinate_632 A h
  · exact coordinate_633 A h
  · exact coordinate_634 A h
  · exact coordinate_635 A h
  · exact coordinate_636 A h
  · exact coordinate_637 A h
  · exact coordinate_638 A h
  · exact coordinate_639 A h
  · exact coordinate_640 A h
  · exact coordinate_641 A h
  · exact coordinate_642 A h
  · exact coordinate_643 A h

private lemma normalForm_row_23 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 23 c = normalForm A 23 c := by
  intro c
  fin_cases c
  · exact coordinate_644 A h
  · exact coordinate_645 A h
  · exact coordinate_646 A h
  · exact coordinate_647 A h
  · exact coordinate_648 A h
  · exact coordinate_649 A h
  · exact coordinate_650 A h
  · exact coordinate_651 A h
  · exact coordinate_652 A h
  · exact coordinate_653 A h
  · exact coordinate_654 A h
  · exact coordinate_655 A h
  · exact coordinate_656 A h
  · exact coordinate_657 A h
  · exact coordinate_658 A h
  · exact coordinate_659 A h
  · exact coordinate_660 A h
  · exact coordinate_661 A h
  · exact coordinate_662 A h
  · exact coordinate_663 A h
  · exact coordinate_664 A h
  · exact coordinate_665 A h
  · exact coordinate_666 A h
  · exact coordinate_667 A h
  · exact coordinate_668 A h
  · exact coordinate_669 A h
  · exact coordinate_670 A h
  · exact coordinate_671 A h

private lemma normalForm_row_24 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 24 c = normalForm A 24 c := by
  intro c
  fin_cases c
  · exact coordinate_672 A h
  · exact coordinate_673 A h
  · exact coordinate_674 A h
  · exact coordinate_675 A h
  · exact coordinate_676 A h
  · exact coordinate_677 A h
  · exact coordinate_678 A h
  · exact coordinate_679 A h
  · exact coordinate_680 A h
  · exact coordinate_681 A h
  · exact coordinate_682 A h
  · exact coordinate_683 A h
  · exact coordinate_684 A h
  · exact coordinate_685 A h
  · exact coordinate_686 A h
  · exact coordinate_687 A h
  · exact coordinate_688 A h
  · exact coordinate_689 A h
  · exact coordinate_690 A h
  · exact coordinate_691 A h
  · exact coordinate_692 A h
  · exact coordinate_693 A h
  · exact coordinate_694 A h
  · exact coordinate_695 A h
  · exact coordinate_696 A h
  · exact coordinate_697 A h
  · exact coordinate_698 A h
  · exact coordinate_699 A h

private lemma normalForm_row_25 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 25 c = normalForm A 25 c := by
  intro c
  fin_cases c
  · exact coordinate_700 A h
  · exact coordinate_701 A h
  · exact coordinate_702 A h
  · exact coordinate_703 A h
  · exact coordinate_704 A h
  · exact coordinate_705 A h
  · exact coordinate_706 A h
  · exact coordinate_707 A h
  · exact coordinate_708 A h
  · exact coordinate_709 A h
  · exact coordinate_710 A h
  · exact coordinate_711 A h
  · exact coordinate_712 A h
  · exact coordinate_713 A h
  · exact coordinate_714 A h
  · exact coordinate_715 A h
  · exact coordinate_716 A h
  · exact coordinate_717 A h
  · exact coordinate_718 A h
  · exact coordinate_719 A h
  · exact coordinate_720 A h
  · exact coordinate_721 A h
  · exact coordinate_722 A h
  · exact coordinate_723 A h
  · exact coordinate_724 A h
  · exact coordinate_725 A h
  · exact coordinate_726 A h
  · exact coordinate_727 A h

private lemma normalForm_row_26 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 26 c = normalForm A 26 c := by
  intro c
  fin_cases c
  · exact coordinate_728 A h
  · exact coordinate_729 A h
  · exact coordinate_730 A h
  · exact coordinate_731 A h
  · exact coordinate_732 A h
  · exact coordinate_733 A h
  · exact coordinate_734 A h
  · exact coordinate_735 A h
  · exact coordinate_736 A h
  · exact coordinate_737 A h
  · exact coordinate_738 A h
  · exact coordinate_739 A h
  · exact coordinate_740 A h
  · exact coordinate_741 A h
  · exact coordinate_742 A h
  · exact coordinate_743 A h
  · exact coordinate_744 A h
  · exact coordinate_745 A h
  · exact coordinate_746 A h
  · exact coordinate_747 A h
  · exact coordinate_748 A h
  · exact coordinate_749 A h
  · exact coordinate_750 A h
  · exact coordinate_751 A h
  · exact coordinate_752 A h
  · exact coordinate_753 A h
  · exact coordinate_754 A h
  · exact coordinate_755 A h

private lemma normalForm_row_27 (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) :
    ∀ c, A 27 c = normalForm A 27 c := by
  intro c
  fin_cases c
  · exact coordinate_756 A h
  · exact coordinate_757 A h
  · exact coordinate_758 A h
  · exact coordinate_759 A h
  · exact coordinate_760 A h
  · exact coordinate_761 A h
  · exact coordinate_762 A h
  · exact coordinate_763 A h
  · exact coordinate_764 A h
  · exact coordinate_765 A h
  · exact coordinate_766 A h
  · exact coordinate_767 A h
  · exact coordinate_768 A h
  · exact coordinate_769 A h
  · exact coordinate_770 A h
  · exact coordinate_771 A h
  · exact coordinate_772 A h
  · exact coordinate_773 A h
  · exact coordinate_774 A h
  · exact coordinate_775 A h
  · exact coordinate_776 A h
  · exact coordinate_777 A h
  · exact coordinate_778 A h
  · exact coordinate_779 A h
  · exact coordinate_780 A h
  · exact coordinate_781 A h
  · exact coordinate_782 A h
  · exact coordinate_783 A h

/-- The four genuine constant-root equations determine every matrix entry
from the five Cartan entries. -/
theorem eq_normalForm (A : Matrix (Fin 28) (Fin 28) F)
    (h : ∀ k, Commute A (constantMatrix k)) : A = normalForm A := by
  ext r c
  fin_cases r
  · exact normalForm_row_0 A h c
  · exact normalForm_row_1 A h c
  · exact normalForm_row_2 A h c
  · exact normalForm_row_3 A h c
  · exact normalForm_row_4 A h c
  · exact normalForm_row_5 A h c
  · exact normalForm_row_6 A h c
  · exact normalForm_row_7 A h c
  · exact normalForm_row_8 A h c
  · exact normalForm_row_9 A h c
  · exact normalForm_row_10 A h c
  · exact normalForm_row_11 A h c
  · exact normalForm_row_12 A h c
  · exact normalForm_row_13 A h c
  · exact normalForm_row_14 A h c
  · exact normalForm_row_15 A h c
  · exact normalForm_row_16 A h c
  · exact normalForm_row_17 A h c
  · exact normalForm_row_18 A h c
  · exact normalForm_row_19 A h c
  · exact normalForm_row_20 A h c
  · exact normalForm_row_21 A h c
  · exact normalForm_row_22 A h c
  · exact normalForm_row_23 A h c
  · exact normalForm_row_24 A h c
  · exact normalForm_row_25 A h c
  · exact normalForm_row_26 A h c
  · exact normalForm_row_27 A h c

end Triality.Standard.ElementaryCentralKernel.FixedRootCommutant
