module

public import Mathlib.LinearAlgebra.Matrix.Dual
public import Theory.AlgebraicGroup.RootSystems.Exceptional

/-!
# The standard root pairing of type F4

This module equips the 48 explicit roots in `StandardRootSystem.typeF4Roots` with the
Euclidean root-coroot pairing: pair roots have their usual coroot, while signed unit and
half-sign roots have twice their root as coroot.  The coordinate reflection calculations in
`Exceptional.lean` give reflection stability, and direct finite coordinate calculations prove
integrality and reducedness without appealing to root-system classification.

The four displayed simple roots form a base by their explicit simple-root coordinates.  Its
support is identified with `Fin 4`, its Cartan matrix is the standard `typeF4CartanMatrix`, and
the connected Cartan path proves irreducibility via the invariant-submodule criterion.
-/

namespace Theory.AlgebraicGroup.StandardRootSystem

open Set

private lemma dot_add_left_F4 (x y z : Vec 4) :
    dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

private lemma dot_add_right_F4 (x y z : Vec 4) :
    dot x (y + z) = dot x y + dot x z := by
  simp [dot, mul_add, Finset.sum_add_distrib]

private lemma dot_smul_left_F4 (c : ℝ) (x y : Vec 4) :
    dot (c • x) y = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_smul_right_F4 (c : ℝ) (x y : Vec 4) :
    dot x (c • y) = c * dot x y := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private lemma dot_neg_left_F4 (x y : Vec 4) : dot (-x) y = -dot x y := by
  simpa using dot_smul_left_F4 (-1) x y

private lemma dot_neg_right_F4 (x y : Vec 4) : dot x (-y) = -dot x y := by
  simpa using dot_smul_right_F4 (-1) x y

private lemma dot_basisVector_basisVector_F4 (i j : Fin 4) :
    dot (basisVector i) (basisVector j) = if i = j then 1 else 0 := by
  classical
  simp [dot, basisVector, Pi.single_apply, eq_comm]

private lemma dot_basisVector_right_F4 (x : Vec 4) (i : Fin 4) :
    dot x (basisVector i) = x i := by
  classical
  simp [dot, basisVector, Pi.single_apply]

private lemma dot_basisVector_left_F4 (i : Fin 4) (x : Vec 4) :
    dot (basisVector i) x = x i := by
  rw [dot_comm, dot_basisVector_right_F4]

public theorem typeF4Roots_finite : typeF4Roots.Finite := by
  have hB : (typeBRoots 4).Finite := Set.finite_coe_iff.mp
    (Finite.of_surjective (typeBRootEmbedding 4) (typeBRootEmbedding_surjective 4))
  rw [typeF4Roots]
  exact hB.union (Set.finite_range halfSignVector)

public instance typeF4Roots_finiteType : Finite typeF4Roots :=
  Set.finite_coe_iff.mpr typeF4Roots_finite

@[expose] public noncomputable def typeF4RootEmbedding : typeF4Roots ↪ Vec 4 :=
  Function.Embedding.subtype _

@[simp] public lemma typeF4RootEmbedding_apply (r : typeF4Roots) :
    typeF4RootEmbedding r = (r : Vec 4) := rfl

public lemma dot_smul_self_F4 (c : ℝ) (x : Vec 4) :
    dot (c • x) (c • x) = c ^ 2 * dot x x := by
  simp only [dot, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

public lemma typeF4Root_dot_self_of_pair (r : typeF4Roots)
    (hrPair : r.1 ∈ pairRoots 4) : dot r.1 r.1 = 2 := by
  classical
  rcases hrPair with ⟨i, j, hij, s, t, hs, ht, hroot⟩
  rw [hroot]
  simp only [dot_add_left_F4, dot_add_right_F4, dot_smul_left_F4,
    dot_smul_right_F4, dot_basisVector_basisVector_F4]
  have sign_cases (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) : x = -1 ∨ x = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  rcases sign_cases s hs with rfl | rfl <;> rcases sign_cases t ht with rfl | rfl
  all_goals norm_num [hij, hij.symm]

public lemma typeF4Root_dot_self_of_not_pair (r : typeF4Roots)
    (hrPair : r.1 ∉ pairRoots 4) : dot r.1 r.1 = 1 := by
  classical
  rcases r.2 with (hrPair' | hrUnit) | hrHalf
  · exact (hrPair hrPair').elim
  · rcases hrUnit with ⟨i, hi | hi⟩
    · rw [hi]
      rw [dot_basisVector_basisVector_F4, if_pos rfl]
    · rw [hi]
      rw [dot_neg_left_F4, dot_neg_right_F4, neg_neg,
        dot_basisVector_basisVector_F4, if_pos rfl]
  · rcases hrHalf with ⟨ε, hε⟩
    rw [← hε]
    cases h0 : ε 0 <;> cases h1 : ε 1 <;> cases h2 : ε 2 <;> cases h3 : ε 3 <;>
      norm_num [dot, halfSignVector, Fin.sum_univ_four, h0, h1, h2, h3]

@[expose] public noncomputable def typeF4CorootScale (r : typeF4Roots) : ℝ :=
  @ite ℝ (r.1 ∈ pairRoots 4) (Classical.propDecidable _) 1 2

public lemma typeF4CorootScale_of_pair (r : typeF4Roots)
    (hr : r.1 ∈ pairRoots 4) : typeF4CorootScale r = 1 := by
  simp [typeF4CorootScale, hr]

public lemma typeF4CorootScale_of_not_pair (r : typeF4Roots)
    (hr : r.1 ∉ pairRoots 4) : typeF4CorootScale r = 2 := by
  simp [typeF4CorootScale, hr]

@[expose] public noncomputable def typeF4CorootVector (r : typeF4Roots) : Vec 4 :=
  typeF4CorootScale r • r.1

public lemma typeF4CorootVector_injective : Function.Injective typeF4CorootVector := by
  classical
  intro r s h
  by_cases hr : r.1 ∈ pairRoots 4 <;> by_cases hs : s.1 ∈ pairRoots 4
  · have hv : r.1 = s.1 := by
      simpa only [typeF4CorootVector, typeF4CorootScale_of_pair r hr,
        typeF4CorootScale_of_pair s hs, one_smul] using h
    exact Subtype.ext hv
  · have hnorm := congrArg (fun x : Vec 4 => dot x x) h
    change dot (typeF4CorootScale r • r.1) (typeF4CorootScale r • r.1) =
      dot (typeF4CorootScale s • s.1) (typeF4CorootScale s • s.1) at hnorm
    rw [typeF4CorootScale_of_pair r hr,
      typeF4CorootScale_of_not_pair s hs, one_smul, dot_smul_self_F4,
      typeF4Root_dot_self_of_pair r hr, typeF4Root_dot_self_of_not_pair s hs] at hnorm
    norm_num at hnorm
  · have hnorm := congrArg (fun x : Vec 4 => dot x x) h
    change dot (typeF4CorootScale r • r.1) (typeF4CorootScale r • r.1) =
      dot (typeF4CorootScale s • s.1) (typeF4CorootScale s • s.1) at hnorm
    rw [typeF4CorootScale_of_not_pair r hr,
      typeF4CorootScale_of_pair s hs, one_smul, dot_smul_self_F4,
      typeF4Root_dot_self_of_not_pair r hr, typeF4Root_dot_self_of_pair s hs] at hnorm
    norm_num at hnorm
  · have h' : (2 : ℝ) • r.1 = (2 : ℝ) • s.1 := by
      simpa only [typeF4CorootVector, typeF4CorootScale_of_not_pair r hr,
        typeF4CorootScale_of_not_pair s hs] using h
    have hv := (isUnit_iff_ne_zero.mpr
      (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp h'
    exact Subtype.ext hv

@[expose] public noncomputable def typeF4CorootEmbedding : typeF4Roots ↪ Vec 4 :=
  ⟨typeF4CorootVector, typeF4CorootVector_injective⟩

@[simp] public lemma typeF4CorootEmbedding_apply (r : typeF4Roots) :
    typeF4CorootEmbedding r = typeF4CorootVector r := rfl

public noncomputable def typeF4CoordinatePairing :
    Vec 4 →ₗ[ℝ] Vec 4 →ₗ[ℝ] ℝ :=
  (dotProductEquiv ℝ (Fin 4)).toLinearMap

public instance typeF4CoordinatePairing_isPerfPair :
    typeF4CoordinatePairing.IsPerfPair := by
  unfold typeF4CoordinatePairing
  infer_instance

public lemma typeF4CoordinatePairing_apply (x y : Vec 4) :
    typeF4CoordinatePairing x y = dot x y := by
  simp [typeF4CoordinatePairing, dotProductEquiv, dot, dotProduct]

public lemma typeF4Root_coroot_self_pairing (r : typeF4Roots) :
    typeF4CoordinatePairing (typeF4RootEmbedding r) (typeF4CorootEmbedding r) = 2 := by
  classical
  rw [typeF4CoordinatePairing_apply]
  change dot r.1 (typeF4CorootVector r) = 2
  by_cases hr : r.1 ∈ pairRoots 4
  · rw [typeF4CorootVector, typeF4CorootScale_of_pair r hr, one_smul,
      typeF4Root_dot_self_of_pair r hr]
  · rw [typeF4CorootVector, typeF4CorootScale_of_not_pair r hr]
    rw [show dot r.1 ((2 : ℝ) • r.1) = 2 * dot r.1 r.1 by
      simp [dot, Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
    rw [typeF4Root_dot_self_of_not_pair r hr]
    norm_num

public lemma typeF4Root_preReflection_mapsTo (r : typeF4Roots) :
    MapsTo
      (Module.preReflection (typeF4RootEmbedding r)
        (typeF4CoordinatePairing.flip (typeF4CorootEmbedding r)))
      (range typeF4RootEmbedding) (range typeF4RootEmbedding) := by
  classical
  rintro _ ⟨s, rfl⟩
  have hmem := (typeF4Root_reflection_mapsTo r.1 r.2) s.2
  refine ⟨⟨_, hmem⟩, ?_⟩
  rw [Module.preReflection_apply]
  change (@ite (Vec 4) (r.1 ∈ pairRoots 4) (Classical.propDecidable _)
      (s.1 - dot r.1 s.1 • r.1) (s.1 - (2 * dot r.1 s.1) • r.1)) =
    s.1 - typeF4CoordinatePairing s.1 (typeF4CorootEmbedding r) • r.1
  rw [typeF4CoordinatePairing_apply]
  by_cases hr : r.1 ∈ pairRoots 4
  · simp [typeF4CorootEmbedding, typeF4CorootVector,
      typeF4CorootScale_of_pair r hr, hr, dot_comm]
  · rw [if_neg hr, typeF4CorootEmbedding_apply, typeF4CorootVector,
      typeF4CorootScale_of_not_pair r hr]
    rw [show dot s.1 ((2 : ℝ) • r.1) = 2 * dot r.1 s.1 by
      rw [dot_comm]
      simp [dot, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring]

public lemma typeF4RootEmbedding_span_eq_top :
    Submodule.span ℝ (range typeF4RootEmbedding) = ⊤ := by
  simpa [typeF4RootEmbedding] using typeF4Roots_span_eq_top

@[expose] public noncomputable def typeF4RootPairing :
    RootPairing typeF4Roots ℝ (Vec 4) (Vec 4) :=
  RootPairing.mk'' typeF4CoordinatePairing typeF4RootEmbedding typeF4CorootEmbedding
    typeF4Root_coroot_self_pairing typeF4Root_preReflection_mapsTo
    typeF4RootEmbedding_span_eq_top

@[simp] public lemma typeF4RootPairing_root (r : typeF4Roots) :
    typeF4RootPairing.root r = r.1 := rfl

@[simp] public lemma typeF4RootPairing_coroot (r : typeF4Roots) :
    typeF4RootPairing.coroot r = typeF4CorootScale r • r.1 := rfl

@[simp] public lemma typeF4RootPairing_pairing (r s : typeF4Roots) :
    typeF4RootPairing.pairing r s = typeF4CorootScale s * dot r.1 s.1 := by
  change typeF4CoordinatePairing r.1 (typeF4CorootEmbedding s) = _
  rw [typeF4CoordinatePairing_apply]
  rw [typeF4CorootEmbedding_apply, typeF4CorootVector]
  simp [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 2000000 in
public lemma typeF4RootPairing_pairing_eq_intCast (r s : typeF4Roots) :
    ∃ z : ℤ, (z : ℝ) = typeF4RootPairing.pairing r s := by
  classical
  have sign_cases (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) : x = -1 ∨ x = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have int_cases (x : ℝ)
      (hx : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2) :
      ∃ z : ℤ, (z : ℝ) = x := by
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨-2, by norm_num⟩
    · exact ⟨-1, by norm_num⟩
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
  rw [typeF4RootPairing_pairing]
  by_cases hsPair : s.1 ∈ pairRoots 4
  · rw [typeF4CorootScale_of_pair s hsPair, one_mul]
    rcases hsPair with ⟨i, j, hij, a, b, ha, hb, hs⟩
    rcases r.2 with (hrPair | hrUnit) | hrHalf
    · rcases hrPair with ⟨k, l, hkl, c, d, hc, hd, hr⟩
      rw [hs, hr]
      simp only [dot_add_left_F4, dot_add_right_F4, dot_smul_left_F4,
        dot_smul_right_F4, dot_basisVector_basisVector_F4]
      rcases sign_cases a ha with rfl | rfl <;>
        rcases sign_cases b hb with rfl | rfl <;>
        rcases sign_cases c hc with rfl | rfl <;>
        rcases sign_cases d hd with rfl | rfl
      all_goals apply int_cases
      all_goals split_ifs <;> simp_all <;> norm_num
    · rcases hrUnit with ⟨k, hk | hk⟩
      all_goals rw [hs, hk]
      all_goals
        simp only [dot_neg_left_F4, dot_add_right_F4, dot_smul_right_F4,
          dot_basisVector_basisVector_F4]
      all_goals
        rcases sign_cases a ha with rfl | rfl <;> rcases sign_cases b hb with rfl | rfl
      all_goals apply int_cases
      all_goals split_ifs <;> simp_all <;> norm_num
    · rcases hrHalf with ⟨ε, hε⟩
      rw [hs, ← hε]
      simp only [dot_add_right_F4, dot_smul_right_F4, dot_basisVector_right_F4]
      rcases sign_cases a ha with rfl | rfl <;> rcases sign_cases b hb with rfl | rfl
      all_goals cases hi : ε i <;> cases hj : ε j
      all_goals apply int_cases
      all_goals norm_num [halfSignVector, hi, hj]
  · rw [typeF4CorootScale_of_not_pair s hsPair]
    rcases s.2 with (hsPair' | hsUnit) | hsHalf
    · exact (hsPair hsPair').elim
    · rcases hsUnit with ⟨i, hi | hi⟩
      · rw [hi]
        rcases r.2 with (hrPair | hrUnit) | hrHalf
        · rcases hrPair with ⟨k, l, hkl, c, d, hc, hd, hr⟩
          rw [hr]
          simp only [dot_add_left_F4, dot_smul_left_F4,
            dot_basisVector_basisVector_F4]
          rcases sign_cases c hc with rfl | rfl <;> rcases sign_cases d hd with rfl | rfl
          all_goals apply int_cases
          all_goals split_ifs <;> simp_all <;> norm_num
        · rcases hrUnit with ⟨k, hk | hk⟩
          · rw [hk, dot_basisVector_basisVector_F4]
            apply int_cases
            split_ifs <;> norm_num
          · rw [hk, dot_neg_left_F4, dot_basisVector_basisVector_F4]
            apply int_cases
            split_ifs <;> norm_num
        · rcases hrHalf with ⟨ε, hε⟩
          rw [← hε, dot_basisVector_right_F4]
          cases he : ε i <;> apply int_cases <;>
            norm_num [halfSignVector, he]
      · rw [hi]
        rcases r.2 with (hrPair | hrUnit) | hrHalf
        · rcases hrPair with ⟨k, l, hkl, c, d, hc, hd, hr⟩
          rw [hr, dot_neg_right_F4]
          simp only [dot_add_left_F4, dot_smul_left_F4,
            dot_basisVector_basisVector_F4]
          rcases sign_cases c hc with rfl | rfl <;> rcases sign_cases d hd with rfl | rfl
          all_goals apply int_cases
          all_goals split_ifs <;> simp_all <;> norm_num
        · rcases hrUnit with ⟨k, hk | hk⟩
          · rw [hk, dot_neg_right_F4, dot_basisVector_basisVector_F4]
            apply int_cases
            split_ifs <;> norm_num
          · rw [hk, dot_neg_left_F4, dot_neg_right_F4,
              dot_basisVector_basisVector_F4]
            apply int_cases
            split_ifs <;> norm_num
        · rcases hrHalf with ⟨ε, hε⟩
          rw [← hε, dot_neg_right_F4, dot_basisVector_right_F4]
          cases he : ε i <;> apply int_cases <;>
            norm_num [halfSignVector, he]
    · rcases hsHalf with ⟨ε, hε⟩
      rw [← hε]
      rcases r.2 with (hrPair | hrUnit) | hrHalf
      · rcases hrPair with ⟨k, l, hkl, c, d, hc, hd, hr⟩
        rw [hr]
        simp only [dot_add_left_F4, dot_smul_left_F4, dot_basisVector_left_F4]
        rcases sign_cases c hc with rfl | rfl <;> rcases sign_cases d hd with rfl | rfl
        all_goals cases hk : ε k <;> cases hl : ε l
        all_goals apply int_cases
        all_goals norm_num [halfSignVector, hk, hl]
      · rcases hrUnit with ⟨k, hk | hk⟩
        · rw [hk, dot_basisVector_left_F4]
          cases he : ε k <;> apply int_cases <;>
            norm_num [halfSignVector, he]
        · rw [hk, dot_neg_left_F4, dot_basisVector_left_F4]
          cases he : ε k <;> apply int_cases <;>
            norm_num [halfSignVector, he]
      · rcases hrHalf with ⟨δ, hδ⟩
        rw [← hδ]
        cases hε0 : ε 0 <;> cases hε1 : ε 1 <;> cases hε2 : ε 2 <;>
          cases hε3 : ε 3 <;> cases hδ0 : δ 0 <;> cases hδ1 : δ 1 <;>
          cases hδ2 : δ 2 <;> cases hδ3 : δ 3 <;>
          apply int_cases <;>
          norm_num [dot, halfSignVector, Fin.sum_univ_four,
            hε0, hε1, hε2, hε3, hδ0, hδ1, hδ2, hδ3]

public instance typeF4RootPairing_isCrystallographic :
    typeF4RootPairing.IsCrystallographic := by
  constructor
  exact typeF4RootPairing_pairing_eq_intCast

public instance typeF4RootPairing_isRootSystem : typeF4RootPairing.IsRootSystem := by
  unfold typeF4RootPairing
  apply RootPairing.isRootSystem_mk''
  exact typeF4RootPairing_pairing_eq_intCast

public lemma typeF4Int_sq_ne_two (z : ℤ) : z ^ 2 ≠ 2 := by
  intro h
  have hlo : (-2 : ℤ) < z := by nlinarith [sq_nonneg (z + 2)]
  have hhi : z < 2 := by nlinarith [sq_nonneg (z - 2)]
  interval_cases z <;> norm_num at h

public lemma typeF4Int_sq_ne_eight (z : ℤ) : z ^ 2 ≠ 8 := by
  intro h
  have hlo : (-3 : ℤ) < z := by nlinarith [sq_nonneg (z + 3)]
  have hhi : z < 3 := by nlinarith [sq_nonneg (z - 3)]
  interval_cases z <;> norm_num at h

public instance typeF4RootPairing_isReduced : typeF4RootPairing.IsReduced := by
  constructor
  intro r s hdep
  have hsmul := typeF4RootPairing.pairing_smul_root_eq_of_not_linearIndependent hdep
  simp only [typeF4RootPairing_root] at hsmul
  change typeF4RootPairing.pairing s r • r.1 = (2 : ℝ) • s.1 at hsmul
  have hnorm := congrArg (fun x : Vec 4 => dot x x) hsmul
  rw [dot_smul_self_F4, dot_smul_self_F4] at hnorm
  obtain ⟨z, hz⟩ := typeF4RootPairing_pairing_eq_intCast s r
  by_cases hr : r.1 ∈ pairRoots 4 <;> by_cases hs : s.1 ∈ pairRoots 4
  · rw [typeF4Root_dot_self_of_pair r hr, typeF4Root_dot_self_of_pair s hs] at hnorm
    have hc : typeF4RootPairing.pairing s r = 2 ∨
        typeF4RootPairing.pairing s r = -2 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num at hnorm ⊢
      nlinarith
    rcases hc with hc | hc
    · left
      rw [hc] at hsmul
      exact (isUnit_iff_ne_zero.mpr
        (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
    · right
      rw [hc] at hsmul
      have hneg : (2 : ℝ) • (-r.1) = (2 : ℝ) • s.1 := by
        rw [smul_neg, ← neg_smul]
        exact hsmul
      exact neg_eq_iff_eq_neg.mp ((isUnit_iff_ne_zero.mpr
        (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hneg)
  · rw [typeF4Root_dot_self_of_pair r hr,
      typeF4Root_dot_self_of_not_pair s hs] at hnorm
    exfalso
    rw [← hz] at hnorm
    have hzsqReal : (z : ℝ) ^ 2 = 2 := by nlinarith
    have hzsq : z ^ 2 = 2 := by exact_mod_cast hzsqReal
    exact typeF4Int_sq_ne_two z hzsq
  · rw [typeF4Root_dot_self_of_not_pair r hr,
      typeF4Root_dot_self_of_pair s hs] at hnorm
    exfalso
    rw [← hz] at hnorm
    have hzsqReal : (z : ℝ) ^ 2 = 8 := by nlinarith
    have hzsq : z ^ 2 = 8 := by exact_mod_cast hzsqReal
    exact typeF4Int_sq_ne_eight z hzsq
  · rw [typeF4Root_dot_self_of_not_pair r hr,
      typeF4Root_dot_self_of_not_pair s hs] at hnorm
    have hc : typeF4RootPairing.pairing s r = 2 ∨
        typeF4RootPairing.pairing s r = -2 := by
      apply eq_or_eq_neg_of_sq_eq_sq
      norm_num at hnorm ⊢
      nlinarith
    rcases hc with hc | hc
    · left
      rw [hc] at hsmul
      exact (isUnit_iff_ne_zero.mpr
        (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hsmul
    · right
      rw [hc] at hsmul
      have hneg : (2 : ℝ) • (-r.1) = (2 : ℝ) • s.1 := by
        rw [smul_neg, ← neg_smul]
        exact hsmul
      exact neg_eq_iff_eq_neg.mp ((isUnit_iff_ne_zero.mpr
        (show (2 : ℝ) ≠ 0 by norm_num)).smul_left_cancel.mp hneg)

@[expose] public noncomputable def typeF4SimpleRootIndex (i : Fin 4) : typeF4Roots :=
  ⟨typeF4SimpleRoot i, typeF4SimpleRoot_mem_typeF4Roots i⟩

@[simp] public lemma typeF4SimpleRootIndex_val (i : Fin 4) :
    (typeF4SimpleRootIndex i : Vec 4) = typeF4SimpleRoot i := rfl

public lemma typeF4SimpleRootIndex_injective : Function.Injective typeF4SimpleRootIndex := by
  intro i j h
  have hv := congrArg Subtype.val h
  have hs := congrArg
    (fun x : Vec 4 => 2 * x 0 + 4 * x 1 + 8 * x 2 + 16 * x 3) hv
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals
    norm_num [typeF4SimpleRootIndex, typeF4SimpleRoot,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three] at hs

public lemma typeF4SimpleRootIndex_mem_pair_iff (i : Fin 4) :
    (typeF4SimpleRootIndex i : Vec 4) ∈ pairRoots 4 ↔ i.val < 2 := by
  constructor
  · intro h
    fin_cases i
    · norm_num
    · norm_num
    · have hnorm := typeF4Root_dot_self_of_pair (typeF4SimpleRootIndex 2) h
      rw [typeF4SimpleRootIndex_val, typeF4SimpleRoot_normSq] at hnorm
      norm_num at hnorm
    · have hnorm := typeF4Root_dot_self_of_pair (typeF4SimpleRootIndex 3) h
      rw [typeF4SimpleRootIndex_val, typeF4SimpleRoot_normSq] at hnorm
      norm_num at hnorm
  · intro h
    fin_cases i
    · refine ⟨1, 2, by decide, 1, -1, by simp, by simp, ?_⟩
      ext k
      fin_cases k <;> norm_num [typeF4SimpleRootIndex, typeF4SimpleRoot,
        basisVector, Pi.single_apply, Fin.ext_iff]
    · refine ⟨2, 3, by decide, 1, -1, by simp, by simp, ?_⟩
      ext k
      fin_cases k <;> norm_num [typeF4SimpleRootIndex, typeF4SimpleRoot,
        basisVector, Pi.single_apply, Fin.ext_iff]
    · norm_num at h
    · norm_num at h

public lemma typeF4CorootScale_simpleRoot (i : Fin 4) :
    typeF4CorootScale (typeF4SimpleRootIndex i) = if i.val < 2 then 1 else 2 := by
  by_cases hi : i.val < 2
  · rw [if_pos hi, typeF4CorootScale_of_pair]
    exact (typeF4SimpleRootIndex_mem_pair_iff i).mpr hi
  · rw [if_neg hi, typeF4CorootScale_of_not_pair]
    exact fun h => hi ((typeF4SimpleRootIndex_mem_pair_iff i).mp h)

public lemma typeF4RootPairing_simpleIndex_pairing (i j : Fin 4) :
    typeF4RootPairing.pairing (typeF4SimpleRootIndex i) (typeF4SimpleRootIndex j) =
      algebraMap ℤ ℝ (typeF4CartanMatrix i j) := by
  rw [typeF4RootPairing_pairing, typeF4CorootScale_simpleRoot]
  simp only [typeF4SimpleRootIndex_val]
  change _ = (typeF4CartanMatrix i j : ℝ)
  have h := typeF4SimpleRoot_pairing i j
  by_cases hj : j.val < 2
  · rw [if_pos hj] at h ⊢
    simpa only [one_mul] using h
  · rw [if_neg hj] at h ⊢
    exact h

public lemma typeF4SimpleRoots_linearIndependent :
    LinearIndependent ℝ (fun i : Fin 4 => typeF4RootPairing.root (typeF4SimpleRootIndex i)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have h0 := congrFun hg (0 : Fin 4)
  have h1 := congrFun hg (1 : Fin 4)
  have h2 := congrFun hg (2 : Fin 4)
  have h3 := congrFun hg (3 : Fin 4)
  simp [typeF4RootPairing_root, typeF4SimpleRootIndex, typeF4SimpleRoot,
    Fin.sum_univ_four] at h0 h1 h2 h3
  have hg0 : g (0 : Fin 4) = 0 := by linarith
  have hg1 : g (1 : Fin 4) = 0 := by linarith
  have hg2 : g (2 : Fin 4) = 0 := by linarith
  have hg3 : g (3 : Fin 4) = 0 := by linarith
  fin_cases i
  · exact hg0
  · exact hg1
  · exact hg2
  · exact hg3

public lemma typeF4RootPairing_linearIndepOn_simpleRoots :
    LinearIndepOn ℝ typeF4RootPairing.root (Set.range typeF4SimpleRootIndex) := by
  rw [linearIndepOn_range_iff typeF4SimpleRootIndex_injective]
  simpa [Function.comp_def] using typeF4SimpleRoots_linearIndependent

@[expose] public noncomputable def typeF4SimpleCoefficient (x : Vec 4) : Fin 4 → ℝ
  | ⟨0, _⟩ => x 0 + x 1
  | ⟨1, _⟩ => 2 * x 0 + x 1 + x 2
  | ⟨2, _⟩ => 3 * x 0 + x 1 + x 2 + x 3
  | ⟨3, _⟩ => 2 * x 0

public lemma typeF4SimpleCoefficient_reconstruction (x : Vec 4) :
    (∑ i, typeF4SimpleCoefficient x i • typeF4SimpleRoot i) = x := by
  funext ⟨k, hk⟩
  interval_cases k <;>
    norm_num [typeF4SimpleCoefficient, typeF4SimpleRoot, Fin.sum_univ_four] <;>
      ring_nf <;> congr

set_option linter.unusedSimpArgs false in
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option maxHeartbeats 800000 in
public lemma typeF4Root_simpleCoefficients_nat_or_neg (r : typeF4Roots) :
    (∀ i, ∃ n : ℕ, typeF4SimpleCoefficient r.1 i = n) ∨
      (∀ i, ∃ n : ℕ, typeF4SimpleCoefficient (-r.1) i = n) := by
  classical
  have sign_cases (x : ℝ) (hx : x ∈ ({-1, 1} : Set ℝ)) : x = -1 ∨ x = 1 := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
  have coeff_nat (x : ℝ)
      (hx : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4) :
      ∃ n : ℕ, x = n := by
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by norm_num⟩
    · exact ⟨1, by norm_num⟩
    · exact ⟨2, by norm_num⟩
    · exact ⟨3, by norm_num⟩
    · exact ⟨4, by norm_num⟩
  rcases r.2 with (hrPair | hrUnit) | hrHalf
  · rcases hrPair with ⟨i, j, hij, a, b, ha, hb, hr⟩
    rw [hr]
    rcases sign_cases a ha with ha | ha <;> rcases sign_cases b hb with hb | hb
    all_goals rw [ha, hb]
    all_goals fin_cases i <;> fin_cases j
    all_goals
      first
      | exact (hij rfl).elim
      | (left; intro k; fin_cases k <;> apply coeff_nat <;>
          simp [typeF4SimpleCoefficient, basisVector] <;> norm_num <;> done)
      | (right; intro k; fin_cases k <;> apply coeff_nat <;>
          simp [typeF4SimpleCoefficient, basisVector] <;> norm_num <;> done)
  · rcases hrUnit with ⟨i, hi | hi⟩
    · rw [hi]
      fin_cases i <;>
        first
        | (left; intro k; fin_cases k <;> apply coeff_nat <;>
            simp [typeF4SimpleCoefficient, basisVector] <;> norm_num <;> done)
        | (right; intro k; fin_cases k <;> apply coeff_nat <;>
            simp [typeF4SimpleCoefficient, basisVector] <;> norm_num <;> done)
    · rw [hi]
      fin_cases i <;>
        first
        | (left; intro k; fin_cases k <;> apply coeff_nat <;>
            simp [typeF4SimpleCoefficient, basisVector] <;> norm_num <;> done)
        | (right; intro k; fin_cases k <;> apply coeff_nat <;>
            simp [typeF4SimpleCoefficient, basisVector] <;> norm_num <;> done)
  · rcases hrHalf with ⟨ε, hε⟩
    rw [← hε]
    cases h0 : ε 0 <;> cases h1 : ε 1 <;> cases h2 : ε 2 <;> cases h3 : ε 3 <;>
      first
      | (left; intro k; fin_cases k <;> apply coeff_nat <;>
          norm_num [typeF4SimpleCoefficient, halfSignVector, h0, h1, h2, h3] <;> done)
      | (right; intro k; fin_cases k <;> apply coeff_nat <;>
          norm_num [typeF4SimpleCoefficient, halfSignVector, h0, h1, h2, h3] <;> done)

@[expose] public noncomputable def typeF4SimpleClosure : AddSubmonoid (Vec 4) :=
  AddSubmonoid.closure (typeF4RootPairing.root '' Set.range typeF4SimpleRootIndex)

public lemma typeF4SimpleRoot_mem_simpleClosure (i : Fin 4) :
    typeF4RootPairing.root (typeF4SimpleRootIndex i) ∈ typeF4SimpleClosure := by
  apply AddSubmonoid.subset_closure
  exact ⟨_, ⟨i, rfl⟩, rfl⟩

public lemma typeF4RootPairing_root_mem_or_neg_mem_simpleClosure (r : typeF4Roots) :
    typeF4RootPairing.root r ∈
        AddSubmonoid.closure (typeF4RootPairing.root '' Set.range typeF4SimpleRootIndex) ∨
      -typeF4RootPairing.root r ∈
        AddSubmonoid.closure (typeF4RootPairing.root '' Set.range typeF4SimpleRootIndex) := by
  change typeF4RootPairing.root r ∈ typeF4SimpleClosure ∨
    -typeF4RootPairing.root r ∈ typeF4SimpleClosure
  rcases typeF4Root_simpleCoefficients_nat_or_neg r with hpos | hneg
  · left
    choose n hn using hpos
    have hmem : ∑ i, n i • typeF4RootPairing.root (typeF4SimpleRootIndex i) ∈
        typeF4SimpleClosure :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem typeF4SimpleClosure (typeF4SimpleRoot_mem_simpleClosure i) (n i)
    convert hmem using 1
    simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
    rw [← typeF4SimpleCoefficient_reconstruction r.1]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← hn i]
  · right
    choose n hn using hneg
    have hmem : ∑ i, n i • typeF4RootPairing.root (typeF4SimpleRootIndex i) ∈
        typeF4SimpleClosure :=
      AddSubmonoid.sum_mem _ fun i _ =>
        AddSubmonoid.nsmul_mem typeF4SimpleClosure (typeF4SimpleRoot_mem_simpleClosure i) (n i)
    convert hmem using 1
    simp only [typeF4RootPairing_root, typeF4SimpleRootIndex_val]
    rw [← typeF4SimpleCoefficient_reconstruction (-r.1)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← hn i]

/-- The displayed type `F₄` base in the standard Bourbaki order. -/
@[expose] public noncomputable def typeF4RootPairing_base : typeF4RootPairing.Base :=
  RootPairing.Base.mk' typeF4RootPairing (Set.range typeF4SimpleRootIndex)
    typeF4RootPairing_linearIndepOn_simpleRoots
    typeF4RootPairing_root_mem_or_neg_mem_simpleClosure

public lemma typeF4RootPairing_base_support :
    (typeF4RootPairing_base.support : Set typeF4Roots) =
      Set.range typeF4SimpleRootIndex := by
  simp [typeF4RootPairing_base, RootPairing.Base.mk']

@[expose] public noncomputable def typeF4RootPairing_baseEquiv :
    Fin 4 ≃ typeF4RootPairing_base.support :=
  (Equiv.ofInjective typeF4SimpleRootIndex typeF4SimpleRootIndex_injective).trans
    (Equiv.setCongr typeF4RootPairing_base_support.symm)

@[simp] public lemma typeF4RootPairing_baseEquiv_val (i : Fin 4) :
    (typeF4RootPairing_baseEquiv i : typeF4Roots) = typeF4SimpleRootIndex i := rfl

public lemma typeF4RootPairing_base_cartan_apply (i j : Fin 4) :
    typeF4RootPairing_base.cartanMatrix
        (typeF4RootPairing_baseEquiv i) (typeF4RootPairing_baseEquiv j) =
      typeF4CartanMatrix i j := by
  apply FaithfulSMul.algebraMap_injective ℤ ℝ
  rw [RootPairing.Base.algebraMap_cartanMatrixIn_apply]
  rw [typeF4RootPairing_baseEquiv_val, typeF4RootPairing_baseEquiv_val]
  exact typeF4RootPairing_simpleIndex_pairing i j

/-- The displayed base has exactly the standard type `F₄` Cartan matrix. -/
public theorem typeF4RootPairing_base_cartan :
    typeF4RootPairing_base.cartanMatrix.reindex
        typeF4RootPairing_baseEquiv.symm typeF4RootPairing_baseEquiv.symm =
      typeF4CartanMatrix := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact typeF4RootPairing_base_cartan_apply i j

public lemma typeF4Cartan_connected (i j : Fin 4) :
    Relation.ReflTransGen (fun u v : Fin 4 => typeF4CartanMatrix u v ≠ 0) i j := by
  let edge := fun u v : Fin 4 => typeF4CartanMatrix u v ≠ 0
  have h01 : edge 0 1 := by norm_num [edge, typeF4CartanMatrix]
  have h10 : edge 1 0 := by norm_num [edge, typeF4CartanMatrix]
  have h12 : edge 1 2 := by norm_num [edge, typeF4CartanMatrix, Fin.ext_iff]
  have h21 : edge 2 1 := by norm_num [edge, typeF4CartanMatrix, Fin.ext_iff]
  have h23 : edge 2 3 := by norm_num [edge, typeF4CartanMatrix, Fin.ext_iff]
  have h32 : edge 3 2 := by norm_num [edge, typeF4CartanMatrix, Fin.ext_iff]
  have hto : ∀ k : Fin 4, Relation.ReflTransGen edge k 0 := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h10
    · exact (Relation.ReflTransGen.single h21).tail h10
    · exact ((Relation.ReflTransGen.single h32).tail h21).tail h10
  have hfrom : ∀ k : Fin 4, Relation.ReflTransGen edge 0 k := by
    intro k
    fin_cases k
    · exact .refl
    · exact .single h01
    · exact (Relation.ReflTransGen.single h01).tail h12
    · exact ((Relation.ReflTransGen.single h01).tail h12).tail h23
  exact (hto i).trans (hfrom j)

public lemma typeF4RootPairing_base_cartan_connected
    (s t : typeF4RootPairing_base.support) :
    Relation.ReflTransGen
      (fun u v : typeF4RootPairing_base.support =>
        typeF4RootPairing_base.cartanMatrix u v ≠ 0) s t := by
  rw [← typeF4RootPairing_baseEquiv.apply_symm_apply s,
    ← typeF4RootPairing_baseEquiv.apply_symm_apply t]
  exact Relation.ReflTransGen.lift typeF4RootPairing_baseEquiv
    (fun i j h => by
      change typeF4RootPairing_base.cartanMatrix
        (typeF4RootPairing_baseEquiv i) (typeF4RootPairing_baseEquiv j) ≠ 0
      rw [typeF4RootPairing_base_cartan_apply]
      exact h)
    _ _ (typeF4Cartan_connected _ _)

public instance typeF4RootPairing_isIrreducible : typeF4RootPairing.IsIrreducible :=
  isIrreducible_of_cartan_connected typeF4RootPairing typeF4RootPairing_base
    ⟨(typeF4RootPairing_baseEquiv 0 : typeF4Roots),
      (typeF4RootPairing_baseEquiv 0).property⟩
    typeF4RootPairing_base_cartan_connected

end Theory.AlgebraicGroup.StandardRootSystem
