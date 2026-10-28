module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.PointTransport
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover.Determinant
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
public import Mathlib.GroupTheory.Index
/-!
# The isotropic-point index in binary special unitary four-space

The literal setwise stabilizer of the first coordinate line has index
`(q³ + 1) (q² + 1)` over a field of order `q²`, where `q = 2ⁿ` and `n > 0`.
Every isotropic line has a unique representative with last nonzero coordinate
one. The four charts have sizes `q⁵`, `q³`, `q²`, and `1`; the largest is
parametrized by the existing Hermitian radical coordinates. Unitary point
transport and scalar determinant correction identify these lines with the
orbit of the coordinate line under the actual SU group. Orbit–stabilizer then
computes the index of `UnitaryFourFlag.pointParabolicSU`.

This supplies the geometric premise of the split-primary covering argument
supporting Aschbacher–Smith I.1.1–4, printed pp.407–408 of `refs/quasithin.pdf`,
and GLS3 §6.1. The reused point transport and determinant correction implement
GLS3 Lemmas 2.7.1–2.7.2 (`refs/KGroup/GLS3/chapter2.tex`). No ambient group
order or transitivity assumption is required, and the result includes `q = 2`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourConverse.TwoLocalCover
open scoped Pointwise
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointIndex
variable {F : Type*} [Field F]
local notation "V" => (Fin 4 → F)

/-- One-dimensional totally isotropic subspaces for the stored Hermitian form. -/
@[expose] def IsotropicLine (J : HermitianForm 4 F) :=
  {W : Submodule F V // Module.finrank F W = 1 ∧ W ≤ orthogonal J W}

private theorem standard_pairing (σ : F ≃+* F) (hσ : Function.Involutive σ) (x y : V) :
    pairing (form F σ hσ) x y =
      σ (x 0) * y 3 + σ (x 1) * y 2 + σ (x 2) * y 1 + σ (x 3) * y 0 := by
  simp [pairing, form, gram, mulVec, dotProduct, Fin.sum_univ_succ]
  ring

private def Normalized (v : V) : Prop :=
  v 3 = 1 ∨ (v 3 = 0 ∧ v 2 = 1) ∨
    (v 3 = 0 ∧ v 2 = 0 ∧ v 1 = 1) ∨
    (v 3 = 0 ∧ v 2 = 0 ∧ v 1 = 0 ∧ v 0 = 1)

private theorem normalized_ne_zero {v : V} (h : Normalized v) : v ≠ 0 := by
  intro hv
  subst v
  simp [Normalized] at h

private theorem normalized_smul_unique {v w : V}
    (hv : Normalized v) (hw : Normalized w) {a : F} (h : a • v = w) : v = w := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [Pi.smul_apply, smul_eq_mul] at h0 h1 h2 h3
  have ha : a ≠ 0 := by
    intro ha
    have hw0 : w = 0 := by simpa [ha] using h.symm
    exact normalized_ne_zero hw hw0
  have ha1 : a = 1 := by
    rcases hv with hv | ⟨hv3,hv⟩ | ⟨hv3,hv2,hv⟩ | ⟨hv3,hv2,hv1,hv⟩ <;>
      rcases hw with hw | ⟨hw3,hw⟩ | ⟨hw3,hw2,hw⟩ | ⟨hw3,hw2,hw1,hw⟩ <;>
      grind
  simpa [ha1] using h

variable (F) (σ : F ≃+* F)
private def Charts := RadicalCoordinates F σ ⊕ ((F × FixedBy.subfield F σ) ⊕ (F ⊕ Unit))

private def chartVector : Charts F σ → V
  | .inl c => ![c.z, c.x, c.y, 1]
  | .inr (.inl p) => ![p.1, p.2.val, 1, 0]
  | .inr (.inr (.inl a)) => ![a, 1, 0, 0]
  | .inr (.inr (.inr _)) => ![1, 0, 0, 0]

private theorem chartVector_normalized (c : Charts F σ) : Normalized (chartVector F σ c) := by
  rcases c with c | p | a | u <;> simp [chartVector, Normalized]

private theorem chartVector_injective : Function.Injective (chartVector F σ) := by
  intro c d h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  rcases c with c | ⟨a,b⟩ | a | u <;>
    rcases d with d | ⟨e,f⟩ | e | t <;>
    simp [chartVector] at h0 h1 h2 h3
  · cases c with
    | mk x y z ht =>
      cases d with
      | mk x' y' z' ht' =>
        change z = z' at h0
        change x = x' at h1
        change y = y' at h2
        subst x'
        subst y'
        subst z'
        rfl
  · congr
  · exact congrArg (fun a : F => (.inr (.inr (.inl a)) : Charts F σ)) h0
  · cases u
    cases t
    rfl

variable (hσ : Function.Involutive σ) [CharP F 2]
private theorem chartVector_isotropic (c : Charts F σ) :
    pairing (form F σ hσ) (chartVector F σ c) (chartVector F σ c) = 0 := by
  rcases c with c | ⟨a,b⟩ | a | u
  · simp only [standard_pairing]
    change σ c.z * 1 + σ c.x * c.y + σ c.y * c.x + σ 1 * c.z = 0
    rw [map_one, mul_one, one_mul]
    calc
      σ c.z + σ c.x * c.y + σ c.y * c.x + c.z =
          (c.z + σ c.z) + (σ c.x * c.y + σ c.y * c.x) := by ring
      _ = 0 := by rw [c.trace_eq, CharTwo.add_self_eq_zero]
  · have hb : σ b.val = b.val := b.property
    simp [chartVector, standard_pairing, hb, CharTwo.add_self_eq_zero]
  · simp [chartVector, standard_pairing]
  · simp [chartVector, standard_pairing]

omit [CharP F 2] in
private theorem span_isotropic {J : HermitianForm 4 F} {v : V}
    (hv : pairing J v v = 0) : Submodule.span F {v} ≤ orthogonal J (Submodule.span F {v}) := by
  intro x hx y hy
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b,rfl⟩ := Submodule.mem_span_singleton.mp hy
  simp only [pairing_smul_left, pairing_smul_right, hv, mul_zero]

private def chartLine (c : Charts F σ) : IsotropicLine (form F σ hσ) :=
  ⟨Submodule.span F {chartVector F σ c},
    finrank_span_singleton (normalized_ne_zero (chartVector_normalized F σ c)),
    span_isotropic F (chartVector_isotropic F σ hσ c)⟩

private theorem chartLine_injective : Function.Injective (chartLine F σ hσ) := by
  intro c d h
  apply chartVector_injective F σ
  have hm : chartVector F σ d ∈ Submodule.span F {chartVector F σ c} := by
    rw [show Submodule.span F {chartVector F σ c} = Submodule.span F {chartVector F σ d}
      from congrArg Subtype.val h]
    exact Submodule.subset_span (by simp)
  obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hm
  exact normalized_smul_unique (chartVector_normalized F σ c) (chartVector_normalized F σ d) ha

private theorem normalized_is_chart {v : V} (hv : Normalized v)
    (hi : pairing (form F σ hσ) v v = 0) : ∃ c, chartVector F σ c = v := by
  rw [standard_pairing] at hi
  rcases hv with hv | ⟨hv3,hv⟩ | ⟨hv3,hv2,hv⟩ | ⟨hv3,hv2,hv1,hv⟩
  · have ht : v 0 + σ (v 0) = σ (v 1) * v 2 + σ (v 2) * v 1 := by
      simp only [hv, map_one, mul_one, one_mul] at hi
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hi
    refine ⟨.inl ⟨v 1,v 2,v 0,ht⟩, ?_⟩
    ext i
    fin_cases i <;> simp [chartVector, hv]
  · have hb : σ (v 1) = v 1 := by
      simp only [hv3, hv, map_zero, map_one, mul_zero, zero_mul, mul_one,
        one_mul, zero_add, add_zero] at hi
      exact (eq_neg_iff_add_eq_zero.mpr hi).trans (CharTwo.neg_eq _)
    refine ⟨.inr (.inl (v 0,⟨v 1,hb⟩)), ?_⟩
    ext i
    fin_cases i <;> simp [chartVector, hv, hv3]
  · refine ⟨.inr (.inr (.inl (v 0))), ?_⟩
    ext i
    fin_cases i <;> simp [chartVector, hv, hv3, hv2]
  · refine ⟨.inr (.inr (.inr ())), ?_⟩
    ext i
    fin_cases i <;> simp [chartVector, hv, hv3, hv2, hv1]

omit [CharP F 2] in
private theorem exists_normalized (v : V) (hv : v ≠ 0) :
    ∃ (a : F), a ≠ 0 ∧ Normalized (a • v) := by
  by_cases h3 : v 3 = 0
  · by_cases h2 : v 2 = 0
    · by_cases h1 : v 1 = 0
      · have h0 : v 0 ≠ 0 := by
          intro h0
          apply hv
          ext i
          fin_cases i <;> simp_all
        refine ⟨(v 0)⁻¹, inv_ne_zero h0, ?_⟩
        simp [Normalized, h3, h2, h1, h0]
      · refine ⟨(v 1)⁻¹, inv_ne_zero h1, ?_⟩
        simp [Normalized, h3, h2, h1]
    · refine ⟨(v 2)⁻¹, inv_ne_zero h2, ?_⟩
      simp [Normalized, h3, h2]
  · refine ⟨(v 3)⁻¹, inv_ne_zero h3, ?_⟩
    simp [Normalized, h3]

private theorem chartLine_surjective : Function.Surjective (chartLine F σ hσ) := by
  intro W
  have hW : W.val ≠ ⊥ := by
    intro h
    have hd := W.property.1
    rw [h] at hd
    simp at hd
  obtain ⟨v,hvW,hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨a,ha,hn⟩ := exists_normalized F v hv
  have hi : pairing (form F σ hσ) (a • v) (a • v) = 0 := by
    simp only [pairing_smul_left, pairing_smul_right,
      W.property.2 hvW v hvW, mul_zero]
  obtain ⟨c,hc⟩ := normalized_is_chart F σ hσ hn hi
  refine ⟨c, Subtype.ext ?_⟩
  change Submodule.span F {chartVector F σ c} = W.val
  rw [hc, Submodule.span_singleton_smul_eq (isUnit_iff_ne_zero.mpr ha)]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one W.property.1 hvW hv).symm

private def chartsEquivLines : Charts F σ ≃ IsotropicLine (form F σ hσ) :=
  Equiv.ofBijective (chartLine F σ hσ)
    ⟨chartLine_injective F σ hσ, chartLine_surjective F σ hσ⟩

/-- The four normalized-coordinate charts count every isotropic line exactly once. -/
theorem isotropicLine_card [Finite F] : Nat.card (IsotropicLine (form F σ hσ)) =
    Nat.card F * Nat.card F * Nat.card (FixedBy.subfield F σ) +
      Nat.card F * Nat.card (FixedBy.subfield F σ) + Nat.card F + 1 := by
  let : Finite (RadicalCoordinates F σ) :=
    Finite.of_equiv (F × F × FixedBy.subfield F σ) (radicalParametersEquiv F σ hσ).symm
  rw [← Nat.card_congr (chartsEquivLines F σ hσ)]
  change Nat.card (RadicalCoordinates F σ ⊕ ((F × FixedBy.subfield F σ) ⊕ (F ⊕ Unit))) = _
  rw [Nat.card_sum, Nat.card_sum, Nat.card_sum,
    Nat.card_congr (radicalParametersEquiv F σ hσ), Nat.card_prod, Nat.card_prod]
  simp only [Nat.card_unique]
  ring

omit [CharP F 2] in
private theorem pointSpace_eq_span : pointSpace F = Submodule.span F {![1,0,0,0]} := by
  apply le_antisymm
  · intro x hx
    have hx' : x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 := hx
    apply Submodule.mem_span_singleton.mpr
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i <;> simp [hx'.1, hx'.2.1, hx'.2.2]
  · apply Submodule.span_le.mpr
    rintro x rfl
    change (![1,0,0,0] : V) 1 = 0 ∧ _
    simp

omit [CharP F 2] in
private theorem point_image_line (g : (form F σ hσ).specialSubgroup) :
    Module.finrank F ((pointSpace F).map (linearAction (form F σ hσ) g).toLinearMap) = 1 ∧
      (pointSpace F).map (linearAction (form F σ hσ) g).toLinearMap ≤
        orthogonal (form F σ hσ)
          ((pointSpace F).map (linearAction (form F σ hσ) g).toLinearMap) := by
  rw [pointSpace_eq_span, Submodule.map_span, Set.image_singleton]
  constructor
  · apply finrank_span_singleton
    exact (linearAction (form F σ hσ) g).map_ne_zero_iff.mpr (by
      intro h
      have h0 := congrFun h 0
      simp at h0)
  · apply span_isotropic F
    exact (pairing_action (form F σ hσ) g ![1,0,0,0] ![1,0,0,0]).trans
      (by simp [standard_pairing])

omit [CharP F 2] in
private theorem image_point_coe (J : HermitianForm 4 F) (g : J.specialSubgroup) :
    (((pointSpace F).map (linearAction J g).toLinearMap : Submodule F V) : Set V) =
      g • (pointSpace F : Set V) := by
  rw [Submodule.map_coe]
  rfl

private def linesEquivOrbit [Finite F]
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, σ x = x ^ (2 ^ n)) :
    IsotropicLine (form F σ hσ) ≃
      MulAction.orbit (form F σ hσ).specialSubgroup (pointSpace F : Set V) := by
  let f : IsotropicLine (form F σ hσ) →
      MulAction.orbit (form F σ hσ).specialSubgroup (pointSpace F : Set V) := fun W =>
    ⟨(W.val : Set V), by
      obtain ⟨A,hA,hWA⟩ := exists_point_unitary_transport σ hσ n hn hcard hconj
        W.val W.property.1 W.property.2
      obtain ⟨g,hg⟩ := exists_special_same_subspace_images (form F σ hσ) A hA
      refine MulAction.mem_orbit_iff.mpr ⟨g, ?_⟩
      rw [← image_point_coe]
      exact congrArg (fun U : Submodule F V => (U : Set V)) (hWA.trans (hg _)).symm⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro W X h
    apply Subtype.ext
    apply SetLike.coe_injective
    exact congrArg Subtype.val h
  · rintro ⟨W,hW⟩
    obtain ⟨g,rfl⟩ := MulAction.mem_orbit_iff.mp hW
    refine ⟨⟨(pointSpace F).map (linearAction (form F σ hσ) g).toLinearMap,
      point_image_line F σ hσ g⟩, ?_⟩
    apply Subtype.ext
    exact image_point_coe F (form F σ hσ) g

/-- The index is the number of actual isotropic lines, for the literal setwise
stabilizer of the first coordinate point. -/
theorem pointParabolic_index_eq_card [Finite F]
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, σ x = x ^ (2 ^ n)) :
    (pointParabolicSU F (form F σ hσ)).index = Nat.card (IsotropicLine (form F σ hσ)) := by
  have hp : pointParabolicSU F (form F σ hσ) =
      MulAction.stabilizer (form F σ hσ).specialSubgroup (pointSpace F : Set V) := rfl
  rw [hp, MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
  exact (Nat.card_congr (linesEquivOrbit F σ hσ n hn hcard hconj)).symm

variable {F}
omit [CharP F 2] in
/-- The literal isotropic-point parabolic of binary SU₄ has index
`(q³ + 1) (q² + 1)`, including `q = 2`. -/
theorem binary_point_index [Finite F] (J : HermitianForm 4 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    (pointParabolicSU F (UnitaryFourFormTransport.standardForm J)).index =
      ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 + 1) := by
  let : CharP F 2 := UnitaryFourFormTransport.charP_two n hn hcard
  have hf : Nat.card (FixedBy.subfield F J.conj) = 2 ^ n :=
    UnitaryFourFormTransport.fixed_card J n hn hcard hconj
  rw [pointParabolic_index_eq_card F J.conj J.conj_involutive n hn hcard hconj,
    isotropicLine_card, hcard, hf]
  ring

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointIndex
