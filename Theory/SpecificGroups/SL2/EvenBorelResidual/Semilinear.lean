module

public import Theory.SpecificGroups.SL2.EvenBorelResidual.FieldInvolution
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.SylowKernelCore

/-!
# Semilinear actors on the actual even PSL₂ Borel quotient

The projection of the upper triangular Borel onto its diagonal complement
identifies its unipotent quotient with the field's unit group. A field actor
preserves both factors. An inner twist stabilizing the upper root group has
its inner factor in the Borel, and that factor vanishes under the projection.
Thus the induced torus action of every aligned semilinear actor is its actual
coefficient action, without a hypothesis on the actor's order.

Fixation of O³(B)O₂(B)/O₂(B) is expressed by ambient displacements modulo
the embedded two-core. It is equivalent to fixation of O³(Fˣ). Power
relations descend to the field part; an inner actor of two-power order lies
in the inner image of the unipotent radical. Sylow conjugacy aligns an
arbitrary specified Sylow, and both residuals and fixation transport through
that genuine inner equivalence. Only universal semilinear automorphism
coverage is left explicit in the alignment theorem.

Source: Aschbacher–Smith, proof of 13.8.20, printed p.954 (PDF p.971).
This module uses the existing licensed coefficient transport on SL₂/Z(SL₂).
The finite-field exceptional-degree argument and the cyclic-action
commutator quotient bound are separate from these alignment identities.
-/

@[expose] public section

open scoped MatrixGroups
open Subgroup BenderSuzuki.Converse Atlas
namespace Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
open OddBorel FieldInvolution
variable (F : Type*) [Field F]

theorem field_unipotent (σ : F ≃+* F) (t : F) :
    fieldEquivPSL 2 σ (unipotentHom F (Multiplicative.ofAdd t)) =
      unipotentHom F (Multiplicative.ofAdd (σ t)) := by
  change fieldEquivPSL 2 σ (QuotientGroup.mk' _ (uni t)) = QuotientGroup.mk' _ _
  rw [fieldEquivPSL_mk]
  apply congrArg (QuotientGroup.mk' _)
  apply Subtype.ext
  ext i j
  change σ ((uni t).val i j) = (uni (σ t)).val i j
  fin_cases i <;> fin_cases j <;> simp [uni]

theorem field_map_kernel (σ : F ≃+* F) :
    (kernel F).map (fieldEquivPSL 2 σ).toMonoidHom = kernel F := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨Multiplicative.ofAdd (σ t.toAdd), (field_unipotent F σ t.toAdd).symm⟩
  · rintro _ ⟨t, rfl⟩
    refine ⟨unipotentHom F (Multiplicative.ofAdd (σ.symm t.toAdd)), ⟨_, rfl⟩, ?_⟩
    change fieldEquivPSL 2 σ (unipotentHom F (Multiplicative.ofAdd (σ.symm t.toAdd))) = _
    rw [field_unipotent, σ.apply_symm_apply]
    rfl

theorem field_map_complement (σ : F ≃+* F) :
    (complement F).map (fieldEquivPSL 2 σ).toMonoidHom = complement F := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
    exact ⟨Units.map σ.toMonoidHom u, (field_torusHom F σ u).symm⟩
  · rintro _ ⟨u, rfl⟩
    refine ⟨torusHom F (Units.map σ.symm.toMonoidHom u), ⟨_, rfl⟩, ?_⟩
    change fieldEquivPSL 2 σ (torusHom F (Units.map σ.symm.toMonoidHom u)) = _
    rw [field_torusHom]
    congr 1
    apply Units.ext
    exact σ.apply_symm_apply u

theorem field_map_borel (σ : F ≃+* F) :
    (borel F).map (fieldEquivPSL 2 σ).toMonoidHom = borel F := by
  rw [borel, Subgroup.map_sup, field_map_kernel, field_map_complement]

variable [CharP F 2]

theorem inner_factor_mem_borel (g : PSL(2,F)) (σ : F ≃+* F)
    (h : (kernel F).map (MulAut.conj g * fieldEquivPSL 2 σ).toMonoidHom = kernel F) :
    g ∈ borel F := by
  rw [← normalizer_kernel]
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : (MulAut.conj g * fieldEquivPSL 2 σ).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (fieldEquivPSL 2 σ).toMonoidHom := rfl
  rw [he, ← Subgroup.map_map, field_map_kernel] at h
  exact h

noncomputable def unipotentQuotientEquiv :
    borel F ⧸ (kernel F).subgroupOf (borel F) ≃* Fˣ :=
  (kernel_isComplement F).symm.QuotientMulEquiv.trans
    ((subgroupOfEquivOfLe (show complement F ≤ borel F from le_sup_right)).trans
      (torusEquiv F).symm)

noncomputable def torusProjection : borel F →* Fˣ :=
  (unipotentQuotientEquiv F).toMonoidHom.comp
    (QuotientGroup.mk' ((kernel F).subgroupOf (borel F)))

theorem torusProjection_surjective : Function.Surjective (torusProjection F) :=
  (((kernel_isComplement F).symm.QuotientMulEquiv.trans
    ((subgroupOfEquivOfLe (show complement F ≤ borel F from le_sup_right)).trans
      (torusEquiv F).symm)).surjective).comp (QuotientGroup.mk'_surjective _)

theorem torusProjection_eq_one_iff (x : borel F) :
    torusProjection F x = 1 ↔ (x : PSL(2,F)) ∈ kernel F := by
  change unipotentQuotientEquiv F (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [map_eq_one_iff _ (unipotentQuotientEquiv F).injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]
  rfl

theorem torusProjection_torus (u : Fˣ) :
    torusProjection F ⟨torusHom F u, (show complement F ≤ borel F from le_sup_right) ⟨u, rfl⟩⟩ = u := by
  let c : (complement F).subgroupOf (borel F) :=
    ⟨⟨torusHom F u, (show complement F ≤ borel F from le_sup_right) ⟨u, rfl⟩⟩, ⟨u, rfl⟩⟩
  change (torusEquiv F).symm
    (subgroupOfEquivOfLe (show complement F ≤ borel F from le_sup_right)
      ((kernel_isComplement F).symm.QuotientMulEquiv
        (QuotientGroup.mk' _ (c : borel F)))) = u
  rw [quotientMulEquiv_mk_apply_of_isComplement']
  exact (torusEquiv F).symm_apply_apply u

noncomputable def fieldBorel (σ : F ≃+* F) : MulAut (borel F) :=
  ((fieldEquivPSL 2 σ).subgroupMap (borel F)).trans
    (MulEquiv.subgroupCongr (field_map_borel F σ))

theorem torusProjection_field (σ : F ≃+* F) (x : borel F) :
    torusProjection F (fieldBorel F σ x) =
      Units.map σ.toMonoidHom (torusProjection F x) := by
  obtain ⟨⟨k, c⟩, he⟩ := (kernel_isComplement F).2 x
  change (k : borel F) * c = x at he
  rw [← he, map_mul, map_mul, map_mul, map_mul]
  have hk : torusProjection F (k : borel F) = 1 :=
    (torusProjection_eq_one_iff F _).mpr k.property
  have hfk : torusProjection F (fieldBorel F σ (k : borel F)) = 1 := by
    apply (torusProjection_eq_one_iff F _).mpr
    have hkK : (k : borel F).val ∈ kernel F := k.property
    have hh := mem_map_of_mem (fieldEquivPSL 2 σ).toMonoidHom hkK
    change fieldEquivPSL 2 σ (k : borel F).val ∈ kernel F
    simpa only [field_map_kernel, MulEquiv.coe_toMonoidHom] using hh
  obtain ⟨u, hu⟩ := c.property
  have hc : (c : borel F) = ⟨torusHom F u, (show complement F ≤ borel F from le_sup_right) ⟨u, rfl⟩⟩ := Subtype.ext hu.symm
  rw [hk, hfk, map_one, one_mul, one_mul, hc, torusProjection_torus]
  have hf : fieldBorel F σ ⟨torusHom F u, (show complement F ≤ borel F from le_sup_right) ⟨u, rfl⟩⟩ =
      ⟨torusHom F (Units.map σ.toMonoidHom u), (show complement F ≤ borel F from le_sup_right) ⟨_, rfl⟩⟩ :=
    Subtype.ext (field_torusHom F σ u)
  rw [hf, torusProjection_torus]

noncomputable def borelActor (g : borel F) (σ : F ≃+* F) : MulAut (borel F) :=
  MulAut.conj g * fieldBorel F σ

theorem torusProjection_borelActor (g : borel F) (σ : F ≃+* F) (x : borel F) :
    torusProjection F (borelActor F g σ x) =
      Units.map σ.toMonoidHom (torusProjection F x) := by
  change torusProjection F (g * fieldBorel F σ x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, mul_comm (torusProjection F g), mul_assoc,
    mul_inv_cancel, mul_one, torusProjection_field]

/-- Pointwise fixation of the three-residual torus, expressed in the ambient group. -/
def FixesResidualTorus {G : Type*} [Group G] (B : Subgroup G) (a : MulAut G) : Prop :=
  ∀ x ∈ (pResidual 3 B).map B.subtype ⊔ B.pCoreIn 2,
    x⁻¹ * a x ∈ B.pCoreIn 2

variable [Finite F]

theorem twoCoreIn_eq_kernel {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    (borel F).pCoreIn 2 = kernel F := by
  rw [pCoreIn, twoCore_eq_kernel F hF, map_subgroupOf_eq_of_le
    (show kernel F ≤ borel F from le_sup_left)]

theorem borelActor_commutator_mem_core_iff {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (g : borel F) (σ : F ≃+* F) (x : borel F) :
    (x : PSL(2,F))⁻¹ * (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) x ∈
        (borel F).pCoreIn 2 ↔
      Units.map σ.toMonoidHom (torusProjection F x) = torusProjection F x := by
  rw [twoCoreIn_eq_kernel F hF]
  change ((x⁻¹ * borelActor F g σ x : borel F) : PSL(2,F)) ∈ kernel F ↔ _
  rw [← torusProjection_eq_one_iff, map_mul, map_inv, torusProjection_borelActor,
    inv_mul_eq_one]
  exact eq_comm

theorem fixesResidualTorus_iff {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (g : borel F) (σ : F ≃+* F) :
    FixesResidualTorus (borel F) (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) ↔
      ∀ u ∈ pResidual 3 Fˣ, Units.map σ.toMonoidHom u = u := by
  have hres := map_pResidual_of_surjective 3 (torusProjection F)
    (torusProjection_surjective F)
  constructor
  · intro h u hu
    rw [← hres] at hu
    obtain ⟨x, hx, rfl⟩ := hu
    apply (borelActor_commutator_mem_core_iff F hF g σ x).mp
    exact h x (mem_sup_left (mem_map_of_mem _ hx))
  · intro h
    let D := ((FiniteField.BinaryTorusInvolution.displacement σ).comp
      (torusProjection F)).ker
    have hR : pResidual 3 (borel F) ≤ D := by
      intro x hx
      have hu : torusProjection F x ∈ pResidual 3 Fˣ := by
        rw [← hres]
        exact mem_map_of_mem _ hx
      change Units.map σ.toMonoidHom (torusProjection F x) *
        (torusProjection F x)⁻¹ = 1
      rw [h _ hu, mul_inv_cancel]
    have hU : pCore 2 (borel F) ≤ D := by
      intro x hx
      have hxK : (x : PSL(2,F)) ∈ kernel F := by
        rwa [twoCore_eq_kernel F hF] at hx
      have hp := (torusProjection_eq_one_iff F x).mpr hxK
      change FiniteField.BinaryTorusInvolution.displacement σ (torusProjection F x) = 1
      rw [hp, map_one]
    intro x hx
    have hle : (pResidual 3 (borel F)).map (borel F).subtype ⊔ (borel F).pCoreIn 2 ≤
        D.map (borel F).subtype := by
      exact sup_le (map_mono hR) (map_mono hU)
    obtain ⟨y, hy, rfl⟩ := hle hx
    apply (borelActor_commutator_mem_core_iff F hF g σ y).mpr
    change Units.map σ.toMonoidHom (torusProjection F y) * (torusProjection F y)⁻¹ = 1 at hy
    exact mul_inv_eq_one.mp hy

/-- Sylow conjugacy aligns both the Borel and the entire semilinear actor. -/
theorem aligned_semilinear_of_coverage (S : Sylow 2 PSL(2,F)) (a : MulAut PSL(2,F))
    (ha : (S : Subgroup PSL(2,F)).map a.toMonoidHom = S)
    (hcoverage : ∀ β : MulAut PSL(2,F),
      ∃ (g : PSL(2,F)) (σ : F ≃+* F), β = MulAut.conj g * fieldEquivPSL 2 σ) :
    ∃ (c : PSL(2,F)) (g : borel F) (σ : F ≃+* F),
      (kernel F).map (MulAut.conj c).toMonoidHom = S ∧
      (borel F).map (MulAut.conj c).toMonoidHom = normalizer (S : Set PSL(2,F)) ∧
      MulAut.congr (MulAut.conj c).symm a =
        MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ := by
  obtain ⟨c, hcU, hcB⟩ := sylow_normalizer_conjugate F S
  let e := MulAut.conj c
  let b := MulAut.congr e.symm a
  have hb : (kernel F).map b.toMonoidHom = kernel F := by
    calc
      _ = (((kernel F).map e.toMonoidHom).map a.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map, Subgroup.map_map]
        rfl
      _ = (S : Subgroup PSL(2,F)).map e.symm.toMonoidHom := by rw [hcU, ha]
      _ = kernel F := (map_symm_eq_iff_map_eq (kernel F) (e := e)).mpr hcU
  obtain ⟨g, σ, he⟩ := hcoverage b
  have hg : g ∈ borel F := inner_factor_mem_borel F g σ (he ▸ hb)
  exact ⟨c, ⟨g, hg⟩, σ, hcU, hcB, he⟩


omit [CharP F 2] [Finite F] in
theorem borelActor_apply_coe (g : borel F) (σ : F ≃+* F) (x : borel F) :
    (borelActor F g σ x : PSL(2,F)) =
      (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) x := rfl

omit [CharP F 2] [Finite F] in
theorem borelActor_pow_apply_coe (g : borel F) (σ : F ≃+* F) (k : ℕ) (x : borel F) :
    ((borelActor F g σ ^ k) x : PSL(2,F)) =
      ((MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) ^ k) x := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (ih (borelActor F g σ x)).trans (congrArg
      ((MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) ^ k)
        (borelActor_apply_coe F g σ x))

omit [Finite F] in
theorem torusProjection_borelActor_pow (g : borel F) (σ : F ≃+* F) (k : ℕ)
    (x : borel F) :
    torusProjection F ((borelActor F g σ ^ k) x) =
      Units.map (σ ^ k).toMonoidHom (torusProjection F x) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ, pow_succ]
    change torusProjection F ((borelActor F g σ ^ k) (borelActor F g σ x)) = _
    rw [ih, torusProjection_borelActor]
    rfl

omit [Finite F] in
/-- A power relation on the actual actor forces the same relation on its field part. -/
theorem field_pow_eq_one_of_actor_pow (g : borel F) (σ : F ≃+* F) (k : ℕ)
    (h : (MulAut.conj (g : PSL(2,F)) * fieldEquivPSL 2 σ) ^ k = 1) : σ ^ k = 1 := by
  have hb : borelActor F g σ ^ k = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [borelActor_pow_apply_coe, h]
    rfl
  have hu (u : Fˣ) : Units.map (σ ^ k).toMonoidHom u = u := by
    obtain ⟨x, rfl⟩ := torusProjection_surjective F u
    rw [← torusProjection_borelActor_pow, hb]
    rfl
  ext x
  by_cases hx : x = 0
  · subst x; exact map_zero _
  · exact congrArg Units.val (hu (Units.mk0 x hx))


omit [Finite F] in
/-- Innerness is detected by the actual field factor, even for an inner twist. -/
theorem semilinear_inner_iff (g : PSL(2,F)) (σ : F ≃+* F) :
    (∃ d : PSL(2,F), MulAut.conj g * fieldEquivPSL 2 σ = MulAut.conj d) ↔ σ = 1 := by
  constructor
  · rintro ⟨d, hd⟩
    apply RankOneFieldAutomorphisms.field_eq_one_of_PSL_inner σ (g⁻¹ * d)
    rw [map_mul, map_inv, ← hd]
    group
  · intro hσ
    refine ⟨g, ?_⟩
    change MulAut.conj g * RankOneFieldAutomorphisms.pslFieldAction σ = MulAut.conj g
    rw [hσ, map_one, mul_one]

/-- Two-power inner actors in a Borel come from its unipotent radical. -/
theorem inner_mem_kernel_of_pow {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (g : borel F) (k : ℕ) (hg : MulAut.conj (g : PSL(2,F)) ^ (2 ^ k) = 1) :
    (g : PSL(2,F)) ∈ kernel F := by
  have hc : (g : PSL(2,F)) ^ (2 ^ k) ∈ center PSL(2,F) := by
    rw [mem_center_iff]
    intro x
    have hh : MulAut.conj ((g : PSL(2,F)) ^ (2 ^ k)) = 1 := by rw [map_pow]; exact hg
    have hx := MulEquiv.congr_fun hh x
    change (g : PSL(2,F)) ^ (2 ^ k) * x * ((g : PSL(2,F)) ^ (2 ^ k))⁻¹ = x at hx
    exact (mul_inv_eq_iff_eq_mul.mp hx).symm
  have hgp : g ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    change (g : PSL(2,F)) ^ (2 ^ k) = 1
    simpa only [RankOneFieldAutomorphisms.psl_center_eq_bot, mem_bot] using hc
  have hu : torusProjection F g ^ (2 ^ k) = 1 := by rw [← map_pow, hgp, map_one]
  have hn : n ≠ 0 := by
    intro hn
    have hlarge : 1 < Nat.card F := Finite.one_lt_card
    simp [hF, hn] at hlarge
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units, hF]
    exact Nat.Even.sub_odd (Nat.one_le_pow n 2 (by decide))
      (Even.pow_of_ne_zero even_two hn) odd_one
  apply (torusProjection_eq_one_iff F g).mp
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left k)
  · exact orderOf_dvd_of_pow_eq_one hu
  · exact orderOf_dvd_natCard _


omit [Finite F] [CharP F 2] in
/-- The commutator definition of fixation is invariant under a genuine group equivalence. -/
theorem fixesResidualTorus_map_iff {G H : Type*} [Group G] [Group H] [Finite G]
    (e : G ≃* H) (B : Subgroup G) (a : MulAut G) :
    FixesResidualTorus (B.map e.toMonoidHom) (MulAut.congr e a) ↔
      FixesResidualTorus B a := by
  have hC := map_pCoreIn_of_injective 2 B e.toMonoidHom e.injective
  have hR : ((pResidual 3 B).map B.subtype ⊔ B.pCoreIn 2).map e.toMonoidHom =
      (pResidual 3 (B.map e.toMonoidHom)).map (B.map e.toMonoidHom).subtype ⊔
        (B.map e.toMonoidHom).pCoreIn 2 := by
    rw [Subgroup.map_sup, map_embedded_pResidual, hC]
  have he (x : G) : (e x)⁻¹ * MulAut.congr e a (e x) = e (x⁻¹ * a x) := by
    simp [MulAut.congr]
  constructor
  · intro h x hx
    have hm : e x ∈ (pResidual 3 (B.map e.toMonoidHom)).map
        (B.map e.toMonoidHom).subtype ⊔ (B.map e.toMonoidHom).pCoreIn 2 := by
      rw [← hR]
      exact mem_map_of_mem _ hx
    have hh := h (e x) hm
    rw [he, ← hC] at hh
    exact (mem_map_iff_mem e.injective).mp hh
  · intro h y hy
    rw [← hR] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    change (e x)⁻¹ * MulAut.congr e a (e x) ∈ _
    rw [he, ← hC]
    exact mem_map_of_mem _ (h x hx)

/-- The source Borel at every specified Sylow has that Sylow as its embedded two-core. -/
theorem sylowNormalizer_twoCoreIn {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(2,F)) :
    (normalizer (S : Set PSL(2,F))).pCoreIn 2 = (S : Subgroup PSL(2,F)) := by
  obtain ⟨g, hgU, hgB⟩ := sylow_normalizer_conjugate F S
  rw [← hgB, ← map_pCoreIn_of_injective 2 (borel F) (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective, twoCoreIn_eq_kernel F hF, hgU]

/-- The source two-residual is the whole Borel when the binary degree exceeds one. -/
theorem sylowNormalizer_twoResidual {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (S : Sylow 2 PSL(2,F)) :
    pResidual 2 (normalizer (S : Set PSL(2,F))) = ⊤ := by
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ n by omega)
  apply (pResidual_eq_top_iff 2 _).mpr
  exact (borel_isPPerfect F hq).of_surjective (sylowNormalizerEquiv F S).symm.toMonoidHom
    (sylowNormalizerEquiv F S).symm.surjective

end Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.Semilinear
