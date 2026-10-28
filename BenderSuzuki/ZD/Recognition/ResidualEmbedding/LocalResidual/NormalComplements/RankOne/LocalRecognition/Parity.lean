module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.LocalRecognition.Basic
public import BenderSuzuki.SE.Section9Focal
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Abelianization.Defs

/-!
# Distinguished centralizer traces modulo four

The subgroup `M` acts by conjugation on the literal set `Z ∩ M`. Focal
transfer and ambient simplicity force the abelianization of `M` to have
odd order, so the sign of this action is trivial. An involution therefore
moves a multiple of four points. Its fixed points are exactly
`residualCentralizerTrace Z M v`, giving the same residue modulo four
for all involutions of `M`.

Source: GLS, Volume 4, Chapter 2, Corollary 7.14, final paragraph of the
proof (fusion from Proposition 4.2). This step needs no local model,
residual action, or residual generation premise.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII PFchapter1section1
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

private theorem odd_abelianization
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M) :
    Odd (Nat.card (Abelianization M)) := by
  apply Nat.not_even_iff_odd.mp
  rw [even_iff_two_dvd]
  change ¬ 2 ∣ Nat.card (M ⧸ commutator M)
  intro heven
  obtain ⟨S, hSM, hfusion⟩ := r.fusion
  obtain ⟨hlt, hsup⟩ :=
    hallPResidual_factorization_of_dvd_abelianization_of_controlsFusionIn
      M S hSM hfusion (by simpa only [derivedSubgroup, derivedSeries_one] using heven)
  rcases r.simple.eq_bot_or_eq_top_of_normal (External.hallPResidual 2 G)
      (External.hallPResidual_normal 2 G) with hbot | htop
  · exact h.proper (by simpa [hbot] using hsup)
  · exact hlt.ne htop

private theorem character_eq_one
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (f : M →* ℤˣ) (x : M) : f x = 1 := by
  rcases Int.units_eq_one_or (f x) with hx | hx
  · exact hx
  · have hp := congrArg (Abelianization.lift f)
      (pow_card_eq_one' (x := Abelianization.of x))
    rw [map_pow, map_one, Abelianization.lift_apply_of, hx,
      (odd_abelianization h r).neg_one_pow] at hp
    simp at hp

omit [Finite G] in
/-- The actual conjugation action of `M` on `Z ∩ M`, represented as a
homomorphism to its permutation group. Only `M` acts on this subset. -/
public def distinguishedTraceConjugation (h : IsProductDisconnected Z M) :
    M →* Equiv.Perm {z : G // z ∈ Z ∧ z ∈ M} where
  toFun m :=
    { toFun := fun z => ⟨MulAut.conj (m : G) z,
        h.invariant m z z.property.1,
        M.mul_mem (M.mul_mem m.property z.property.2) (M.inv_mem m.property)⟩
      invFun := fun z => ⟨MulAut.conj (m : G)⁻¹ z,
        h.invariant (m : G)⁻¹ z z.property.1,
        by simpa only [MulAut.conj_apply, inv_inv] using
          M.mul_mem (M.mul_mem (M.inv_mem m.property) z.property.2) m.property⟩
      left_inv := by intro z; apply Subtype.ext; simp [MulAut.conj_apply, mul_assoc]
      right_inv := by intro z; apply Subtype.ext; simp [MulAut.conj_apply, mul_assoc] }
  map_one' := by ext z; simp
  map_mul' := by intro m n; ext z; simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
/-- The action uses the ambient conjugation convention `m * z * m⁻¹`. -/
public theorem distinguishedTraceConjugation_apply
    (h : IsProductDisconnected Z M) (m : M) (z : {z : G // z ∈ Z ∧ z ∈ M}) :
    (distinguishedTraceConjugation h m z : G) = (m : G) * z * (m : G)⁻¹ := by rfl

omit [Finite G] in
/-- Conjugation fixes a distinguished point precisely when it commutes
with the acting element. -/
public theorem distinguishedTraceConjugation_fixed_iff (h : IsProductDisconnected Z M)
    (m : M) (z : {z : G // z ∈ Z ∧ z ∈ M}) :
    distinguishedTraceConjugation h m z = z ↔ Commute (z : G) (m : G) := by
  rw [Subtype.ext_iff]
  change (m : G) * z * (m : G)⁻¹ = z ↔ _
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

omit [Finite G] in
/-- The fixed-point subtype is the literal ambient centralizer trace. -/
public def distinguishedTraceConjugationFixedEquiv (h : IsProductDisconnected Z M) (m : M) :
    Function.fixedPoints (distinguishedTraceConjugation h m) ≃
      residualCentralizerTrace Z M m where
  toFun z := ⟨z.val.val, z.val.property.1, z.val.property.2,
    (distinguishedTraceConjugation_fixed_iff h m z.val).mp z.property⟩
  invFun z := ⟨⟨z.val, z.property.1, z.property.2.1⟩,
    (distinguishedTraceConjugation_fixed_iff h m _).mpr z.property.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fixedPoints_modEq_four {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (σ : Equiv.Perm Ω) (hσ : σ ^ 2 = 1) (hs : Equiv.Perm.sign σ = 1) :
    Nat.ModEq 4 (Fintype.card (Function.fixedPoints σ)) (Fintype.card Ω) := by
  have hs' := Equiv.Perm.sign_of_pow_two_eq_one hσ
  rw [hs, Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType,
    Nat.sub_sub_self (Finset.card_le_univ _)] at hs'
  have he : Even (σ.support.card / 2) :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hs'.symm
  have hdiv := Equiv.Perm.two_dvd_card_support hσ
  have hfour : 4 ∣ σ.support.card := by
    obtain ⟨k, hk⟩ := even_iff_two_dvd.mp he
    refine ⟨k, ?_⟩
    have hmul := Nat.div_mul_cancel hdiv
    omega
  rw [Equiv.Perm.card_fixedPoints, Equiv.Perm.sum_cycleType]
  apply (Nat.modEq_iff_dvd' (Nat.sub_le _ _)).mpr
  rwa [Nat.sub_sub_self (Finset.card_le_univ _)]

/-- Each involution fixes as many distinguished points modulo four as
there are points in `Z ∩ M`. The sign premise is proved by focal transfer. -/
public theorem residualCentralizerTrace_ncard_modEq_card
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v : G} (hv : IsInvolution v) (hvM : v ∈ M) :
    Nat.ModEq 4 (residualCentralizerTrace Z M v).ncard
      (Z ∩ (M : Set G)).ncard := by
  classical
  let Ω := {z : G // z ∈ Z ∧ z ∈ M}
  let : Fintype Ω := Fintype.ofFinite Ω
  let vM : M := ⟨v, hvM⟩
  let a := distinguishedTraceConjugation h
  have hsq : a vM ^ 2 = 1 := by
    rw [← map_pow, show vM ^ 2 = 1 from Subtype.ext hv.sq_eq_one, map_one]
  have hs : Equiv.Perm.sign (a vM) = 1 :=
    character_eq_one h r (Equiv.Perm.sign.comp a) vM
  have hmod := fixedPoints_modEq_four (a vM) hsq hs
  have hcard : Fintype.card (Function.fixedPoints (a vM)) =
      (residualCentralizerTrace Z M v).ncard := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (distinguishedTraceConjugationFixedEquiv h vM)
  rw [hcard] at hmod
  have hΩ : Fintype.card Ω = (Z ∩ (M : Set G)).ncard := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_coe_set_eq _
  rwa [hΩ] at hmod

/-- The permutation-sign implication used in GLS4 Corollary 7.14:
any two involutions of `M` have congruent distinguished traces modulo four. -/
public theorem residualCentralizerTrace_ncard_modEq_four
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    {v₁ v₂ : G} (hv₁ : IsInvolution v₁) (hv₁M : v₁ ∈ M)
    (hv₂ : IsInvolution v₂) (hv₂M : v₂ ∈ M) :
    Nat.ModEq 4 (residualCentralizerTrace Z M v₁).ncard
      (residualCentralizerTrace Z M v₂).ncard :=
  (residualCentralizerTrace_ncard_modEq_card h r hv₁ hv₁M).trans
    (residualCentralizerTrace_ncard_modEq_card h r hv₂ hv₂M).symm

end BenderSuzuki.ZD
