module
public import Theory.Representation.SL2FourNaturalOrbits.BorelFactors
public import Theory.Representation.RepEquiv
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.Module.ZMod
public import Theory.GroupTheory.NoncentralChiefRefinement.Homogeneous

/-!
# Dual flags and core conjugation for the four-element-field Borel

Annihilators of invariant subspaces retain the literal contragredient action.
Quotient duality and restriction of functionals give equivariant comparisons,
so finite-dimensional irreducibility and noncentrality pass to both dual factors.
The upper root group has actual additive-field coordinates; conjugation by an
upper triangular matrix acts by its squared diagonal entry. Torus transitivity
makes this binary plane irreducible and noncentral. One-copy coordinates use
the literal relative quotient and feed the chief-refinement interface.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
14.7.70, printed p.1074 (PDF p.1091). These are model and duality calculations;
source compatibility and five-factor assembly are separate obligations.
-/

@[expose] public section
noncomputable section
namespace Representation.SL2FourNatural.BorelDualCore
section Dual
variable {k K M : Type*} [Field k] [Group K] [AddCommGroup M] [Module k M]
  (ρ : Representation k K M)

/-- The annihilator of an invariant subspace for the literal contragredient action. -/
def annihilator (U : Subrepresentation ρ) : Subrepresentation ρ.dual where
  toSubmodule := U.toSubmodule.dualAnnihilator
  apply_mem_toSubmodule g f hf := by
    apply (U.toSubmodule.mem_dualAnnihilator _).mpr
    intro v hv
    exact (U.toSubmodule.mem_dualAnnihilator f).mp hf _ (U.apply_mem_toSubmodule g⁻¹ hv)

/-- Quotient duality uses the original quotient map. -/
def annihilatorEquiv (U : Subrepresentation ρ) :
    Representation.RepEquiv (annihilator ρ U).toRepresentation U.quotientRepresentation.dual where
  toLinearEquiv := U.toSubmodule.dualQuotEquivDualAnnihilator.symm
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H x => rfl

/-- Restriction of functionals identifies the dual quotient with the dual of the line. -/
def annihilatorQuotientEquiv (U : Subrepresentation ρ) :
    Representation.RepEquiv (annihilator ρ U).quotientRepresentation U.toRepresentation.dual where
  toLinearEquiv := Subspace.quotAnnihilatorEquiv U.toSubmodule
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    induction f using Submodule.Quotient.induction_on with
    | H f =>
      apply LinearMap.ext
      intro v
      rfl

/-- Finite-dimensional contragredients preserve irreducibility. -/
theorem dual_irreducible [FiniteDimensional k M] [IsIrreducible ρ] :
    IsIrreducible ρ.dual := by
  let : Nontrivial M := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun S => ?_⟩
  let C : Subrepresentation ρ := {
    toSubmodule := S.toSubmodule.dualCoannihilator
    apply_mem_toSubmodule g v hv := by
      apply (Submodule.mem_dualCoannihilator _).mpr
      intro f hf
      have he := (Submodule.mem_dualCoannihilator v).mp hv
        (ρ.dual g⁻¹ f) (S.apply_mem_toSubmodule g⁻¹ hf)
      change f (ρ (g⁻¹)⁻¹ v) = 0 at he
      simpa only [inv_inv] using he }
  have hd := Subspace.dualCoannihilator_dualAnnihilator_eq (W := S.toSubmodule)
  rcases eq_bot_or_eq_top C with hC | hC
  · right
    apply Subrepresentation.toSubmodule_injective
    have he : S.toSubmodule.dualCoannihilator = ⊥ := congrArg Subrepresentation.toSubmodule hC
    rw [he, Submodule.dualAnnihilator_bot] at hd
    exact hd.symm
  · left
    apply Subrepresentation.toSubmodule_injective
    have he : S.toSubmodule.dualCoannihilator = ⊤ := congrArg Subrepresentation.toSubmodule hC
    rw [he, Submodule.dualAnnihilator_top] at hd
    exact hd.symm

/-- A moved vector is detected by an actual functional in the dual. -/
theorem dual_noncentral (h : ∃ g v, ρ g v ≠ v) : ∃ g f, ρ.dual g f ≠ f := by
  obtain ⟨g, v, hv⟩ := h
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero k (sub_ne_zero.mpr hv)
  refine ⟨g⁻¹, f, ?_⟩
  intro he
  have he' := LinearMap.congr_fun he v
  change f (ρ (g⁻¹)⁻¹ v) = f v at he'
  rw [inv_inv] at he'
  exact hf (by rw [map_sub, he', sub_self])

set_option backward.isDefEq.respectTransparency false in
theorem annihilator_irreducible (U : Subrepresentation ρ)
    [FiniteDimensional k (M ⧸ U.toSubmodule)] [IsIrreducible U.quotientRepresentation] :
    IsIrreducible (k := k) (G := K) (V := (annihilator ρ U).toSubmodule)
      (annihilator ρ U).toRepresentation :=
  (annihilatorEquiv ρ U).irreducible_of_euqiv (dual_irreducible U.quotientRepresentation)

theorem annihilatorQuotient_irreducible (U : Subrepresentation ρ)
    [FiniteDimensional k U.toSubmodule] [IsIrreducible U.toRepresentation] :
    IsIrreducible (annihilator ρ U).quotientRepresentation :=
  (annihilatorQuotientEquiv ρ U).irreducible_of_euqiv (dual_irreducible U.toRepresentation)

private theorem noncentral_of_equiv {N : Type*} [AddCommGroup N] [Module k N]
    {σ : Representation k K N} (e : Representation.RepEquiv ρ σ)
    (h : ∃ g v, σ g v ≠ v) : ∃ g v, ρ g v ≠ v := by
  obtain ⟨g, v, hv⟩ := h
  refine ⟨g, e.symm v, ?_⟩
  intro he
  have he' := congrArg e he
  rw [e.isIntertwining, e.apply_symm_apply] at he'
  exact hv he'

set_option backward.isDefEq.respectTransparency false in
theorem annihilator_noncentral (U : Subrepresentation ρ)
    (h : ∃ g v, U.quotientRepresentation g v ≠ v) :
    ∃ g f, (annihilator ρ U).toRepresentation g f ≠ f :=
  noncentral_of_equiv (k := k) (K := K) (M := (annihilator ρ U).toSubmodule)
    (annihilator ρ U).toRepresentation (annihilatorEquiv ρ U) (dual_noncentral _ h)

theorem annihilatorQuotient_noncentral (U : Subrepresentation ρ)
    (h : ∃ g v, U.toRepresentation g v ≠ v) :
    ∃ g f, (annihilator ρ U).quotientRepresentation g f ≠ f :=
  noncentral_of_equiv _ (annihilatorQuotientEquiv ρ U) (dual_noncentral _ h)

end Dual
end Representation.SL2FourNatural.BorelDualCore

namespace Representation.SL2FourNatural.BorelDualCore
open Subgroup Matrix.SpecialLinearGroup BorelFactors

/-- Additive-field coordinates on the literal upper root group. -/
def upperCoordinates : U0 ≃* Multiplicative F :=
  (MonoidHom.ofInjective (upperUnipotentHom_injective F)).symm

theorem upperCoordinates_symm (b : F) :
    (upperCoordinates.symm (Multiplicative.ofAdd b)).val = upper b :=
  (upper_eq_transvection b).symm

section Transport
variable {G : Type*} [Group G] (U : Subgroup G)
    (e : U ≃* Multiplicative F)

/-- Conjugation transported through actual additive-field coordinates. -/
def coordinateAction : Representation (ZMod 2) (Subgroup.normalizer (U : Set G)) F where
  toFun g := AddMonoidHom.toZModLinearMap 2 {
    toFun b := (e (U.normalizerMonoidHom g (e.symm (Multiplicative.ofAdd b)))).toAdd
    map_zero' := by simp
    map_add' b c := by
      change (e (U.normalizerMonoidHom g (e.symm
        (Multiplicative.ofAdd b * Multiplicative.ofAdd c)))).toAdd = _
      simp only [map_mul]
      rfl }
  map_one' := by
    apply LinearMap.ext
    intro b
    change (e (U.normalizerMonoidHom 1 (e.symm (Multiplicative.ofAdd b)))).toAdd = b
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro b
    change (e (U.normalizerMonoidHom (g * h) (e.symm (Multiplicative.ofAdd b)))).toAdd =
      (e (U.normalizerMonoidHom g (e.symm (e
        (U.normalizerMonoidHom h (e.symm (Multiplicative.ofAdd b))))))).toAdd
    rw [e.symm_apply_apply, map_mul]
    rfl

/-- Coordinates intertwine literal ambient conjugation. -/
theorem coordinateAction_equivariant (g : Subgroup.normalizer (U : Set G)) (u : U) :
    (e (U.normalizerMonoidHom g u)).toAdd = coordinateAction U e g (e u).toAdd := by
  change _ = (e (U.normalizerMonoidHom g (e.symm (e u)))).toAdd
  rw [e.symm_apply_apply]
end Transport

/-- The Borel's core action is conjugation, not the natural-line action. -/
abbrev coreAction : Representation (ZMod 2) B0 F := coordinateAction U0 upperCoordinates

theorem coreAction_apply (g : B0) (b : F) : coreAction g b = g.val.val 0 0 ^ 2 * b := by
  apply Multiplicative.ofAdd.injective
  apply upperCoordinates.symm.injective
  apply Subtype.ext
  change (upperCoordinates.symm (upperCoordinates
    (U0.normalizerMonoidHom g (upperCoordinates.symm (Multiplicative.ofAdd b))))).val = _
  rw [upperCoordinates.symm_apply_apply]
  change g.val * (upperCoordinates.symm (Multiplicative.ofAdd b)).val * g.val⁻¹ = _
  rw [upperCoordinates_symm, upperCoordinates_symm, upper_eq_transvection,
    upper_eq_transvection, triangular_conj_upper ((mem_rankOneBorel_iff _).mp g.property)]

theorem coreAction_diag (a : F) (ha : a ≠ 0) (b : F) :
    coreAction ⟨diag2 a ha, diag_mem_rankOneBorel a ha⟩ b = a ^ 2 * b := by
  rw [coreAction_apply]
  rfl

theorem coreAction_transitive (b c : F) (hb : b ≠ 0) (hc : c ≠ 0) :
    ∃ g : B0, coreAction g b = c := by
  have hs : ∀ d : F, (d ^ 2) ^ 2 = d := by decide +kernel
  let a := (c / b) ^ 2
  have ha : a ≠ 0 := pow_ne_zero _ (div_ne_zero hc hb)
  refine ⟨⟨diag2 a ha, diag_mem_rankOneBorel a ha⟩, ?_⟩
  rw [coreAction_diag]
  change ((c / b) ^ 2) ^ 2 * b = c
  rw [hs, div_mul_cancel₀ _ hb]

instance coreAction_irreducible : IsIrreducible coreAction :=
  irreducible_of_transitive _ coreAction_transitive

theorem coreAction_noncentral : ∃ g b, coreAction g b ≠ b := by
  have h : ∃ a : F, a ≠ 0 ∧ a ^ 2 ≠ 1 := by decide +kernel
  obtain ⟨a, ha, ha1⟩ := h
  exact ⟨⟨diag2 a ha, diag_mem_rankOneBorel a ha⟩, 1, by
    simpa only [coreAction_diag, mul_one] using ha1⟩

theorem coreAction_finrank : Module.finrank (ZMod 2) F = 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := F)
  rw [Nat.card_eq_fintype_card, card_field, Nat.card_eq_fintype_card, ZMod.card] at hc
  exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) hc).symm
end Representation.SL2FourNatural.BorelDualCore

namespace Representation.SL2FourNatural.BorelDualCore
open NoncentralChiefRefinement
variable {K M : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
  (N : NormalNode K) (ρ : Representation (ZMod 2) K M)
  (e : N.val ≃* Multiplicative M)
  (he : ∀ k x, (e (MulAut.conjNormal k x)).toAdd = ρ k (e x).toAdd)

/-- The literal quotient above the identity has one-copy equivariant coordinates. -/
def singleCoordinates : SectionCoordinates ⊥ N ρ 1 := by
  let q : N.val →* Multiplicative (Fin 1 → M) := {
    toFun x := Multiplicative.ofAdd (fun _ => (e x).toAdd)
    map_one' := by
      apply Multiplicative.toAdd.injective
      funext i
      exact congrArg Multiplicative.toAdd e.map_one
    map_mul' x y := by
      apply Multiplicative.toAdd.injective
      funext i
      exact congrArg Multiplicative.toAdd (e.map_mul x y) }
  have hq : Function.Surjective q := by
    intro v
    refine ⟨e.symm (Multiplicative.ofAdd (v.toAdd 0)), ?_⟩
    apply Multiplicative.toAdd.injective
    funext i
    change (e (e.symm (Multiplicative.ofAdd (v.toAdd 0)))).toAdd = v.toAdd i
    rw [e.apply_symm_apply]
    exact congrArg v.toAdd (Subsingleton.elim (0 : Fin 1) i)
  have hk : q.ker = (⊥ : NormalNode K).val.subgroupOf N.val := by
    ext x
    change (fun _ : Fin 1 => (e x).toAdd) = 0 ↔ x.val = 1
    constructor
    · intro hx
      have hz : e x = 1 := Multiplicative.toAdd.injective (congrFun hx 0)
      exact congrArg Subtype.val (e.injective (hz.trans e.map_one.symm))
    · intro hx
      have hx' : x = 1 := Subtype.ext hx
      simp only [hx', map_one]
      rfl
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective q hq), ?_⟩
  intro k x i
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ((⊥ : NormalNode K).val.subgroupOf N.val) x
  rw [sectionAction_mk]
  exact he k x
end Representation.SL2FourNatural.BorelDualCore
