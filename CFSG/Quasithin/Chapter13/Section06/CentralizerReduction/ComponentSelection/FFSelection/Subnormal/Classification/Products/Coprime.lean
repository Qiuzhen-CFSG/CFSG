module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Setup

/-!
# Coprime lifting for the cubic product deductions

Averaging over an order-three subgroup annihilates its moved space and is
identity on its binary fixed space. Thus projection modulo any fixed kernel
is injective on the moved space. This applies both to the global quotient
V/C_V(J) in B.5.6(3) and to the internal fixed quotient in B.5.6(5b),
without splitting V or assuming the cubic normal.

The final two lemmas apply these injections to the literal offender restriction
of `CubicHypothesis`; their section dimensions remain explicit.

Source: Aschbacher–Smith, B.5.6, printed p.105, and 13.6.10, printed p.928.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W) (A : Subgroup D)

/-- Averaging separates the cubic moved and fixed spaces. -/
theorem cubic_disjoint_fixedSpace (hc : Nat.card A = 3) :
    Disjoint (moved ρ A) (fixedSpace ρ A) := by
  classical
  let := Fintype.ofFinite A
  let P := norm (ρ.comp A.subtype)
  have hz : moved ρ A ≤ LinearMap.ker P := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, v, _, rfl⟩
    change P (ρ a v - v) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (norm_self_apply (ρ.comp A.subtype) ⟨a, ha⟩ v)
  rw [Submodule.disjoint_def]
  intro v hv hf
  have hp := hz hv
  change P v = 0 at hp
  have hvp : P v = v := by
    have hh : Fintype.card A = 3 := by rwa [← Nat.card_eq_fintype_card]
    change (∑ a : A, (ρ.comp A.subtype) a) v = v
    simp only [LinearMap.sum_apply, show ∀ a : A, (ρ.comp A.subtype) a v = v from hf,
      Finset.sum_const, Finset.card_univ, hh]
    have hone : (3 : ZMod 2) = 1 := by decide
    rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2)]
    change (3 : ZMod 2) • v = v
    rw [hone, one_smul]
  exact hvp.symm.trans hp

/-- The actual global-fixed quotient map is injective on a cubic moved space. -/
theorem cubic_finrank_le_quotientImage [FiniteDimensional (ZMod 2) W] (hc : Nat.card A = 3)
    (U : Subrepresentation ρ) (hU : moved ρ A ≤ U.toSubmodule) :
    Module.finrank (ZMod 2) (moved ρ A) ≤
      Module.finrank (ZMod 2) ((fixed ρ).quotientImage U).toSubmodule := by
  let f : moved ρ A →ₗ[ZMod 2] ((fixed ρ).quotientImage U).toSubmodule :=
    { toFun := fun v => ⟨ρ.invariants.mkQ v, ⟨v, hU v.property, rfl⟩⟩
      map_add' := by intros; apply Subtype.ext; simp; rfl
      map_smul' := by intros; apply Subtype.ext; simp; rfl }
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    apply Subtype.ext
    apply Submodule.disjoint_def.mp (cubic_disjoint_fixedSpace ρ A hc) v v.property
    have hf : (v : W) ∈ ρ.invariants := by
      exact (Submodule.Quotient.mk_eq_zero _).mp (congrArg Subtype.val hv)
    exact fun a => hf a
  exact LinearMap.finrank_le_finrank_of_injective hi

/-- Any quotient with cubic-fixed kernel preserves the cubic moved-space rank. -/
theorem cubic_finrank_le_fixedQuotient [FiniteDimensional (ZMod 2) W] (hc : Nat.card A = 3)
    (U : Submodule (ZMod 2) W) (hU : moved ρ A ≤ U)
    (K : Submodule (ZMod 2) U) (hK : ∀ v ∈ K, (v : W) ∈ fixedSpace ρ A) :
    Module.finrank (ZMod 2) (moved ρ A) ≤ Module.finrank (ZMod 2) (U ⧸ K) := by
  let f : moved ρ A →ₗ[ZMod 2] (U ⧸ K) := K.mkQ.comp (Submodule.inclusion hU)
  have hi : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    apply Subtype.ext
    exact Submodule.disjoint_def.mp (cubic_disjoint_fixedSpace ρ A hc) v v.property
      (hK (Submodule.inclusion hU v) ((Submodule.Quotient.mk_eq_zero K).mp hv))
  exact LinearMap.finrank_le_finrank_of_injective hi

open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
variable [FiniteDimensional (ZMod 2) W]

omit [FiniteDimensional (ZMod 2) W] in
private theorem moved_mono {E : Type*} [Group E]
    (σ : Representation (ZMod 2) E W) {B F : Subgroup E} (hBF : B ≤ F) :
    moved σ B ≤ moved σ F := by
  apply Submodule.span_mono
  rintro _ ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, hBF hb, v, hv, rfl⟩

/-- The quotient section in B.5.6(3) bounds the original moved space.
The lower bound uses the faithful cubic hypothesis on the original action. -/
theorem moved_eq_two_of_factor_section {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (F : Subgroup (offenderSubgroup ρ)) (U : Subrepresentation (offenderRepresentation ρ))
    (hAF : A.subgroupOf (offenderSubgroup ρ) ≤ F)
    (hU : moved (offenderRepresentation ρ) F ≤ U.toSubmodule)
    (hd : Module.finrank (ZMod 2)
      ((fixed (offenderRepresentation ρ)).quotientImage U).toSubmodule = 2) :
    Module.finrank (ZMod 2) (moved ρ A) = 2 := by
  have hh := cubic_finrank_le_quotientImage (offenderRepresentation ρ)
    (A.subgroupOf (offenderSubgroup ρ)) h.internal_card U
    ((moved_mono _ hAF).trans hU)
  have ht := Submodule.finrank_mono (marked_commutator ρ A h.le_offender ⊤).ge
  exact le_antisymm (ht.trans (hh.trans_eq hd)) h.two_le_moved

/-- The internal fixed quotient in B.5.6(5b) bounds the original moved
space. The kernel is fixed by A because A lies in the actual second factor. -/
theorem moved_eq_two_of_internal_section {S : Sylow 2 D} {C : Subgroup D}
    (h : CubicHypothesis ρ A S C)
    (F : Subgroup (offenderSubgroup ρ)) (U : Subrepresentation (offenderRepresentation ρ))
    (hAF : A.subgroupOf (offenderSubgroup ρ) ≤ F)
    (hU : moved (offenderRepresentation ρ) F ≤ U.toSubmodule)
    (hd : Module.finrank (ZMod 2)
      (U.toSubmodule ⧸ (Representation.invariants (U.toRepresentation.comp F.subtype))) = 2) :
    Module.finrank (ZMod 2) (moved ρ A) = 2 := by
  have hh := cubic_finrank_le_fixedQuotient (offenderRepresentation ρ)
    (A.subgroupOf (offenderSubgroup ρ)) h.internal_card U.toSubmodule
    ((moved_mono _ hAF).trans hU) (Representation.invariants (U.toRepresentation.comp F.subtype))
    (fun v hv a => congrArg Subtype.val (hv ⟨a, hAF a.property⟩))
  have ht := Submodule.finrank_mono (marked_commutator ρ A h.le_offender ⊤).ge
  exact le_antisymm (ht.trans (hh.trans_eq hd)) h.two_le_moved

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
