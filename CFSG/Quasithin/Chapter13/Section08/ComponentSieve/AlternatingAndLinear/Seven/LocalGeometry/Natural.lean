module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Basic
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
/-!
# Selecting and coordinating the natural module in the first case

The group and module clauses of 13.8.5 retain S₆, S₇ and L₄(2), each with
an actual group equivalence. A faithful seven-point action containing A₇
has order between 2520 and 5040, which excludes S₆ and L₄(2). Thus its
module is the literal binary seven-point natural module and the source
L/O₂(L) is the triple cover of A₆. Conjugating the seven coordinates then
transports the natural embedding by the same permutation.

`TransvectionModels` is an explicit earlier-theorem input, not a recognition
theorem proved here. It projects only the clauses used from 13.8.5(2–3);
no discarded six-point or four-dimensional module is restricted by the input.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.5 and 13.8.24, printed pp.947–948, 958 (1 March 2004 manuscript).
-/

public section
open Subgroup Equiv BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
variable {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]

/-- The exact equivariant natural identification, before coordinates are chosen. -/
@[expose] def SevenNaturalModel (ρ : Representation (ZMod 2) J E) : Prop :=
  ∃ e : J ≃* S7, ∃ c : core (Fin 7) ≃ₗ[ZMod 2] E,
    ∀ g v, c (coreRepresentation _ (e g) v) = ρ g (c v)

/-- The group and module clauses of 13.8.5 needed here, retaining every group
alternative. The unused six-point modules and four-point linear module are
not restricted; in the seven-point branch the whole module is natural. -/
@[expose] def TransvectionModels (ρ : Representation (ZMod 2) J E)
    {G : Type*} [Group G] (L : Subgroup G) : Prop :=
  Nonempty (J ≃* Perm (Fin 6)) ∨
  Nonempty (J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) ∨
  (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ SevenNaturalModel ρ)

private theorem linear_four_card {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) F) = 20160 := by
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
  rw [hF] at h
  norm_num [Fin.prod_univ_succ] at h
  omega

/-- The faithful seven-point action rules out S₆ and L₄(2) by their orders. -/
theorem seven_natural_of_transvection_models
    (ρ : Representation (ZMod 2) J E) {G : Type*} [Group G] (L : Subgroup G)
    (φ : J →* S7) (hφ : Function.Injective φ)
    (hAlt : alternatingGroup (Fin 7) ≤ φ.range) (hm : TransvectionModels ρ L) :
    SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ SevenNaturalModel ρ := by
  have h7 : Nat.card S7 = 5040 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hle := Nat.card_le_card_of_injective φ hφ
  have hlo : 2520 ≤ Nat.card J := by
    rw [← hA, Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact Nat.card_le_card_of_injective (inclusion hAlt) (inclusion_injective hAlt)
  unfold TransvectionModels at hm
  rcases hm with hs | hl | hm
  · obtain ⟨e⟩ := hs
    have he := Nat.card_congr e.toEquiv
    have hc : Nat.card (Perm (Fin 6)) = 720 := by
      norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    omega
  · obtain ⟨e⟩ := hl
    have he := Nat.card_congr e.toEquiv
    have hc : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 :=
      linear_four_card (Nat.card_zmod 2)
    omega
  · exact hm

/-- Changing the seven coordinates transports the embedded natural core by
that same permutation. -/
theorem naturalSubmodule_conjugate (ρ : Representation (ZMod 2) J E)
    (φ : J →* S7) (hm : HasNaturalSubmodule ρ φ) (σ : S7) :
    HasNaturalSubmodule ρ ((MulAut.conj σ).toMonoidHom.comp φ) := by
  obtain ⟨j, hj, he⟩ := hm
  let r := coreRepresentation (Fin 7)
  refine ⟨j.comp (r σ⁻¹), hj.comp (r.apply_bijective σ⁻¹).injective, ?_⟩
  intro g v
  change j (r σ⁻¹ (r (σ * φ g * σ⁻¹) v)) = ρ g (j (r σ⁻¹ v))
  rw [← Module.End.mul_apply, ← map_mul]
  have hh : σ⁻¹ * (σ * φ g * σ⁻¹) = φ g * σ⁻¹ := by group
  rw [hh, map_mul, Module.End.mul_apply]
  exact he g (r σ⁻¹ v)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
