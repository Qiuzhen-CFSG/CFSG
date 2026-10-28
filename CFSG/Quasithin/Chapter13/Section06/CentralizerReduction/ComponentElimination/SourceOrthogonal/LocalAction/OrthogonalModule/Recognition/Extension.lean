module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition.Section
public import Theory.Representation.BinaryPermutation.EightCommutant

/-!
# Extending the chosen component coordinates to the plus action

The marked symmetric extension retains the chosen identification of K⁺ with
A₈. For every plus actor, the discrepancy between its transported linear
action and the standard symmetric action centralizes A₈. The actual natural
module has trivial linear centralizer, so that discrepancy is the identity.
The original coordinates therefore intertwine the entire plus action.

The upper space and its full fixed submodule are retained literally. This
step assumes component natural-module recognition; it does not eliminate the
other B.5.1 alternatives or assert a splitting of W_K.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the paragraph
following 13.6.23, printed p.933/PDF p.950.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) D V) (C : Subgroup D) [C.Normal]

private theorem extend_intertwiner
    (rigid : ∀ (f : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 8)),
      (∀ g : alternatingGroup (Fin 8), ∀ x,
        f (BinaryPermutation.naturalRepresentation (Fin 8) g.val x) =
          BinaryPermutation.naturalRepresentation (Fin 8) g.val (f x)) →
      f = LinearEquiv.refl _ _)
    (e : ActionEquiv (σ.comp C.subtype) (alternatingNatural 8))
    (E : D ≃* Equiv.Perm (Fin 8)) (hE : ∀ k : C, E k = (e.groupEquiv k).val)
    (g : D) (w : V) :
    e.linearEquiv (σ g w) =
      BinaryPermutation.naturalRepresentation (Fin 8) (E g) (e.linearEquiv w) := by
  let τ := BinaryPermutation.naturalRepresentation (Fin 8)
  have hinter (k : C) (x : V) : e.linearEquiv (σ k x) =
      τ (e.groupEquiv k).val (e.linearEquiv x) := by
    simpa only [alternatingNatural, MonoidHom.comp_apply, Subgroup.coe_subtype] using
      e.intertwines k x
  let F := ((e.linearEquiv.symm.trans (LinearEquiv.ofBijective (σ g) (σ.apply_bijective g))).trans
    e.linearEquiv).trans (LinearEquiv.ofBijective (τ (E g)⁻¹) (τ.apply_bijective (E g)⁻¹))
  have hF : ∀ k : alternatingGroup (Fin 8), ∀ x, F (τ k.val x) = τ k.val (F x) := by
    intro k x
    obtain ⟨k, rfl⟩ := e.groupEquiv.surjective k
    let k' : C := ⟨g * (k : D) * g⁻¹, (inferInstance : C.Normal).conj_mem k k.property g⟩
    have hek : e.linearEquiv.symm (τ (e.groupEquiv k).val x) =
        σ k (e.linearEquiv.symm x) := by
      apply e.linearEquiv.injective
      simpa only [LinearEquiv.apply_symm_apply] using
        (hinter k (e.linearEquiv.symm x)).symm
    have hconj : (e.groupEquiv k').val = E g * (e.groupEquiv k).val * (E g)⁻¹ := by
      rw [← hE k']
      change E (g * (k : D) * g⁻¹) = _
      rw [map_mul, map_mul, map_inv, hE k]
    change τ (E g)⁻¹ (e.linearEquiv (σ g (e.linearEquiv.symm (τ (e.groupEquiv k).val x)))) = _
    rw [hek]
    have hmul : σ g (σ k (e.linearEquiv.symm x)) =
        σ k' (σ g (e.linearEquiv.symm x)) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      change g * (k : D) = (g * (k : D) * g⁻¹) * g
      group
    rw [hmul, hinter]
    change τ (E g)⁻¹ (τ (e.groupEquiv k').val (e.linearEquiv (σ g (e.linearEquiv.symm x)))) =
      τ (e.groupEquiv k).val (τ (E g)⁻¹ (e.linearEquiv (σ g (e.linearEquiv.symm x))))
    rw [hconj]
    simp only [← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have h := congrArg (fun f : BinaryPermutation.natural (Fin 8) ≃ₗ[ZMod 2]
      BinaryPermutation.natural (Fin 8) => f (e.linearEquiv w)) (rigid F hF)
  change τ (E g)⁻¹ (e.linearEquiv (σ g (e.linearEquiv.symm (e.linearEquiv w)))) =
    e.linearEquiv w at h
  rw [LinearEquiv.symm_apply_apply] at h
  have hh := congrArg (τ (E g)) h
  simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply] using hh

section Local
open ComponentSelection
open scoped IsMulCommutative
variable {G : Type*} [Group G] (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    [IsElementaryAbelian 2 (WK K L T z v)]

/-- Component recognition gives a natural moved section for the entire plus
actor, with the same upper space, fixed kernel, and linear coordinates. -/
theorem naturalMovedSection_of_component_coordinates
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (e : ActionEquiv (s.action.comp (plusImage K L T z v hL hz K).subtype)
      (alternatingNatural 8)) : Nonempty (NaturalMovedSection K L T z v hL hz) := by
  obtain ⟨E, hE, hC⟩ := exists_marked_symmetricEquiv K L T z v hL hz hK hLK
    e.groupEquiv hT hcore hout
  let : (plusImage K L T z v hL hz K).Normal :=
    plusComponent_normal K L T z v hL hz hLK hK
  exact ⟨{
    actor := E
    component_image := hC
    upper := s.space
    upper_mem := section_upper_mem K L T z v hL hz s
    central := s.central
    central_mem := section_central_mem K L T z v hL hz s
    coordinates := e.linearEquiv
    equivariant := extend_intertwiner s.action (plusImage K L T z v hL hz K)
      BinaryPermutation.EightCommutant.commuting_eq_refl e E hE }⟩

/-- The source recognition owner need only select the component's actual
natural action. The full plus-action extension is discharged here. -/
theorem naturalMovedSection_of_component_natural
    (hK : Tv T v ≤ normalizer (K : Set G)) (hLK : Lv L v ≤ K)
    (hT : IsPGroup 2 (Tv T v)) (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hout : ¬ plusImage K L T z v hL hz (Tv T v) ≤ plusImage K L T z v hL hz K)
    (s : MovedSection (representation K L T z v hL hz) (plusImage K L T z v hL hz K))
    (hnatural : IsAlternatingNatural
      (s.action.comp (plusImage K L T z v hL hz K).subtype) 8) :
    Nonempty (NaturalMovedSection K L T z v hL hz) := by
  obtain ⟨e⟩ := hnatural
  exact naturalMovedSection_of_component_coordinates K L T z v hL hz
    hK hLK hT hcore hout s e

end Local
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.LocalAction.OrthogonalModule.Recognition

