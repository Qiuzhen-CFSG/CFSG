module

public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Canonical
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.Reduction

/-!
# Intrinsic recognition of the residual pair in S₆

Two generating overgroups of a common Sylow two-subgroup, each of relative
index three, are simultaneously conjugate to the incident duad and syntheme
parabolics. Their two-residuals are A₄, each residual has a Klein four
two-core, and the two cores generate D₈ with nontrivial intersection.

The reduction uses the exhaustive six-letter parabolic geometry. The canonical
calculation uses actual permutation embeddings of A₄ and D₈. Residuals and
cores are then transported through the same ambient conjugation, preserving
both the join and the intersection.

Source: Aschbacher–Smith, the paragraph after 15.4.23, printed p.1165
(PDF p.1182 of the combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition

private theorem map_core (e : S6 ≃* S6) (L : Subgroup S6) :
    (L.pCoreIn 2).map e.toMonoidHom = (L.map e.toMonoidHom).pCoreIn 2 := by
  let eL : L ≃* L.map e.toMonoidHom := e.subgroupMap L
  rw [pCoreIn, pCoreIn, ← pCore_map_iso 2 eL, map_map, map_map]
  rfl

private theorem mapped_canonical (e : S6 ≃* S6) :
    let H₁ : Subgroup S6 := duadStabilizer.map e.toMonoidHom
    let H₂ : Subgroup S6 := synthemeStabilizer.map e.toMonoidHom
    let L₁ : Subgroup S6 := (pResidual 2 H₁).map H₁.subtype
    let L₂ : Subgroup S6 := (pResidual 2 H₂).map H₂.subtype
    let U₁ : Subgroup S6 := L₁.pCoreIn 2
    let U₂ : Subgroup S6 := L₂.pCoreIn 2
    Nonempty (L₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (L₂ ≃* alternatingGroup (Fin 4)) ∧
      Nat.card U₁ = 4 ∧ Nat.card U₂ = 4 ∧
      Nonempty (↥(U₁ ⊔ U₂) ≃* DihedralGroup 4) ∧ U₁ ⊓ U₂ ≠ ⊥ := by
  dsimp only
  rw [← map_embedded_pResidual 2 duadStabilizer e.toMonoidHom,
    ← map_embedded_pResidual 2 synthemeStabilizer e.toMonoidHom,
    residual_duad, residual_syntheme,
    ← map_core e duadHom.range, ← map_core e synthemeHom.range,
    core_range duadHom duadHom_injective, core_range synthemeHom synthemeHom_injective]
  refine ⟨⟨(e.subgroupMap duadHom.range).symm.trans
      (MonoidHom.ofInjective duadHom_injective).symm⟩,
    ⟨(e.subgroupMap synthemeHom.range).symm.trans
      (MonoidHom.ofInjective synthemeHom_injective).symm⟩, ?_, ?_, ?_, ?_⟩
  · exact (Nat.card_congr ((klein.equivMapOfInjective duadHom duadHom_injective).trans
      (e.subgroupMap (klein.map duadHom))).toEquiv).symm.trans klein_card
  · exact (Nat.card_congr ((klein.equivMapOfInjective synthemeHom synthemeHom_injective).trans
      (e.subgroupMap (klein.map synthemeHom))).toEquiv).symm.trans klein_card
  · rw [← Subgroup.map_sup, core_join]
    exact ⟨(e.subgroupMap dihedralHom.range).symm.trans
      (MonoidHom.ofInjective dihedralHom_injective).symm⟩
  · rw [← map_inf _ _ e.toMonoidHom e.injective]
    intro h
    apply core_intersection
    apply e.mapSubgroup.injective
    change (klein.map duadHom ⊓ klein.map synthemeHom).map e.toMonoidHom =
      (⊥ : Subgroup S6).map e.toMonoidHom
    rwa [Subgroup.map_bot]

/-- Intrinsic recognition of the residual pair of generating index-three
Sylow overgroups in the symmetric group on six letters. -/
theorem residual_pair_recognition (T : Sylow 2 S6) (H₁ H₂ : Subgroup S6)
    (h₁ : (T : Subgroup S6) ≤ H₁) (h₂ : (T : Subgroup S6) ≤ H₂)
    (hi₁ : (T : Subgroup S6).relIndex H₁ = 3)
    (hi₂ : (T : Subgroup S6).relIndex H₂ = 3) (hgen : H₁ ⊔ H₂ = ⊤) :
    let L₁ : Subgroup S6 := (pResidual 2 H₁).map H₁.subtype
    let L₂ : Subgroup S6 := (pResidual 2 H₂).map H₂.subtype
    let U₁ : Subgroup S6 := L₁.pCoreIn 2
    let U₂ : Subgroup S6 := L₂.pCoreIn 2
    Nonempty (L₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (L₂ ≃* alternatingGroup (Fin 4)) ∧
      Nat.card U₁ = 4 ∧ Nat.card U₂ = 4 ∧
      Nonempty (↥(U₁ ⊔ U₂) ≃* DihedralGroup 4) ∧ U₁ ⊓ U₂ ≠ ⊥ := by
  obtain ⟨g, h | h⟩ := pair_conjugate T H₁ H₂ h₁ h₂ hi₁ hi₂ hgen
  · rcases h with ⟨rfl, rfl⟩
    exact mapped_canonical (MulAut.conj g)
  · rcases h with ⟨rfl, rfl⟩
    obtain ⟨hd, hs, hdc, hsc, hj, hi⟩ := mapped_canonical (MulAut.conj g)
    exact ⟨hs, hd, hsc, hdc, by rw [sup_comm]; exact hj,
      by rw [inf_comm]; exact hi⟩

end Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
