module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.RefinedComponent
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.AlternatingActions

/-!
# Refinement of the raw cover and sporadic rows at the actual component

The original marked action is transported through the literal inclusion
K → C_G(z₂) → G before applying the completed 2.3.9 calculations. The
central-two-cover row leaves precisely PSL₃(4). The sporadic row leaves
M₁₁, M₂₂, M₂₃ and the genuine binary M₂₂ quotient, with its kernel order.
Every equivalence in the result is transported back to the original K.

These are branch reductions, not a model selection from an unrelated
refined intersection. Source: Aschbacher–Smith 2.3.9(7), pp.525–526,
used in the paired-cubic inspection 2.4.32, p.547.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ComponentRefinement ClassificationModels
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

theorem SourceCentralizerGeometry.two_cover_component_refined
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (hz : center K = pCore 2 K) (hzn : center K ≠ ⊥)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨ IsG2At (K ⧸ pCore 2 K) 4) :
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 := by
  rcases hm with hm | ⟨F,_,_,hF,⟨f⟩⟩
  · exact hm
  · let H := involutionCentralizer g.z₂
    let A := K.map H.subtype
    let e : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
    let q : (K ⧸ pCore 2 K) ≃* (A ⧸ pCore 2 A) :=
      QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    have hzmap : (center K).map e.toMonoidHom = center A := by
      ext a
      constructor
      · rintro ⟨k,hk,rfl⟩
        exact (centerCongr e ⟨k,hk⟩).property
      · intro ha
        exact ⟨e.symm a,(centerCongr e.symm ⟨a,ha⟩).property,e.apply_symm_apply a⟩
    have hzA : center A = pCore 2 A := by rw [←hzmap,←pCore_map_iso 2 e,hz]
    have hnA : pCore 2 A ≠ ⊥ := by
      intro he
      have hk := (map_eq_bot_iff_of_injective _ e.injective).mp
        ((pCore_map_iso 2 e).trans he)
      exact hzn (hz.trans hk)
    obtain ⟨t,ht⟩ := hinner
    have hi : ∃ a : A, IsConjugationProjection A (g.z₁*g.z₂) a := by
      refine ⟨e t,?_⟩
      intro a
      obtain ⟨k,rfl⟩ := e.surjective a
      have hh := hα k
      rw [←ht] at hh
      exact hh.symm
    have hg := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
    let source := g.refinement_setup hM hTM hu hg.2.2.2.2.2.1 K hK
    let localData := source.localSetup hG structural115Input localC129Input_knownSimple
    exact (LieType.G2.not_central_quotient_model localData hi hzA hnA F hF
      ⟨q.symm.trans f⟩).elim

theorem SourceCentralizerGeometry.sporadic_component_refined
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hpair : d.L0 ≠ d.block)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (name : SporadicName) (hn : name ≠ .j3)
    (hm : Nonempty ((K ⧸ pCore 2 K) ≃* name.Carrier)) :
    Nonempty (K ≃* Sporadic.Mathieu.M11) ∨ Nonempty (K ≃* Sporadic.Mathieu.M22) ∨
      Nonempty (K ≃* Sporadic.Mathieu.M23) ∨
      (Nat.card (pCore 2 K) = 2 ∧ Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22)) := by
  let H := involutionCentralizer g.z₂
  let A := K.map H.subtype
  let e : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
  let q : (K ⧸ pCore 2 K) ≃* (A ⧸ pCore 2 A) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let β := (MulAut.congr e) α
  have hβ : ∀ a : A, (β a : G) = (g.z₁*g.z₂)*(a:G)*(g.z₁*g.z₂)⁻¹ := by
    intro a
    obtain ⟨k,rfl⟩ := e.surjective a
    change ((α (e.symm (e k)) : H):G) = _
    rw [e.symm_apply_apply]
    exact hα k
  have hβi : β ∈ (MulAut.conj (G := A)).range := by
    obtain ⟨t,ht⟩ := hinner
    refine ⟨e t,?_⟩
    change MulAut.conj (e t) = (MulAut.congr e) α
    rw [←MulAut.congr_conj,ht]
  have hg := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  let source := g.refinement_setup hM hTM hu hg.2.2.2.2.2.1 K hK
  obtain ⟨f⟩ := hm
  rcases source.sporadic_intersection_or_binary_cover hG localC129Input_knownSimple
    ⟨q.symm.trans f,β,hβ,hβi⟩ hn with hh | ⟨_,hc,⟨f⟩,_⟩
  · rcases hh with ⟨⟨f⟩,_⟩ | ⟨f,_⟩ | ⟨f,_⟩
    · exact .inl ⟨e.trans f⟩
    · exact .inr (.inl ⟨e.trans f⟩)
    · exact .inr (.inr (.inl ⟨e.trans f⟩))
  · refine .inr (.inr (.inr ⟨?_,⟨q.trans f⟩⟩))
    rw [←pCore_map_iso 2 e,card_map_of_injective e.injective] at hc
    exact hc

end CFSG.Quasithin.Chapter2.DoubleA3
