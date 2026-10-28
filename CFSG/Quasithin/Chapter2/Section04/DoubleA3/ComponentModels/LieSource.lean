module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.RefinedComponent
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.BenderOdd
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.AlternatingEight
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.SymplecticFour
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentModels.LinearThree
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.BlockAbsorption
public import Theory.GroupTheory.GeneralizedFitting.ComponentCenterPrimeCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8

/-!
# The complete raw Lie branch of the paired-cubic component inspection

The actual marked automorphism is transported along the literal inclusion of
K in the ambient group. The original refinement setup then applies the
proved 2.3.9 Lie calculations to that same action. The completed Bender,
symplectic, linear and alternating-eight screens leave exactly A₆ or PSL₃(2),
and their absorption theorems place the original first block in K.

This theorem consumes the raw `lie` constructor of 1.1.5. It does not infer
a retained model from an unrelated refined intersection.
Source: Aschbacher–Smith 2.4.32, printed p.547, using 2.3.9(7), p.525.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ComponentRefinement ClassificationModels

private theorem simple_lie_of_raw {K : Type*} [Group K]
    (hm : LieTypeTwoModel K) : LieType.SimpleLieModel K := by
  rcases hm with hm | hm | hm
  · exact .inl hm
  · apply Or.inr ∘ Or.inl
    cases hm with
    | linear f hf he => exact ⟨f,.linear hf he⟩
    | symplectic f hf he => exact ⟨f,.symplectic hf he⟩
    | g2 f hf he => exact ⟨f,.g2 hf he⟩
    | triality f hf he => exact ⟨f,.triality hf he⟩
    | ree m hm he => exact ⟨2*m+1,.ree_f4 m hm rfl
        ((ReeF4.exists_localBlockInput_mulEquiv_iff K m).mp he)⟩
    | symplectic_derived he => exact ⟨1,.symplectic_derived rfl he⟩
    | g2_derived he => exact ⟨1,.g2_derived rfl he⟩
    | tits he => exact ⟨1,.tits rfl he⟩
  · exact .inr (.inr hm)

private theorem simple_lie_transport {K A : Type*} [Group K] [Group A]
    (e : A ≃* K) (hm : LieType.SimpleLieModel K) : LieType.SimpleLieModel A := by
  rcases hm with hm | ⟨f,hm⟩ | ⟨n,hn,hm⟩
  · exact .inl (hm.of_mulEquiv e)
  · exact .inr (.inl ⟨f,hm.of_mulEquiv e⟩)
  · exact .inr (.inr ⟨n,hn,hm.of_mulEquiv e⟩)

variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- Exact raw lie branch, using the original marked refinement setup. -/
theorem SourceCentralizerGeometry.lie_component_action_source32
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
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hs : IsSimpleGroup K) (hm : LieTypeTwoModel K)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range) :
    d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype ∧
      (Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL)) := by
  let H := involutionCentralizer g.z₂
  let A := K.map H.subtype
  let e : K ≃* A := K.equivMapOfInjective H.subtype H.subtype_injective
  let := hs
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup A := e.symm.isSimpleGroup
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e
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
  have hgeom := d.paired_cubic_source_sylow_geometry hG T hM hTM hu hST hpair c.cubic_first
  let source := g.refinement_setup hM hTM hu hgeom.2.2.2.2.2.1 K hK
  let localData := source.localSetup hG structural115Input localC129Input_knownSimple
  have h115 := (g.lemma115 hG hM hTM hu).2
  have hcases := LieType.refinement_of_inner_action localData
    (simple_lie_transport e.symm (simple_lie_of_raw hm)) β hβ hβi
  have hlin (hm : ∃ n, 1 ≤ n ∧ ClassicalGroup.IsPSL K 3 (2^n)) :
      d.block.map d.H.subtype ≤ K.map H.subtype ∧
        (Nonempty (K ≃* alternatingGroup (Fin 6)) ∨ Nonempty (K ≃* Matrix.PSL3Two.PSL)) := by
    obtain ⟨n,hn,hm⟩ := hm
    obtain ⟨f⟩ := g.psl3_even_binary hG h115 K hK α hα hinner ⟨n,by omega,hm⟩
    exact ⟨g.linear_three_two_absorbs_first_block hG h115 K hK α hα hinner ho f,.inr ⟨f⟩⟩
  rcases hcases with hb | hb | ⟨f,_⟩
  · exact (g.bender_model_false hG h115 K hK α hα hs (hb.of_mulEquiv e) hinner).elim
  · rcases hb with ⟨n,hn,F,hF,hfin,hcard,⟨f⟩⟩ | ⟨n,hn,hb⟩ | hb | ⟨_,hc,_⟩
    · have hmK : LieType.IsDerivedSymplecticFour K := ⟨n,hn,F,hF,hfin,hcard,⟨e.trans f⟩⟩
      obtain ⟨he,_,hL⟩ := g.derived_symplectic_four_component_absorbs_first_block hG h115 K hK hmK
      exact ⟨hL,.inl he⟩
    · exact hlin ⟨n,hn,hb.of_mulEquiv e⟩
    · have hzA : center A = ⊥ := center_eq_bot_of_simple_perfect
      have hoK := Subgroup.IsSubnormal.pPrimeCore_eq_bot ho K hK.1
      have hoA : pPrimeCore 2 A = ⊥ := by
        rw [←pPrimeCore_map_iso 2 e,hoK,Subgroup.map_bot]
      have hpA : pCore 2 A = ⊥ := (IsQuasisimple.center_eq_pCore hoA).symm.trans hzA
      let q : A ≃* (A ⧸ pCore 2 A) :=
        (((QuotientGroup.quotientMulEquivOfEq hpA).trans QuotientGroup.quotientBot)).symm
      exact hlin ⟨2,by decide,by simpa using hb.of_mulEquiv (e.trans q)⟩
    · rw [center_eq_bot_of_simple_perfect,card_bot] at hc
      omega
  · exact (g.alternating_eight_model_false hG h115 K hK
      ((e.trans f).trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)).elim

end CFSG.Quasithin.Chapter2.DoubleA3
