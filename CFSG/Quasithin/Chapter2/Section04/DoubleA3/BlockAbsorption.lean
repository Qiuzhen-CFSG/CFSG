module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ModuleAbsorption
public import Theory.GroupTheory.ConjugatePairInternalLift
public import Theory.GroupAction.MaximalCosetOrbit
public import Theory.GroupTheory.GeneralizedFitting.CubicActorAbsorption
public import Theory.SpecificGroups.PSL3Two.InvolutionResidual

/-!
# Absorbing the whole original cubic block

After placing its four-group in the component, the two-core centralizes that
four-group. The original actor moves it, so the index-two source geometry
puts the two-core in the Thompson subgroup, which normalizes the full block.
The faithful two-perfect block then lies in the component whenever its outer
automorphism group is a two-group.

Source: Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

theorem SourceCentralizerGeometry.first_block_le_component_of_first_module
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (hU : c.U₁ ≤ K.map (involutionCentralizer g.z₂).subtype)
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (hout : IsPGroup 2 (MulAut.Outer K)) :
    d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype := by
  let H := involutionCentralizer g.z₂
  let A := d.block.map d.H.subtype
  let L := A.subgroupOf H
  let U := c.U₁.subgroupOf H
  let R := (sourceR d).subgroupOf H
  have hLH : A ≤ H := g.first_block_le_second_centralizer
  have hUH : c.U₁ ≤ H := (map_subtype_le _).trans hLH
  have hRH : sourceR d ≤ H := fun r hr => mem_centralizer_singleton_iff.mpr (g.second_fixed r hr)
  obtain ⟨hKn,_,hF⟩ := g.component_structure_of_first_module h K hK hU ho
  let := hKn
  have hUK : U ≤ K := by
    intro u hu
    obtain ⟨k,hk,he⟩ := hU hu
    exact H.subtype_injective he ▸ hk
  let : Group.IsNilpotent (pCore 2 H) := (pCore_isPGroup (p := 2) (G := H)).isNilpotent
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  have hKC : K ≤ centralizer (pCore 2 H : Set H) :=
    hK.le_centralizer_of_solvable_normal (pCore 2 H)
  have hQC : pCore 2 H ≤ centralizer (U : Set H) :=
    (le_centralizer_iff.mp hKC).trans (centralizer_le hUK)
  have hRU : R ≤ normalizer (U : Set H) := by
    intro r hr
    apply mem_normalizer_iff.mpr
    intro u
    change u ∈ U ↔ (r:H)*(u:H)*(r:H)⁻¹ ∈ U
    exact mem_normalizer_iff.mp (c.first.coordinates.normalizes
      (show ((r:H):G) ∈ ChapterB.baumann ((d.S:Subgroup d.H).map d.H.subtype) from c.baumann.symm ▸ hr)) (u:G)
  have hxH : c.x ∈ H := g.x_second
  let xH : H := ⟨c.x,hxH⟩
  have hxP : xH ∈ (g.P₂ : Subgroup H) := by
    have hh : c.x ∈ (g.P₂ : Subgroup H).map H.subtype :=
      g.second_span ▸ mem_sup_right (mem_zpowers c.x)
    obtain ⟨v,hv,he⟩ := hh
    have hev : v = xH := H.subtype_injective he
    exact hev ▸ hv
  have hxNU : xH ∉ normalizer (U : Set H) := by
    intro hn
    have hnG : c.x ∈ normalizer (c.U₁ : Set G) := by
      have hh := mem_normalizer_iff_map_conj_eq.mp hn
      have hm := congrArg (Subgroup.map H.subtype) hh
      change (U.conjBy xH).map H.subtype = U.map H.subtype at hm
      rw [map_conjBy_hom,map_subgroupOf_eq_of_le hUH] at hm
      exact mem_normalizer_iff_map_conj_eq.mpr hm
    have he := mem_normalizer_iff_map_conj_eq.mp ((normalizer (c.U₁:Set G)).inv_mem hnG)
    exact c.noncommuting (he ▸ c.U₁.le_centralizer)
  have hRP : R ≤ (g.P₂ : Subgroup H) := by
    intro r hr
    have hh : ((r:H):G) ∈ (g.P₂ : Subgroup H).map H.subtype := g.second_span ▸ mem_sup_left hr
    obtain ⟨v,hv,he⟩ := hh
    exact H.subtype_injective he ▸ hv
  have hi : R.relIndex (g.P₂ : Subgroup H) = 2 := by
    have hh := relIndex_map_map_of_injective R (g.P₂ : Subgroup H) H.subtype_injective
    rw [map_subgroupOf_eq_of_le hRH] at hh
    exact hh.symm.trans g.second_index
  have hQR : pCore 2 H ≤ R := by
    intro q hq
    by_contra hqR
    have hs := sup_zpowers_eq_of_relIndex_prime hRP Nat.prime_two hi
      (pCore_isPGroup.le_sylow_of_normal g.P₂ hq) hqR
    have hPN : (g.P₂ : Subgroup H) ≤ normalizer (U : Set H) := by
      rw [←hs]
      exact sup_le hRU (zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ (hQC hq)))
    exact hxNU (hPN hxP)
  have hRL : R ≤ normalizer (L : Set H) := by
    intro r hr
    apply mem_normalizer_iff.mpr
    intro l
    exact mem_normalizer_iff.mp (c.first.normalizes
      (show ((r:H):G) ∈ ChapterB.baumann ((d.S:Subgroup d.H).map d.H.subtype) from c.baumann.symm ▸ hr)) (l:G)
  obtain ⟨f,hf,ha⟩ := g.faithful_first_block_action hG h K hK
  have hfaith : L ⊓ centralizer (K : Set H) = ⊥ := by
    apply bot_unique
    intro l hl
    have he : f ⟨(l:G),hl.1⟩ = 1 := by
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      apply Subtype.ext
      rw [ha]
      change (l:G)*(k:G)*(l:G)⁻¹ = (k:G)
      have hecomm : (l:G)*(k:G) = (k:G)*(l:G) :=
        congrArg H.subtype (mem_centralizer_iff.mp hl.2 (k:H) k.property).symm
      rw [hecomm, mul_inv_cancel_right]
    have he1 := hf (he.trans (map_one f).symm)
    exact mem_bot.mpr (H.subtype_injective (congrArg Subtype.val he1))
  have hpL : IsPPerfect 2 L := c.first.short.twoPerfect.of_surjective
    (subgroupOfEquivOfLe hLH).symm.toMonoidHom (subgroupOfEquivOfLe hLH).symm.surjective
  have hLK : L ≤ K := twoPerfect_le_component_of_normalized_core K L (pCore 2 H) hF hKC
    pCore_isPGroup hpL hout (hQR.trans hRL) hfaith
  change A ≤ K.map H.subtype
  rw [←map_subgroupOf_eq_of_le hLH]
  exact map_mono hLK
/-- The retained linear-three binary model contains the literal first block. -/
theorem SourceCentralizerGeometry.linear_three_two_absorbs_first_block
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K)
    (α : MulAut K)
    (hα : ∀ k : K, ((α k : involutionCentralizer g.z₂) : G) =
      (g.z₁*g.z₂)*(k:G)*(g.z₁*g.z₂)⁻¹)
    (hinner : α ∈ (MulAut.conj : K →* MulAut K).range)
    (ho : pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥)
    (e : K ≃* Matrix.PSL3Two.PSL) :
    d.block.map d.H.subtype ≤ K.map (involutionCentralizer g.z₂).subtype := by
  have hz : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro k hk
    have he := (centerCongr e ⟨k,hk⟩).property
    change e k ∈ center Matrix.PSL3Two.PSL at he
    rw [Matrix.PSL3Two.Automorphisms.center_psl_eq_bot,mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hout : IsPGroup 2 (MulAut.Outer K) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
      (MulAut.outerCongr (e.trans Matrix.PSL3Two.equiv.symm)).symm
  exact g.first_block_le_component_of_first_module hG h K hK
    (g.first_module_le_component hG h K hK α hα hinner hz) ho hout
end CFSG.Quasithin.Chapter2.DoubleA3
