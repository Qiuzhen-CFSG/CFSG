module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree.FaithfulAction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwoSource
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.Centralizers
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentStructure

/-!
# The original faithful A₄ action on the selected component

The first cubic block centralizes the second fixed involution. Its
2-perfectness and the component orbit bound make it normalize every
ordinary component of that centralizer. The original marked actor is its
first fixed module involution times the central second involution, so acts
nontrivially on each component. The cubic-block kernel lemma therefore
makes the actual block action faithful before any component absorption or
model selection. Source: Aschbacher–Smith 2.4.32, printed p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

omit [Finite G] in
/-- The opposite actual block centralizes the second selected involution. -/
theorem SourceCentralizerGeometry.first_block_le_second_centralizer
    (g : SourceCentralizerGeometry c) :
    d.block.map d.H.subtype ≤ involutionCentralizer g.z₂ := by
  intro l hl
  exact mem_centralizer_singleton_iff.mpr
    (c.commute ((map_subtype_le _) g.second_mem) l hl)

/-- The actual cubic block normalizes each ordinary component of G₂. -/
theorem SourceCentralizerGeometry.first_block_normalizes_component
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) :
    (d.block.map d.H.subtype).subgroupOf (involutionCentralizer g.z₂) ≤ normalizer (K : Set _) := by
  let H := involutionCentralizer g.z₂
  have hsq := hG.twoLocal_sqtk (isTwoLocal_involution_centralizer g.order_second)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  let e := subgroupOfEquivOfLe g.first_block_le_second_centralizer
  exact Chapter1.Section02.twoPerfect_normalizes_cComponent_source hQ hK.isCComponent
    (c.first.short.twoPerfect.of_surjective e.symm.toMonoidHom e.symm.surjective)

/-- The same original A₄ acts faithfully on each marked component; no
component absorption or model assumption has yet been used. -/
theorem SourceCentralizerGeometry.faithful_first_block_action
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (h : Chapter1.Lemma115Hypotheses (involutionCentralizer g.z₂) g.P₂ M (g.z₁*g.z₂))
    (K : Subgroup (involutionCentralizer g.z₂))
    (hK : IsComponent (involutionCentralizer g.z₂) K) :
    ∃ f : (d.block.map d.H.subtype) →* MulAut K, Function.Injective f ∧
      ∀ (l : d.block.map d.H.subtype) (k : K),
        ((f l k : involutionCentralizer g.z₂) : G) = (l:G)*(k:G)*(l:G)⁻¹ := by
  let H := involutionCentralizer g.z₂
  let L := d.block.map d.H.subtype
  let e := subgroupOfEquivOfLe g.first_block_le_second_centralizer
  have hn := g.first_block_normalizes_component hG K hK
  let f : L →* MulAut K := K.normalizerMonoidHom.comp
    ((inclusion hn).comp e.symm.toMonoidHom)
  have hact (l : L) (k : K) : ((f l k : H) : G) = (l:G)*(k:G)*(l:G)⁻¹ := rfl
  obtain ⟨_,α,P,hα,mark,_⟩ := h.component_inputs K hK
  have hz := g.first_mem
  change g.z₁ ∈ (blockU L).map L.subtype at hz
  obtain ⟨a,ha,he⟩ := hz
  have hea : (a:G) = g.z₁ := he
  have hf : f a = α := by
    apply MulEquiv.ext
    intro k
    apply Subtype.ext
    apply Subtype.ext
    have hkc : g.z₂*(k:G)*g.z₂⁻¹ = (k:G) := by
      rw [←mem_centralizer_singleton_iff.mp (k : H).property,mul_inv_cancel_right]
    calc
      ((f a k : H) : G) = g.z₁*(k:G)*g.z₁⁻¹ := by rw [hact,hea]
      _ = g.z₁*(g.z₂*(k:G)*g.z₂⁻¹)*g.z₁⁻¹ := by rw [hkc]
      _ = ((α k : H) : G) := by rw [hα]; group
  have hm : f a ≠ 1 := by
    intro hh
    have ho := mark.order_two
    rw [←hf,hh,orderOf_one] at ho
    norm_num at ho
  exact ⟨f,c.cubic_first.injective_of_moves_module f a ha hm,hact⟩

end CFSG.Quasithin.Chapter2.DoubleA3
