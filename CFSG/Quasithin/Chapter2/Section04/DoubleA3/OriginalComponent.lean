module
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.ComponentActionSource
public import CFSG.Quasithin.Chapter2.Section04.DoubleA3.MarkedCentralizers
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.CoreAction

/-!
# The actual component entering the paired-cubic census

The source first block and its commutator four-group are restricted to the
literal centralizer of the second fixed involution. Their full commutator
relation and the original 1.1.5 marking kill its odd core. The separately
proved characteristic-two exclusion then produces an ordinary component
with its actual marked model action and displacement outside M.

The only remaining earlier-source premise is precisely 2.4.31, supplied by
`SourceCentralizerGeometry.not_He_of_prior_cases`. No model or action
choice is added to the original setup. Source: Aschbacher–Smith p.547,
the paragraph preceding 2.4.32.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section03.Candidates.ComponentStructure
namespace CFSG.Quasithin.Chapter2.DoubleA3
open ChapterC ChapterC.Section05.BlockAnalysis ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
variable {d : MinimalBlockSetup M} {T : Sylow 2 G} {c : SourcePairCoordinates d T}

/-- All original centralizer inputs before the component census, with only
the separately proved characteristic-two exclusion left as a premise. -/
theorem SourceCentralizerGeometry.original_component_catalogue
    (g : SourceCentralizerGeometry c) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hn : involutionCentralizer g.z₂ ∉ Chapter1.He G) :
    pPrimeCore 2 (involutionCentralizer g.z₂) = ⊥ ∧
      ∃ K : Subgroup (involutionCentralizer g.z₂), IsComponent (involutionCentralizer g.z₂) K ∧
        K.map (involutionCentralizer g.z₂).subtype =
          ⁅K.map (involutionCentralizer g.z₂).subtype,zpowers (g.z₁*g.z₂)⁆ ∧
        ¬ K.map (involutionCentralizer g.z₂).subtype ≤ M ∧ HasModelAction115 K (g.z₁*g.z₂) := by
  let H := involutionCentralizer g.z₂
  let A := d.block.map d.H.subtype
  let L := A.subgroupOf H
  let U := c.U₁.subgroupOf H
  have hLH : A ≤ H := g.first_block_le_second_centralizer
  have hUH : c.U₁ ≤ H := (map_subtype_le _).trans hLH
  let e := subgroupOfEquivOfLe hLH
  have hp : IsPPerfect 2 L := c.first.short.twoPerfect.of_surjective
    e.symm.toMonoidHom e.symm.surjective
  let : IsElementaryAbelian 2 c.U₁ := c.first.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hUH
  have hc : ⁅U,L⁆ = U := by
    apply map_injective H.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hUH,map_subgroupOf_eq_of_le hLH]
    have hi := commutator_isPPerfect_idempotent A (pCoreIn 2 A)
      c.first.short.twoPerfect (isPGroup_pCoreIn 2 A)
      (A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
    change ⁅(blockU A).map A.subtype,A⁆ = (blockU A).map A.subtype
    simpa only [pCoreIn,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hi
  let a : H := ⟨g.z₁,hUH g.first_mem⟩
  have hf : generalizedFitting H ≠ pCore 2 H := by
    intro he
    apply hn
    apply Chapter1.mem_He_iff.mpr
    rw [←he]
    exact centralizer_generalizedFitting_le H
  exact source_centralizer_component_catalogue hG g.z₂ g.order_second g.P₂ M
    (g.z₁*g.z₂) (g.lemma115 hG hM hTM hu).2 L U hp hc a g.first_mem rfl hf

end CFSG.Quasithin.Chapter2.DoubleA3
