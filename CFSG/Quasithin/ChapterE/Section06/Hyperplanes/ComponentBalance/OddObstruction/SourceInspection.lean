module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Adequate
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.SourceDetection
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.SmallBorel
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.ExtraModels
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.SymplecticFour
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Inspection.AlternatingSix
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.SourceInheritance
/-!
# Original E.6.19 and its odd-core and hyperplane consumers

The component detected by a balance failure acts on its original Sylow subgroup.
The complete small-Borel and extra-model inspections eliminate those rows; the
symplectic and alternating-six inspections leave exactly the two seven-models.
Only the model and corank clauses of E.6.8 are needed. In particular, this proof
does not require a fixed-space equality for the odd or linear-four rows.

Original E.6.18 now gives E.6.19 balance. The existing signalizer, odd-core
and component-enlargement arguments then supply E.6.20–22, with their earlier
local facts and I.3 orbit/projection source already discharged.
Source: Aschbacher–Smith, E.6.19–22, printed pp.252–254.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
open Components
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V A U L : Subgroup G}

theorem detected_isSeven_of_adequate
    (h : HypothesisE61 K T M V) (hA : A ∈ obstructionFamily M V)
    (hcor : subgroupCorank V A = 2) (hUV : U ≤ V) (hindex : A.relIndex U = 2)
    (d : DetectedComponent A U V L)
    (ha : AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) L) :
    IsSeven L := by
  have hi := detected_sylowFixedInvolution h hA hUV hindex d
  let _ := d.quasisimple
  rcases ha with ⟨n,b⟩ | ⟨n,s⟩ | h4 | halt | ho
  · exact (detected_not_smallBorel h hA hUV hindex d (borel_models hcor b).2).elim
  · rcases symplectic_small_models hcor s with hm | hm
    · exact (d.action_oddCore (symplectic_four_oddCore_eq_bot d.quasisimple hi hm)).elim
    · exact (d.action_oddCore (alternating_six_oddCore_eq_bot hi hm)).elim
  · exact (detected_not_extraModel h hA hUV hindex d (Or.inl h4.1)).elim
  · rcases halt.model with h7 | h6 | h7
    · exact Or.inl h7
    · exact (d.action_oddCore (alternating_six_cover_oddCore_eq_bot hi h6)).elim
    · exact Or.inr h7
  · exact (detected_not_extraModel h hA hUV hindex d (Or.inr ho.1)).elim

theorem source_oddCoreObstruction
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    OddCoreObstruction M V := by
  intro A hA hcor U hAU hUV hindex hfail
  obtain ⟨L,d⟩ := source_detectedComponent h hA hAU hUV hfail
  exact ⟨L,d.component,detected_isSeven_of_adequate h hA hcor hUV hindex d
    (h68 A hA L d.component)⟩

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes
open Components ComponentBalance Enlargement SignalizerElimination
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V : Subgroup G}

theorem source_hyperplaneBalance [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    HyperplaneBalance V := by
  intro W W0 hW hW0
  by_contra hfail
  have h6 := fun (A : Subgroup G) (_ : A ≠ ⊥) (hAM : A ≤ M) (hp : IsPGroup 2 A) =>
    h.localCentralizer_characteristicTwo (source_earlierLocalFacts h) hAM hp
  obtain ⟨_,hA,hcor,hindex⟩ := balance_failure_setup h h15 h6 hW hW0 hfail
  obtain ⟨L,hL,hs⟩ := OddObstruction.source_oddCoreObstruction h h68
    (W ⊓ W0) hA hcor W inf_le_left hW.1 hindex hfail
  exact h18 (W ⊓ W0) hA hcor.le L hL hs
/-- The full E.6.21 conclusion from the original E.6.18 and component sieve. -/
theorem source_oddCoreFree [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    OddCoreFree V :=
  source_oddCoreFree_of_balance h h15 h311 (source_hyperplaneBalance h h15 h18 h68)

/-- E.6.22 with balance and the global odd-core conclusion supplied by source. -/
theorem source_hyperplane_characteristicTwo_of_model_sources [IsElementaryAbelian 2 V]
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (h15 : HypothesisE615 V)
    (h311 : InvariantSubspaces.CommonNormalInput KnownSimple.IsKnownSimple T)
    (h18 : SevenExcluded M V)
    (h68 : ∀ A ∈ obstructionFamily M V, ∀ X : Subgroup G, CentralizerComponent A X →
      AdequateComponentAlternatives M V A (sylowCentralizer (T : Subgroup G) V) X) :
    ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) :=
  source_hyperplane_characteristicTwo h h15 h311 h18
    (source_oddCoreFree h h15 h311 h18 h68) h68
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes
