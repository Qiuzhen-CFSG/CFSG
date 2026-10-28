module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicRankThreeComplete.Catalogue.SevenKernel.Inputs
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.BlockSelection

/-!
# Excluding the characteristic alternative on the actual radical

A nontrivial characteristic subgroup of Baum(R) is characteristic in R.
If it were normal in KR, characteristic-normalizer control would put all
of KR in its proper local overgroup, contrary to the source escape. This
removes the first C.1.24 alternative for the literal radical; R need not
be Sylow.

Source: Aschbacher--Smith C.1.24(a), pp.130--131, and C.2.3, p.144.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source
variable {G : Type*} [Group G] [Finite G] {H K R M : Subgroup G}

/-- Source characteristic control excludes the actual Baumann obstruction. -/
theorem baumann_characteristic_not_normal
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (D : Subgroup (ChapterB.baumann (R.subgroupOf (K ⊔ R))))
    (hD : D.Characteristic) (hne : D ≠ ⊥) :
    ¬ (D.map (ChapterB.baumann (R.subgroupOf (K ⊔ R))).subtype).Normal := by
  let := hD
  intro hn
  let := hn
  have hc := ChapterC.RankOne.ChiProduct.SelectedRankOne.characteristic_baumann_normalizer_le_control
    (R.subgroupOf (K ⊔ R)) D hne
  rw [normalizer_eq_top] at hc
  have hi := source_join_input h
  have ht : (M ⊓ (K ⊔ R)).subgroupOf (K ⊔ R) = ⊤ :=
    top_unique (hc.trans hi.setup.characteristic_control)
  exact hi.outside (hi.component.1.trans (subgroupOf_eq_top.mp ht))

/-- Relative source selection suffices; its characteristic alternative is impossible. -/
theorem block_of_selection (h : Input KnownSimple.IsKnownSimple H R M K)
    (hs : SelectionConclusion K R) : ChapterC.IsBlock (K.subgroupOf (K ⊔ R)) := by
  rcases hs with ⟨D,hD,hne,hn⟩ | hb
  · exact (baumann_characteristic_not_normal h D hD hne hn).elim
  · exact hb

end CFSG.Quasithin.Chapter14.Section06.ParabolicCatalogue.SevenKernel
