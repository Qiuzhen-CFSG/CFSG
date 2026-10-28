module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.ActionSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.BlockSource
/-!
# Original Thompson action identities with the block exit

The faithful source classification and the actual Baumann arguments give
all common action, alpha and orbit identities on the original reduced
module. The block exit is now obtained internally from the complete C.1.29
and the original symmetric-five characteristic-pair source. Its hypothesis
quantifies characteristic subgroups of Baum(T), not of T. The general exit
uses χ₀ exactly as defined in C.1.12; its strict nonsolvable specialization
is exported alongside it. Factorwise natural and Sylow data remain in the
unchanged marked source theorems imported by ActionSource.

Source: Aschbacher–Smith E.2.3, pp.216–217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterC
universe u
variable {G : Type u} [Group G] [Finite G]

theorem source_action_and_block_conclusions
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : generalizedFitting G = pCore 2 G)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G)) :
    letI := hU.normal
    letI := hU.elementary
    let C := centralizer (U : Set G)
    let q := QuotientGroup.mk' C
    let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
    pResidual 2 G ≤ elementaryAbelianMaxJ (⊤ : Subgroup G) ∧
      (elementaryAbelianMaxJ (⊤ : Subgroup G)).map q = offenderSubgroup α ∧
      (elementaryAbelianMaxJ (T : Subgroup G)).map q = (baumann (T : Subgroup G)).map q ∧
      thompsonAlpha (T : Subgroup G) =
        ((⁅U,pResidual 2 G⁆ : Subgroup G) ⊓
          centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ∧
      conjugateSpanBy (thompsonAlpha (T : Subgroup G)) (pResidual 2 G) =
        (⁅U,pResidual 2 G⁆ : Subgroup G) ⊔
          (thompsonAlpha (T : Subgroup G) ⊓ centralizer (pResidual 2 G : Set G)) ∧
      ((∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
          (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥) →
        ∃ L : Subgroup G, IsChiZeroBlockIn L ∧
          L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
          L ⊔ (T : Subgroup G) = ⊤ ∧ ¬L ≤ minimalParabolicMax T hP) := by
  obtain ⟨hr,hglobal,himages,halpha,horbit⟩ := source_action_conclusions hG T hP U hU hJ
  exact ⟨hr,hglobal,himages,halpha,horbit,source_chiZero_block hG T hP hf U hU hJ⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
