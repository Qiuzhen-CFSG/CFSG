module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.BlockModuleSource.MovedControl
public import CFSG.Quasithin.ChapterB.Section02.FullOffenderMovement

/-!
# C.1.28 block lifting from original Thompson movement

The local seed's image is quasisimple or has order three. The internal
full-offender theorem supplies exactly the B.1.13 movement identity from
K=[K,J(T)]. The actual block lift, natural-module recognition and exceptional
A₇ control then give a moved ambient χ-block outside the same control group.
Only the preceding local χ-seed and its omega-module support remain.

Source: Aschbacher--Smith C.1.26--28, pp.132--134.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
open ChapterB SourceInduction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Literal C.1.28 application of the local seed, retaining original J(T). -/
theorem source_outside_moved_chi_of_thompson_seed
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (h4 : ProjectiveLine.IrreducibleClassificationInput.{u,u} KnownSimple.IsKnownSimple)
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hf : generalizedFitting G = pCore 2 G)
    (M K V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hM : (T : Subgroup G).characteristicNormalizerClosure ≤ M)
    (hout : ¬ K ≤ M)
    (hV : V = normalClosure (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hK : IsChiBlock K) (hs : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal)
    (hU : (blockU K).map K.subtype ≤ V)
    (hJ : K = ⁅K, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆) :
    ∃ L : Subgroup G, K ≤ L ∧ ¬ L ≤ M ∧ IsChiBlockIn L ∧
      (blockU L).map L.subtype ≤ V ∧
      L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  have hVT : V ≤ (T : Subgroup G) :=
    (IsElementaryAbelian.isPGroup 2 V).le_sylow_of_normal T
  have hmove := internal_full_best_movement V (QuotientGroup.mk' (centralizer (V : Set G)))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) K (T : Subgroup G)
    T.isPGroup' hVT hs (ComponentSource.short_image_kind V K hK.short hU) hJ
  exact source_outside_moved_chi_of_local_seed hA hC h4 hG T hf M K V hM hout hV hK hs hU hJ hmove

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.BlockModuleSource
