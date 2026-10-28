module
public import CFSG.Quasithin.Chapter15.Section01.SourceThompsonGeneration
public import CFSG.Quasithin.ChapterD.Section02.SymmetricThreePairCore

/-!
# Thompson generation on the proper chosen Omega support

The literal support-to-subgroup action equivalence transfers the source
proper-branch coordinates onto the chosen ambient subgroup. Cubic ratio
three halves and the symmetric-three pair force its starred core to be the
whole action image. The four-group Sylow argument then proves15.1.13(4) on
this exact chosen subgroup, retaining the exceptional order-two alternative.

Source: Aschbacher--Smith15.1.4,15.1.7(3),15.1.13(4), pp.1087,1091.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
open scoped ENNReal IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

theorem SourceCases.Proper.chosen_omega
    (T : Sylow 2 G) (M Mc V : Subgroup G) [IsElementaryAbelian 2 V]
    (hn : M ≤ normalizer (V : Set G)) (U : Submodule (ZMod 2) (Additive V))
    (h : SourceCases.Proper T M Mc V (imageRepresentation M V hn) U)
    [IsElementaryAbelian 2 ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)]
    (hnW : M ≤ normalizer (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) : Set G)) :
    SourceCases.Omega (imageRepresentation M _ hnW) := by
  obtain ⟨_,_,hdim,hstable,_,_,_,_,hpair,_,_,x,e,hcoord⟩ := h
  let a := supportActionEquiv M V hn U hstable hnW
  let l := supportLinearEquiv V U
  let xW := l.symm.trans x
  let eW := a.trans e
  have hi : ∀ g w, xW (imageRepresentation M _ hnW g w) = (eW g).val.val (xW w) := by
    intro g w
    change x (l.symm (imageRepresentation M _ hnW g w)) =
      (e (a g)).val.val (x (l.symm w))
    exact (congrArg x (supportActionEquiv_intertwines_symm M V hn U hstable hnW g w)).trans (hcoord _ _)
  have hrat := OrthogonalFourBinary.ratios_of_omega_coordinates (imageRepresentation M _ hnW) xW eW hi
  have epair := a.trans hpair.some
  exact ⟨Jhat_eq_top_of_symmetricThree_pair_ratio _ epair hrat.1,hrat.1,
    l.finrank_eq.symm.trans hdim,⟨epair⟩,xW,eW,hi⟩

theorem chosen_thompson_images_of_source_proper
    (T : Sylow 2 G) {M Mc V : Subgroup G} [IsElementaryAbelian 2 V]
    (hTM : (T : Subgroup G) ≤ M) (hn : M ≤ normalizer (V : Set G))
    (U : Submodule (ZMod 2) (Additive V))
    (h : SourceCases.Proper T M Mc V (imageRepresentation M V hn) U)
    [IsElementaryAbelian 2 ((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype)]
    (hnW : M ≤ normalizer (((Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype) : Set G))
    (hm : ⁅(Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype,
      ChapterB.thompsonJ (T : Subgroup G) 1⁆ ≠ ⊥) :
    let W := (Subgroup.toAddSubgroup.symm U.toAddSubgroup).map V.subtype
    (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M W hnW).rangeRestrict =
        ((T : Subgroup G).subgroupOf M).map (actionHom M W hnW).rangeRestrict ⊓
          Jhat (imageRepresentation M W hnW) ∧
      ((ChapterB.thompsonJ M 1).subgroupOf M).map (actionHom M W hnW).rangeRestrict =
        Jhat (imageRepresentation M W hnW)) ∨
    Nat.card (((ChapterB.thompsonJ (T : Subgroup G) 1).subgroupOf M).map
      (actionHom M W hnW).rangeRestrict) = 2 :=
  chosen_thompson_images_of_source_omega T hTM hnW hm (h.chosen_omega T M Mc V hn U hnW)
end CFSG.Quasithin.Chapter15.Section01
