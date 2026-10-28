module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Borel.ModelOvergroups
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Borel.Reduction
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.Bender.Orbit

/-!
# The Bender join belongs to H-star

The local SQTK theorem gives either a normal component or an exchanged pair
in the centralizer of the diagonal involution. The Bender model calculation
makes every proper overgroup of the original Sylow inside I T solvable.
The survivor puts those overgroups in M. Since I escapes M and the diagonal
involution supplies a nontrivial two-core, I T belongs to H-star in the
original subgroup lattice.

Source: Aschbacher--Smith, the Bender paragraph of 10.3.3, printed p.756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The original Borel-to-H-star input, with no normalization, parabolic,
or Borel-containment premise. -/
theorem borelHStar_source : BorelHStarAt T := by
  apply borelHStar_of_solvable_overgroups
  intro L D s d I hI hb P hTP hP
  let C := centralizer ({d.first * d.second} : Set G)
  let S := T.subtype d.sylow_le_centralizer
  let A := I.subgroupOf C
  have hC : C ∈ Chapter1.H G := Chapter1.mem_H_of_isTwoLocal
    (isTwoLocal_involution_centralizer d.order)
  have hidx := Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (Chapter1.Section02.uniqueness_local_quotient_sqtk D.simpleQTKE hC) hI.2
  let a : A ≃* I := subgroupOfEquivOfLe hI.1
  have hm : ClassificationModels.IsBenderModel (A ⧸ pCore 2 A) :=
    hb.of_mulEquiv (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
  have hYC : I ⊔ (T : Subgroup G) ≤ C := sup_le hI.1 d.sylow_le_centralizer
  have hPC : P ≤ C := hP.le.trans hYC
  have hgen : A ⊔ (S : Subgroup C) = (I ⊔ (T : Subgroup G)).subgroupOf C := by
    exact (subgroupOf_sup hI.1 d.sylow_le_centralizer).symm
  have hSP : (S : Subgroup C) ≤ P.subgroupOf C := subgroupOf_mono C hTP
  have hlt : P.subgroupOf C < A ⊔ (S : Subgroup C) := by
    rw [hgen]
    refine lt_of_le_of_ne (subgroupOf_mono C hP.le) ?_
    intro he
    have hh := congrArg (map C.subtype) he
    rw [map_subgroupOf_eq_of_le hPC, map_subgroupOf_eq_of_le hYC] at hh
    exact hP.ne hh
  let := bender_component_proper_overgroup_solvable S A hI.2 hm
    (hidx.imp_right And.left) (P.subgroupOf C) hSP hlt
  exact Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hPC).symm.toMonoidHom)
    (subgroupOfEquivOfLe hPC).symm.injective

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Bender
