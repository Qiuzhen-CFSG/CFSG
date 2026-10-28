module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductSeed
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.Complete
public import Stellmacher.CentralizerQuotientThompson
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The faithful terminal module on the literal two-core quotient

Conjugation on U descends through the original Y → Y/O₂(Y). The specified
centralizer equality makes it faithful, and the full Thompson image supplies
all of the offender-generation hypothesis of B.5.3. The SQTK cover is the
actual Y, embedded in the selected involution centralizer. Consequently the
complete adequate B.5 classifier applies with no new source premise.
Source: Aschbacher--Smith, completion of 12.3.1, printed p.812.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
variable {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

instance moduleSubgroup_normal : (P.U.subgroupOf P.Y).Normal := P.U_reduced.normal
instance moduleSubgroup_elementary : IsElementaryAbelian 2 (P.U.subgroupOf P.Y) :=
  P.U_reduced.elementary

/-- The kernel identity inside the actual local group, before any model transport. -/
theorem module_centralizer_eq (A : P.ProductAnalysis) :
    centralizer (P.U.subgroupOf P.Y : Set P.Y) = pCore 2 P.Y := by
  have hc : centralizer (P.U.subgroupOf P.Y : Set P.Y) =
      (P.Y ⊓ centralizer (P.U : Set G)).subgroupOf P.Y := by
    ext y
    constructor
    · intro hy
      refine ⟨y.property, ?_⟩
      intro z hz
      exact congrArg Subtype.val (hy ⟨z, P.U_le_Y hz⟩ hz)
    · intro hy z hz
      exact Subtype.ext (hy.2 z hz)
  rw [hc, A.centralizer_eq]
  exact subgroupOf_map_subtype_eq _

/-- The binary conjugation action of the original quotient, on the original U. -/
noncomputable def moduleAction (A : P.ProductAnalysis) :
    Representation (ZMod 2) (P.Y ⧸ pCore 2 P.Y) (Additive (P.U.subgroupOf P.Y)) :=
  NormalElementaryQuotient.representation (P.U.subgroupOf P.Y)
    (QuotientGroup.mk' (pCore 2 P.Y)) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (P.module_centralizer_eq A).symm)

/-- The action retains the ambient conjugation formula on representatives. -/
theorem moduleAction_apply (A : P.ProductAnalysis) (y : P.Y)
    (v : Additive (P.U.subgroupOf P.Y)) :
    (((P.moduleAction A (QuotientGroup.mk' (pCore 2 P.Y) y) v).toMul : P.Y) : G) =
      (y : G) * (v.toMul : P.Y) * (y : G)⁻¹ :=
  congrArg Subtype.val (NormalElementaryQuotient.representation_apply
    (P.U.subgroupOf P.Y) (QuotientGroup.mk' (pCore 2 P.Y))
    (QuotientGroup.mk'_surjective _) _ y v)

theorem moduleAction_faithful (A : P.ProductAnalysis) :
    Function.Injective (P.moduleAction A) :=
  NormalElementaryQuotient.representation_injective _ _ _ _

/-- Undo the model equivalence in the supplied full Thompson image. -/
theorem module_thompson_image (A : P.ProductAnalysis) :
    (Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup P.Y)).map
      (QuotientGroup.mk' (pCore 2 P.Y)) = ⊤ := by
  have hj : Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup P.Y) =
      (Stellmacher.elementaryAbelianMaxJ P.Y).subgroupOf P.Y := by
    apply map_injective P.Y.subtype_injective
    rw [← Stellmacher.elementaryAbelianMaxJ_map_injective P.Y.subtype
      P.Y.subtype_injective, ← MonoidHom.range_eq_map, range_subtype,
      map_subgroupOf_eq_of_le (show Stellmacher.elementaryAbelianMaxJ P.Y ≤ P.Y from sSup_le fun _ h => h.1)]
  apply map_injective (f := A.quotient.toMonoidHom) A.quotient.injective
  rw [map_top_of_surjective _ A.quotient.surjective, hj, map_map]
  exact A.thompson_image

/-- Full ordinary Thompson image generates the full best-offender actor. -/
theorem moduleAction_generated (A : P.ProductAnalysis) :
    offenderSubgroup (P.moduleAction A) = ⊤ := by
  apply top_unique
  rw [← P.module_thompson_image A]
  exact NormalElementaryQuotient.maxJ_image_le_offenderSubgroup
    (P.U.subgroupOf P.Y) (QuotientGroup.mk' (pCore 2 P.Y))
    (QuotientGroup.mk'_surjective _) _ ⊤ le_top

/-- Y itself is the required SQTK cover; no quotient closure of SQTK is assumed. -/
theorem Y_sqtk : IsSQTK KnownSimple.IsKnownSimple P.Y := by
  have ho : orderOf (P.point : G) = 2 :=
    orderOf_eq_prime ((mem_omegaCenterIn_iff _ _).mp P.central).2.2
      (fun h => P.nonidentity (Subtype.ext h))
  have hc := S.hypothesis.simpleQTKE.involution_centralizer_sqtk ho
  have hy := hc.subgroup (P.Y.subgroupOf P.pointCentralizer)
  let e := subgroupOfEquivOfLe P.Y_le_pointCentralizer
  exact (IsSQTK.equiv e).mp hy

/-- All hypotheses of B.5.3 for this literal action. -/
theorem moduleAction_FFHypothesis (A : P.ProductAnalysis) :
    ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple (P.moduleAction A) where
  finite_module := inferInstance
  faithful := P.moduleAction_faithful A
  twoCore := by
    let e := QuotientGroup.quotientMulEquivOfEq (P.module_centralizer_eq A)
    have hm := pCore_map_iso 2 e
    rw [P.U_reduced.quotient_pCore_eq_bot, Subgroup.map_bot] at hm
    exact hm.symm
  generated := P.moduleAction_generated A
  quotient := ⟨{
    Cover := P.Y
    kernel := pCore 2 P.Y
    sqtk := P.Y_sqtk
    equiv := MulEquiv.refl _ }⟩

/-- The completed classifier, applied to the actual terminal source action. -/
theorem moduleAction_alternative (A : P.ProductAnalysis) :
    ChapterB.SourceInduction.NontrivialAdequateAlternative (P.moduleAction A) := by
  let : Nontrivial (P.Y ⧸ pCore 2 P.Y) := A.quotient.symm.injective.nontrivial
  exact ChapterB.SourceInduction.nontrivialAdequateAlternative_knownSimple
    (P.moduleAction A) (P.moduleAction_FFHypothesis A)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
