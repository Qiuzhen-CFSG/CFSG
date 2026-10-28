module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourFactors
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.ResidualAction
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms

/-!
# The original U₄ right-quotient action

The same original S marking preserves both native parabolics. Restrict its
right action to the characteristic residual and its intrinsic two-core
quotient. The original O₂(RS) acts trivially there by the transported core
commutator theorem; T∩L acts by literal inner automorphisms. The proved
normalized-Borel factorization therefore makes every S actor inner on this
quotient. In the canonical point PSL₂(2ᵐ) coordinates its field coefficient
is trivial.

This does not remove the possible graph action on the full U₄ carrier. Its
remaining degree bound and the full original comparison still require the
native kernel calculation. The literal Chapter 12 application uses the same
selected perfect R and original endpoint maps.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
namespace OriginalUnitaryFour
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms
private theorem quotientAction_conj {X : Type*} [Group X] (P Q : Subgroup X)
    (a : Theory.SpecificGroups.ClassicalUnitary.NativeAmalgamActions.flagAutomorphisms P Q)
    (u : rightResidualImage Q) (ha : a.val = MulAut.conj u.val) :
    rightQuotientAction P Q a = MulAut.conj (QuotientGroup.mk' (pCore 2 (rightResidualImage Q)) u) := by
  apply MulEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (rightResidualImage Q)) z
  rw [rightQuotientAction_mk]
  simp only [MulAut.conj_apply]
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg (QuotientGroup.mk' (pCore 2 (rightResidualImage Q)))
  apply Subtype.ext
  rw [rightImageAction_val,ha]
  rfl

/-- The canonical PSL₂ coordinates on the native point residual quotient. -/
def pointQuotient (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m) :
    (rightResidualImage (pointParabolic m hm) ⧸
      pCore 2 (rightResidualImage (pointParabolic m hm))) ≃*
        Theory.PSL2.Group (PointLocal.FixedField m) :=
  let a := MulEquiv.subgroupCongr (PointLocal.pointParabolic_solvableResidual m hm hmgt)
  (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans
    (PointLocal.projectiveQuotientByTwoCoreEquivPSL m hm)

end OriginalUnitaryFour

namespace Preparation
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms

/-- The literal action of the original S on the marked native right quotient. -/
def originalUnitaryFourRightQuotientAction : sourceS L H →*
    MulAut (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point)) ⧸
      pCore 2 (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point)))) :=
  (Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction
    (OriginalUnitaryFour.endpoint m hm point) (OriginalUnitaryFour.endpoint m hm (!point))).comp
      (e.sylowFlagHom (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm))

include d h hTH hp e in
/-- The entire original join-core acts trivially on this native quotient. -/
theorem original_unitaryFour_core_quotient_action
    (g : sourceS L H) (hg : g.val ∈ (R ⊔ sourceS L H).pCoreIn 2) :
    originalUnitaryFourRightQuotientAction m hm point e g = 1 := by
  let P := OriginalUnitaryFour.endpoint m hm point
  let Q := OriginalUnitaryFour.endpoint m hm (!point)
  let hi := ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm
  let a := e.sylowFlagHom hi g
  let act := Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightImageAction P Q a
  apply MulEquiv.ext
  intro z
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point)))) z
  change Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction P Q a
    (QuotientGroup.mk' _ x) = QuotientGroup.mk' _ x
  rw [Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightQuotientAction_mk]
  change QuotientGroup.mk' _ (act x) = QuotientGroup.mk' _ x
  apply div_eq_one.mp
  rw [←map_div]
  apply (QuotientGroup.eq_one_iff (act x / x)).mpr
  apply (mem_map_iff_mem (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point))).subtype_injective).mp
  change (act x).val / x.val ∈ (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point))).pCoreIn 2
  rw [show (act x).val = e.sylowHom g x.val from
    Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveFlagAutomorphisms.rightImageAction_val P Q a x]
  exact d.original_right_core_native_action h hTH hp e hi g hg x

include d h hTH hp e in
/-- Every S actor is inner on the actual right residual quotient. The
normalizing Borel removes its fixed-field coefficient, but leaves the
possible outer action on the whole U₄ carrier intact. -/
theorem original_unitaryFour_right_quotient_inner (s : sourceS L H) :
    originalUnitaryFourRightQuotientAction m hm point e s ∈
      MulAut.innerSubgroup (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point)) ⧸
        pCore 2 (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point)))) := by
  let K := rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point))
  let f := originalUnitaryFourRightQuotientAction m hm point e
  let I := MulAut.innerSubgroup (K ⧸ pCore 2 K)
  let D := (I.comap f).map (sourceS L H).subtype
  have hD : sourceS L H ≤ D := by
    rw [d.original_unitaryFour_source_factorization h hTH hp m hm point e]
    apply sup_le
    · intro g hg
      let gS : sourceS L H := ⟨g,d.original_right_core_le_sourceS h hTH hg⟩
      refine ⟨gS,?_,rfl⟩
      change f gS ∈ I
      rw [show f gS = 1 from d.original_unitaryFour_core_quotient_action h hTH hp m hm point e gS hg]
      exact I.one_mem
    · intro g hg
      have hgS : g ∈ sourceS L H :=
        (d.left_intersection.ge hg).1
      have hgR : g ∈ R :=
        ((d.original_unitaryFour_inner_iff h hTH hp m hm point e ⟨g,hgS⟩).2).mpr hg.2
      let gS : sourceS L H := ⟨g,hgS⟩
      let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
      have hr := d.original_local_eq_residual h hTH hp 1
      change R.subgroupOf P = _ at hr
      have hmem : e.sylowHom gS ∈ K.map MulAut.conj := by
        change e.sylowHom gS ∈ ((solvableResidual (OriginalUnitaryFour.endpoint m hm (!point))).map
          (OriginalUnitaryFour.endpoint m hm (!point)).subtype).map MulAut.conj
        rw [←e.right_residual,←hr]
        exact mem_map_of_mem e.right (show (⟨g,(show R ≤ P from le_sup_left.trans le_sup_left) hgR⟩ : P) ∈ R.subgroupOf P from hgR)
      obtain ⟨u,hu,he⟩ := hmem
      let uK : K := ⟨u,hu⟩
      refine ⟨gS,?_,rfl⟩
      change f gS ∈ I
      refine ⟨QuotientGroup.mk' (pCore 2 K) uK,?_⟩
      exact (OriginalUnitaryFour.quotientAction_conj _ _
        (e.sylowFlagHom (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm) gS)
        uK he.symm).symm

  exact (mem_map_iff_mem (sourceS L H).subtype_injective).mp (hD s.property)

include d h hTH hp e in
/-- Under any actual binary PSL₂ coordinates on the native right quotient,
the same original source action has trivial field coefficient. -/
theorem original_unitaryFour_right_field_trivial
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point)) ⧸
      pCore 2 (rightResidualImage (OriginalUnitaryFour.endpoint m hm (!point)))) ≃* Theory.PSL2.Group F)
    (s : sourceS L H) :
    Theory.PSL2.fieldProjection F ((MulAut.congr q)
      (originalUnitaryFourRightQuotientAction m hm point e s)) = 1 := by
  obtain ⟨x,hx⟩ := d.original_unitaryFour_right_quotient_inner h hTH hp m hm point e s
  rw [←hx,MulAut.congr_conj]
  change MulAut.conj (q x) ∈ (Theory.PSL2.fieldProjection F).ker
  rw [Theory.PSL2.fieldProjection_ker]
  exact ⟨q x,rfl⟩


omit point e in
include d h hTH hp in
/-- The actual canonical point-quotient field coefficient vanishes on every
original S element in the surviving plane-first orientation. -/
theorem original_unitaryFour_point_field_trivial
    (e : OriginalUnitaryFour.Marking m hm false L R (sourceS L H)) (s : sourceS L H) :
    Theory.PSL2.fieldProjection (PointLocal.FixedField m)
      ((MulAut.congr (OriginalUnitaryFour.pointQuotient m hm
        (d.original_unitaryFour_nonbinary h hTH hp m hm false e)))
        (originalUnitaryFourRightQuotientAction m hm false e s)) = 1 :=
  d.original_unitaryFour_right_field_trivial h hTH hp m hm false e _ s

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
