module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFiveTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFiveKernel
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Removing the original marked U₅ extension

For an arbitrary selected perfect R, the original normalized right Borel
transports to the full native line Borel. Its displacements lie in the exact
inner part of the source S image. The native coefficient and odd-scalar
calculation then makes every element of S inner, and the already established
inner preimage identifies S as a subgroup of both selected factors.

Thus adjoining S changes neither local two-core. Full-overlap agreement and
source endpoint generation make both whole endpoint images inner. Restricting
the same three maps gives the reversed U₅(4) comparison, with both inclusion
squares and every odd overlap element retained. The quasithin obstruction and
faithful left quotient filter arbitrary U₅ fields and both orientations before
this reduction; neither S=T nor R=O²(H) is a premise.

Broad original marking construction and exhaustiveness remain with DGS source
assembly. The Chapter12 extension applies the comparison to residual preparation
and reuses the completed prepared U₅ source for GlobalExit.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace Preparation
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (M : Model 4) (e : OriginalUnitaryFive.Marking M false L R (sourceS L H))

/-- The source S action in the ordinary native line--plane orientation. -/
def originalUnitaryFiveFlagHom : sourceS L H →* ChapterF.UnitaryFiveFlagAutomorphisms.flagAutomorphisms M :=
  e.sylowHom.codRestrict _ (fun s =>
    let a := e.sylowFlagHom (Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
      M.form M.local_field_card M.conjugation M.matrix) s
    ⟨a.property.2,a.property.1⟩)

include d h hTH hp M e in
/-- The normalized original right Borel gives literal native displacements,
without identifying S with its inner intersection. -/
theorem original_unitaryFive_borel_displacements (s : sourceS L H)
    (x : M.Carrier) (hx : x ∈ M.leftLocalImage ⊓ M.overlap) :
    x⁻¹ * e.sylowHom s x ∈ M.flagTwoSubgroup := by
  have hi := Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
    M.form M.local_field_card M.conjugation M.matrix
  have hnU : M.overlap ≤ normalizer (M.flagTwoSubgroup : Set M.Carrier) :=
    (normal_subgroupOf_iff_le_normalizer M.flagTwoSubgroup_le_overlap).mp
      M.flagTwoSubgroup_normal_in_overlap
  have hn := d.original_unitaryFive_borel_normalizes h hTH hp M e
    (mem_map_of_mem MulAut.conj (show x ∈ M.leftLocalImage ⊓ normalizer (M.flagTwoSubgroup : Set M.Carrier)
      from ⟨hx.1,hnU hx.2⟩))
  have ha : e.sylowHom s ∈ e.sylowHom.range := ⟨s,rfl⟩
  have hc : (MulAut.conj x)⁻¹ * e.sylowHom s * MulAut.conj x * (e.sylowHom s)⁻¹ ∈
      e.sylowHom.range := (e.sylowHom.range).mul_mem
    ((mem_normalizer_iff''.mp hn (e.sylowHom s)).mp ha)
    ((e.sylowHom.range).inv_mem ha)
  have he : MulAut.conj (x⁻¹ * e.sylowHom s x) =
      (MulAut.conj x)⁻¹ * e.sylowHom s * MulAut.conj x * (e.sylowHom s)⁻¹ := by
    apply MulEquiv.ext
    intro y
    change (x⁻¹ * e.sylowHom s x) * y * (x⁻¹ * e.sylowHom s x)⁻¹ =
      x⁻¹ * e.sylowHom s (x * (e.sylowHom s).symm y * x⁻¹) * x
    simp only [map_mul,map_inv,MulEquiv.apply_symm_apply]
    group
  rw [←he] at hc
  apply (mem_map_iff_mem hi).mp
  rw [←d.original_unitaryFive_source_inner h hTH hp M e]
  exact ⟨hc,⟨_,rfl⟩⟩

include d h hTH hp M e in
/-- Every original S element has trivial field coefficient on the actual
plane PSL₂(16) quotient, forced by the opposite normalized line Borel. -/
theorem original_unitaryFive_coefficient (s : sourceS L H) :
    ChapterF.UnitaryFiveFlagAutomorphisms.rightCoefficient M
      (originalUnitaryFiveFlagHom M e s) = 1 := by
  obtain ⟨k,hk⟩ := (d.hypothesisF11 h hTH).S_isP.exists_pow_pow_eq_one s
  apply OriginalUnitaryFive.coefficient_eq_one_of_line_borel_displacements M
    (originalUnitaryFiveFlagHom M e s) k
    (by rw [←map_pow,hk,map_one])
  exact d.original_unitaryFive_borel_displacements h hTH hp M e s

include d h hTH hp M e in
/-- The original U₅ normalized-Borel marking forces the entire S inside
both selected factors, prior to any whole-residual identification. -/
theorem original_unitaryFive_sourceS_le : sourceS L H ≤ R ∧ sourceS L H ≤ L := by
  have hi (s : sourceS L H) : e.sylowHom s ∈ MulAut.innerSubgroup M.Carrier := by
    obtain ⟨k,hk⟩ := (d.hypothesisF11 h hTH).S_isP.exists_pow_pow_eq_one s
    exact OriginalUnitaryFive.inner_of_twoPower_coefficient_eq_one M
      (originalUnitaryFiveFlagHom M e s) k (by rw [←map_pow,hk,map_one])
      (d.original_unitaryFive_coefficient h hTH hp M e s)
  constructor
  · intro x hx
    exact ((d.original_unitaryFive_inner_iff h hTH hp M e ⟨x,hx⟩).1).mp (hi ⟨x,hx⟩)
  · intro x hx
    exact ((d.original_unitaryFive_inner_iff h hTH hp M e ⟨x,hx⟩).2).mp
      (((d.original_unitaryFive_inner_iff h hTH hp M e ⟨x,hx⟩).1).mp (hi ⟨x,hx⟩))

include d h hTH hp M e in
/-- Both original full endpoints are native inner endpoints. -/
theorem original_unitaryFive_endpoints_inner :
    e.left.range ≤ MulAut.innerSubgroup M.Carrier ∧
    e.right.range ≤ MulAut.innerSubgroup M.Carrier :=
  d.original_extension_endpoints_inner h hTH hp e
    (d.original_unitaryFive_sourceS_le h hTH hp M e).1

include d h hTH hp M e in
/-- Adjoining the actual original source S changes neither local two-core. -/
theorem original_unitaryFive_core_eq :
    (R ⊔ sourceS L H).pCoreIn 2 = R.pCoreIn 2 ∧
    (L ⊔ sourceS L H).pCoreIn 2 = L.pCoreIn 2 := by
  have hs := d.original_unitaryFive_sourceS_le h hTH hp M e
  rw [sup_eq_left.mpr hs.1,sup_eq_left.mpr hs.2]
  exact ⟨rfl,rfl⟩
end Preparation
namespace OriginalUnitaryFive
open ChapterF.GreenBook.UnitaryFive
private def intersectionIso (M : Model 4) :
    RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups M.rightParabolic (M.rightParabolic ⊓ M.leftParabolic)
        M.leftParabolic inf_le_left inf_le_right) M.amalgam.reverse :=
  { left := MulEquiv.refl _
    right := MulEquiv.refl _
    middle := MulEquiv.subgroupCongr (inf_comm _ _)
    left_commutes := fun _ => Subtype.ext rfl
    right_commutes := fun _ => Subtype.ext rfl }
end OriginalUnitaryFive

namespace Preparation
open ChapterF.GreenBook.UnitaryFive
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (M : Model 4) (e : OriginalUnitaryFive.Marking M false L R (sourceS L H))

/-- Restrict the same original endpoint and whole-overlap markings to the
native reversed U₅ amalgam, preserving both inclusion squares. -/
def originalUnitaryFiveComparison : RankTwoAmalgam.Iso
    (sourceParabolicAmalgam ![L,R] (sourceS L H)) M.amalgam.reverse :=
  (e.restrict (Theory.SpecificGroups.UnitaryFive.SmallCompletion.conj_injective
    M.form M.local_field_card M.conjugation M.matrix)
    (d.original_unitaryFive_endpoints_inner h hTH hp M e)).trans
      (OriginalUnitaryFive.intersectionIso M)

/-- The restricted left map is exactly the supplied original left map. -/
theorem originalUnitaryFiveComparison_left_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    MulAut.conj ((d.originalUnitaryFiveComparison h hTH hp M e).left x).val = e.left x :=
  e.restrict_left_apply _ _ x

/-- The restricted right map is exactly the supplied original right map. -/
theorem originalUnitaryFiveComparison_right_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    MulAut.conj ((d.originalUnitaryFiveComparison h hTH hp M e).right x).val = e.right x :=
  e.restrict_right_apply _ _ x

/-- The entire original odd overlap is retained by the comparison. -/
theorem originalUnitaryFiveComparison_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G)) :
    MulAut.conj ((d.originalUnitaryFiveComparison h hTH hp M e).middle x).val =
      e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) :=
  e.restrict_middle_apply _ _ x

omit M e in
include d h hTH hp in
/-- Every original U₅ field and orientation is filtered and collapsed into
the concrete catalogue, for the same arbitrary selected perfect R. -/
theorem concreteComparison_of_original_unitaryFive
    {q : ℕ} (hq : IsPrimePow q) (heven : Even q) (M : Model q) (line : Bool)
    (hi : Function.Injective (MulAut.conj : M.Carrier →* MulAut M.Carrier))
    (e : OriginalUnitaryFive.Marking M line L R (sourceS L H)) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  have hq4 := Preparation.original_unitaryFive_marked_field h hq heven M line hi e
  subst q
  have ho := d.original_unitaryFive_marked_orientation h hTH hp M line e
  subst line
  exact .unitaryFive M (Or.inr ⟨d.originalUnitaryFiveComparison h hTH hp M e⟩)
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
