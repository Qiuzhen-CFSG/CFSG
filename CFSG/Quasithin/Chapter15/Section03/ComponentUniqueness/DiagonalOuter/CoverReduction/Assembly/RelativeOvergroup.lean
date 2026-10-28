module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.FixedResidualSource
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry
public import Theory.SpecificGroups.PSL3.OuterSolvable.Coverage

/-!
# The actual overgroup of the selected four-cover

The covering map is transported along the canonical equivalence between the
component and its relative subgroup in I. Actual conjugation descends to the
original marked action, transported by the supplied projective marking. The actual marked-action surjectivity therefore supplies the full standard action.

Source: Aschbacher–Smith 15.3.38, printed pp.1136–1137.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel
open Matrix.PSL3Four Matrix.PSL3Four.ExtendedCentralizer
variable {G : Type*} [Group G] [Finite G]
variable {d : CharacteristicTwo.LocalData G} {I L : Subgroup G}

/-- The selected cover on the literal relative component in I. -/
def LocalResult.relativeFourCover (r : LocalResult d I L) (h : Setup d I L)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) : FourCover (L.subgroupOf I) := by
  let c := r.fourCover h e
  let j := subgroupOfEquivOfLe h.component_le
  have hc : (center L).comap j.toMonoidHom = center (L.subgroupOf I) := by
    ext x
    exact MulEquivClass.apply_mem_center_iff j
  refine {
    toMonoidHom := c.toMonoidHom.comp j.toMonoidHom
    surjective := c.surjective.comp j.surjective
    isPerfect := ?_
    ker_le_center := ?_
    ker_eq_center := ?_
    center_isKleinFour := ?_ }
  · let := c.isPerfect
    exact Group.IsPerfect.ofSurjective (f := j.symm.toMonoidHom) j.symm.surjective
  · rw [← MonoidHom.comap_ker, c.ker_eq_center, hc]
  · rw [← MonoidHom.comap_ker, c.ker_eq_center, hc]
  · let := c.center_isKleinFour
    let z := Subgroup.centerCongr j
    exact ⟨(Nat.card_congr z.toEquiv).trans IsKleinFour.card_four,
      (Monoid.exponent_eq_of_mulEquiv z).trans IsKleinFour.exponent_two⟩

@[simp] theorem LocalResult.relativeFourCover_apply (r : LocalResult d I L)
    (h : Setup d I L) (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL)
    (x : L.subgroupOf I) :
    (r.relativeFourCover h e).toMonoidHom x =
      e (projectiveMap r.marking (subgroupOfEquivOfLe h.component_le x)) := by
  change (r.fourCover h e).toMonoidHom (subgroupOfEquivOfLe h.component_le x) = _
  exact r.fourCover_apply h e _

omit [Finite G] in
/-- The relative overgroup centralizer is exactly the actual central four. -/
theorem LocalResult.relative_centralizer_eq (r : LocalResult d I L) (h : Setup d I L) :
    centralizer (L.subgroupOf I : Set I) = (center (L.subgroupOf I)).map (L.subgroupOf I).subtype := by
  let j := subgroupOfEquivOfLe h.component_le
  ext x
  constructor
  · intro hx
    have hxG : (x : G) ∈ I ⊓ centralizer (L : Set G) := by
      refine ⟨x.property, fun y hy => ?_⟩
      exact congrArg Subtype.val (hx ⟨y, h.component_le hy⟩ hy)
    rw [r.cover.overgroup_centralizer, ← r.cover.center_plane] at hxG
    obtain ⟨z, hz, hzx⟩ := hxG
    refine ⟨j.symm z, (MulEquivClass.apply_mem_center_iff j.symm).mpr hz, ?_⟩
    exact Subtype.ext hzx
  · rintro ⟨z, hz, rfl⟩ y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)

/-- Actual relative conjugation agrees with the original marked action. -/
theorem LocalResult.relative_projectiveAction_eq (s : SourceInputs d)
    (r : LocalResult d I L) (h : Setup d I L)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL) [(L.subgroupOf I).Normal] :
    projectiveAction (L.subgroupOf I) (r.relativeFourCover h e) =
      (MulAut.congr e).toMonoidHom.comp
        ((markedAction r.marking).comp (inclusion (h.normalizes_component s.earlier))) := by
  ext x p
  obtain ⟨y, rfl⟩ := (r.relativeFourCover h e).surjective p
  rw [projectiveAction, MonoidHom.comp_apply, PerfectCentralCovering.Cover.autMap_apply]
  change (r.relativeFourCover h e).toMonoidHom (MulAut.conjNormal x y) =
    e (markedAction r.marking (inclusion (h.normalizes_component s.earlier) x)
      (e.symm ((r.relativeFourCover h e).toMonoidHom y)))
  rw [r.relativeFourCover_apply, r.relativeFourCover_apply, e.symm_apply_apply,
    markedAction_apply]
  rfl

/-- Surjectivity of the literal marked action constructs the complete
overgroup record. The source application discharges this in OvergroupSource. -/
def LocalResult.extendedOvergroupOfSurjective (s : SourceInputs d) (r : LocalResult d I L)
    (h : Setup d I L) (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL)
    (hsurj : Function.Surjective ((markedAction r.marking).comp
      (inclusion (h.normalizes_component s.earlier)))) :
    letI : (L.subgroupOf I).Normal := r.cover.normal
    Overgroup (L.subgroupOf I) := by
  let : (L.subgroupOf I).Normal := r.cover.normal
  refine {
    cover := r.relativeFourCover h e
    centralizer_eq := r.relative_centralizer_eq h
    full_action := ?_ }
  rw [r.relative_projectiveAction_eq s h e,
    Matrix.PSL3.OuterSolvable.standard_eq_top_of_two_power_card Matrix.PSL3Four.F
      (m := 2) (by decide) Matrix.PSL3Four.card_F]
  exact MonoidHom.range_eq_top.mpr
    ((MulAut.congr e).surjective.comp hsurj)

/-- The source overgroup retains its literal relative covering map. -/
@[simp] theorem LocalResult.extendedOvergroupOfSurjective_cover (s : SourceInputs d)
    (r : LocalResult d I L) (h : Setup d I L)
    (e : PSL(3,r.marking.F) ≃* Matrix.PSL3Four.PSL)
    (hsurj : Function.Surjective ((markedAction r.marking).comp
      (inclusion (h.normalizes_component s.earlier)))) :
    letI : (L.subgroupOf I).Normal := r.cover.normal
    (r.extendedOvergroupOfSurjective s h e hsurj).cover = r.relativeFourCover h e := by
  rfl

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
end
