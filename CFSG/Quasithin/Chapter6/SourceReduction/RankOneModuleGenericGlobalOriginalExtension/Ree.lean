module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.InnerSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue
public import Theory.SpecificGroups.ReeF4.SmallCompletion.Native

/-!
# Removing the original Ree extension, for every parameter

Every two-power automorphism of the native Ree carrier is inner, including
full binary Ree. Apply this to the image of the actual source S in the
marked right endpoint. The full-overlap square and source generation then
put both endpoints in the inner image. Restriction through faithful native
conjugation constructs the comparison with both whole-Borel squares and
retains the original three maps, in either orientation.

The PSL₂ left quotient forces the linear-first orientation. Actual endpoint
nonsolvability excludes the binary parameter, and the local comparison gives
2m+1=n with m>0. Native prime-to-two residual containment also proves S≤R
for the SAME selected R. No ambient-Sylow transport, residual-H identity,
simplicity premise or bound on the general Ree parameter is assumed.

The Chapter 12 extension applies this to every original preparation. Broad
marked alternatives and exhaustiveness remain with the shared DGS assembly;
this reduction alone does not assert GlobalExit.
Source: Aschbacher--Smith F.1.12, pp.263--264, and 5.2.6, pp.650--651
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
namespace OriginalRee
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds

/-- The other root node, without fixing the original orientation. -/
@[expose] def other : Side → Side
  | .suzuki => .linear
  | .linear => .suzuki

variable (m : ℕ) (a : Side)

@[expose] def orientedAmalgam : RankTwoAmalgam (parabolic m a)
    (borel m) (parabolic m (other a)) :=
  RankTwoAmalgam.ofSubgroups _ _ _ (borel_le_parabolic m a)
    (borel_le_parabolic m (other a))

variable {G : Type*} [Group G] (L R S : Subgroup G)

/-- The broad original marking in the full automorphism group of the Ree carrier. -/
abbrev Marking := OriginalExtension.Marking L R S
  (localFactor m a) (localFactor m (other a))
  (parabolic m a) (parabolic m (other a))

private theorem inner_injective (m : ℕ) :
    Function.Injective (MulAut.conj : Model m →* MulAut (Model m)) := by
  cases m with
  | zero =>
    exact Theory.GroupTheory.conj_injective_of_center_eq_bot OuterLocal.binary_center_eq_bot
  | succ m => exact SmallCompletion.conj_injective (m+1) (Nat.succ_pos m)

private def intersectionIso : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic m a)
      (parabolic m a ⊓ parabolic m (other a)) (parabolic m (other a))
      inf_le_left inf_le_right) (orientedAmalgam m a) := by
  have he : parabolic m a ⊓ parabolic m (other a) = borel m := by
    cases a
    · exact ChapterF.GreenBook.LieModels.ReeFour.overlap m
    · rw [inf_comm]
      exact ChapterF.GreenBook.LieModels.ReeFour.overlap m
  exact { left := MulEquiv.refl _
          right := MulEquiv.refl _
          middle := MulEquiv.subgroupCongr he
          left_commutes := fun _ => Subtype.ext rfl
          right_commutes := fun _ => Subtype.ext rfl }
end OriginalRee

namespace Preparation
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (a : Side)
  (e : OriginalRee.Marking m a L R (sourceS L H))
include d h hTH hp e

/-- Odd outer degree kills the image of the actual source S, including m=0.
The full original endpoints then have inner image. -/
theorem original_ree_endpoints_inner :
    e.left.range ≤ MulAut.innerSubgroup (Model m) ∧
    e.right.range ≤ MulAut.innerSubgroup (Model m) := by
  apply d.original_extension_endpoints_inner_of_sourceS_inner h hTH hp e
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hU : IsPGroup 2 ((sourceS L H).subgroupOf P) :=
    (pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).comap_subtype
  rintro z ⟨x,hx,rfl⟩
  obtain ⟨k,hk⟩ := (hU.map e.right).exists_pow_pow_eq_one
    (⟨e.right x,mem_map_of_mem e.right hx⟩ : ((sourceS L H).subgroupOf P).map e.right)
  exact OuterLocal.inner_of_twoPower m (e.right x) k (congrArg Subtype.val hk)

/-- Restrict all three original maps, retaining both full-Borel squares. -/
def originalReeComparison : RankTwoAmalgam.Iso
    (sourceParabolicAmalgam ![L,R] (sourceS L H)) (OriginalRee.orientedAmalgam m a) :=
  (e.restrict (OriginalRee.inner_injective m)
    (d.original_ree_endpoints_inner h hTH hp m a e)).trans
      (OriginalRee.intersectionIso m a)

theorem concreteComparison_of_original_ree :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) := by
  apply ConcreteAmalgamComparison.ree m
  have he := d.originalReeComparison h hTH hp m a e
  cases a
  · exact Or.inl ⟨he⟩
  · exact Or.inr ⟨he⟩

/-- The original PSL₂ left quotient forces the linear-first orientation. -/
theorem original_ree_orientation : a = .linear := by
  cases a
  · exact False.elim (d.not_ree_unreversed h hTH hp m
      ⟨d.originalReeComparison h hTH hp m .suzuki e⟩)
  · rfl

/-- The surviving parameter has 2m+1=n, with binary Ree excluded by nonsolvability. -/
theorem original_ree_field : 2*m+1 = n ∧ 0 < m := by
  have ha := d.original_ree_orientation h hTH hp m a e
  subst a
  have hh := d.ree_local_structure h hTH hp m
    (d.originalReeComparison h hTH hp m .linear e)
  exact ⟨hh.1,hh.2.1⟩

theorem originalReeComparison_left_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    MulAut.conj ((d.originalReeComparison h hTH hp m a e).left x).val = e.left x :=
  e.restrict_left_apply _ _ x

theorem originalReeComparison_right_apply
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    MulAut.conj ((d.originalReeComparison h hTH hp m a e).right x).val = e.right x :=
  e.restrict_right_apply _ _ x

theorem originalReeComparison_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G)) :
    MulAut.conj ((d.originalReeComparison h hTH hp m a e).middle x).val =
      e.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) :=
  e.restrict_middle_apply _ _ x
/-- Every original source two-element belongs to the same selected Ree factor. -/
theorem sourceS_le_right_of_original_ree : sourceS L H ≤ R := by
  let P := ChapterF.Source.parabolic ![L,R] (sourceS L H) 1
  have hSP : sourceS L H ≤ P := le_sup_right.trans le_sup_left
  intro x hx
  let y : P := ⟨x,hSP hx⟩
  let c := d.originalReeComparison h hTH hp m a e
  obtain ⟨k,hk⟩ := (pCore_isPGroup.map _ : IsPGroup 2 (sourceS L H)).exists_pow_pow_eq_one
    (⟨x,hx⟩ : sourceS L H)
  have hxpow : x^(2^k)=1 := congrArg (fun z : sourceS L H => z.val) hk
  have hy : y^(2^k)=1 := Subtype.ext hxpow
  have hz : (c.right y).val^(2^k)=1 := by
    rw [←coe_pow,←map_pow,hy,map_one,coe_one]
  have hl := mem_localFactor_of_pow m (OriginalRee.other a) (c.right y).val
    (c.right y).property k hz
  have hh : e.right y ∈ (R.subgroupOf P).map e.right := by
    have he := d.original_local_eq_residual h hTH hp 1
    change R.subgroupOf P = _ at he
    rw [he,e.right_residual,←d.originalReeComparison_right_apply h hTH hp m a e y]
    exact mem_map_of_mem MulAut.conj hl
  exact (mem_map_iff_mem e.right_injective).mp hh

end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
