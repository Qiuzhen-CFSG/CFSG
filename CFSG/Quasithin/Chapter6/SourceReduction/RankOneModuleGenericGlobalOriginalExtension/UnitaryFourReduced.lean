module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourTransport
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.TwoResidual
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourPlacement

/-!
# The native U₄ comparison inside a broad original extension

The native point and plane endpoints have trivial two-group quotients.
Together with the original common Sylow and endpoint generation, this
identifies their inner images with O² of the original endpoints. Restricting
the supplied maps constructs the ordinary U₄ amalgam on the literal reduced
source S₀=T∩L, retaining the whole reduced Borel and both inclusion squares.
The solvable residuals remain the same selected L and R.

The native involution-placement theorem therefore applies to the actual
original factors before any bound on the outer extension. This does not
identify the full original amalgam: bounding its remaining outer action by
the specified degree-two action remains necessary, as do DGS exhaustiveness,
uniqueness and unconditional GlobalExit assembly. No equality S=T or
R=O²(H), pure comparison or desired core equality is assumed.

Source: Aschbacher--Smith F.1.12, pp.263--264, 5.2.6--7, pp.650--651,
and the local placement in F.4.35, p.292 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global

namespace OriginalUnitaryFour
open ChapterF.GreenBook.LieModels.UnitaryFour
private theorem twoResidual_eq_top_of_perfect_sylow
    {X : Type*} [Group X] [Finite X] (P K : Subgroup X) [Group.IsPerfect K]
    (hKP : K ≤ P)
    (hU : ∀ U : Subgroup P, IsPGroup 2 U → U.map P.subtype ≤ K) :
    pResidual 2 P = ⊤ := by
  have hk : IsPPerfect 2 K := by
    intro N hN hq
    let : N.Normal := hN
    by_contra hne
    let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    let : Group.IsPerfect (K ⧸ N) := Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
    let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
    exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance
  let U : Sylow 2 P := Classical.choice inferInstance
  have hp : IsPPerfect 2 (K.subgroupOf P) := hk.of_surjective
    (subgroupOfEquivOfLe hKP).symm.toMonoidHom (subgroupOfEquivOfLe hKP).symm.surjective
  have hu : (U : Subgroup P) ≤ pResidual 2 P :=
    ((map_le_iff_le_comap).mp (hU U U.isPGroup')).trans (le_pResidual_of_isPPerfect _ hp)
  simpa only [sup_of_le_left hu] using pResidual_sup_sylow_eq_top U

private theorem endpoint_twoResidual (m : ℕ) (hm : 1 ≤ m) (hmgt : 1 < m) (point : Bool) :
    pResidual 2 (endpoint m hm point) = ⊤ := by
  cases point
  · let := L2_isPerfect m hm
    exact twoResidual_eq_top_of_perfect_sylow _ (L2 m hm) (L2_le_planeParabolic m hm)
      (fun U hU => two_subgroup_le_L2 m hm _ (hU.map _) (map_subtype_le _))
  · let := PointLocal.projectiveLocal_isPerfect m hm hmgt
    exact twoResidual_eq_top_of_perfect_sylow _ (PointLocal.ProjectiveLocal m hm)
      (PointLocal.projectiveLocal_le_pointParabolic m hm)
      (fun U hU => PointLocal.twoSubgroup_le_projectiveLocal m hm _ (hU.map _) (map_subtype_le _))
end OriginalUnitaryFour


namespace OriginalUnitaryFour
open ChapterF.GreenBook.LieModels.UnitaryFour
/-- The native intersection amalgam in the given original orientation. -/
@[expose] def nativeAmalgam (m : ℕ) (hm : 1 ≤ m) (point : Bool) :=
  RankTwoAmalgam.ofSubgroups (endpoint m hm point)
    (endpoint m hm point ⊓ endpoint m hm (!point)) (endpoint m hm (!point))
    inf_le_left inf_le_right

private def intersectionIso (m : ℕ) (hm : 1 ≤ m) :
    RankTwoAmalgam.Iso (nativeAmalgam m hm true) (amalgam m hm) where
  left := MulEquiv.refl _
  right := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr (exact_overlap m hm)
  left_commutes _ := rfl
  right_commutes _ := rfl

private def intersectionIsoReverse (m : ℕ) (hm : 1 ≤ m) :
    RankTwoAmalgam.Iso (nativeAmalgam m hm false) (amalgam m hm).reverse where
  left := MulEquiv.refl _
  right := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr ((inf_comm _ _).trans (exact_overlap m hm))
  left_commutes _ := rfl
  right_commutes _ := rfl
end OriginalUnitaryFour

namespace Preparation
open ChapterF.GreenBook.LieModels.UnitaryFour
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (e : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))

include d h hTH hp e in
theorem originalUnitaryFour_reduced_le (i : Fin 2) :
    ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i ≤
      ChapterF.Source.parabolic ![L,R] (sourceS L H) i := by
  rw [d.original_unitaryFour_reduced_parabolics h hTH hp m hm point e i]
  exact map_subtype_le _

include d h hTH hp e in
/-- Both two-residual endpoints have exactly their native inner images. -/
theorem original_unitaryFour_reduced_images :
    (e.left.comp (inclusion (d.originalUnitaryFour_reduced_le h hTH hp m hm point e 0))).range =
      (OriginalUnitaryFour.endpoint m hm point).map MulAut.conj ∧
    (e.right.comp (inclusion (d.originalUnitaryFour_reduced_le h hTH hp m hm point e 1))).range =
      (OriginalUnitaryFour.endpoint m hm (!point)).map MulAut.conj := by
  have hs := d.original_unitaryFour_intersections h hTH hp m hm point e
  have hmgt := d.original_unitaryFour_nonbinary h hTH hp m hm point e
  have he := d.original_twoResidual_images h hTH hp e hs
    (OriginalUnitaryFour.endpoint_twoResidual m hm hmgt point)
    (OriginalUnitaryFour.endpoint_twoResidual m hm hmgt (!point))
  have hr (i : Fin 2) : (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i).subgroupOf
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) i) =
      pResidual 2 (ChapterF.Source.parabolic ![L,R] (sourceS L H) i) := by
    rw [d.original_unitaryFour_reduced_parabolics h hTH hp m hm point e i]
    exact comap_map_eq_self_of_injective
      (ChapterF.Source.parabolic ![L,R] (sourceS L H) i).subtype_injective _
  simpa only [MonoidHom.range_comp,inclusion_range,hr] using he

/-- Restrict the original marking to O² of both endpoints. The full
restricted odd overlap and both inclusion squares are preserved. -/
def originalUnitaryFourReducedComparison : RankTwoAmalgam.Iso
    (sourceParabolicAmalgam ![L,R] ((T : Subgroup G) ⊓ L))
    (OriginalUnitaryFour.nativeAmalgam m hm point) :=
  e.restrictTo (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm)
    _ _ (d.originalUnitaryFour_reduced_le h hTH hp m hm point e 0)
    (d.originalUnitaryFour_reduced_le h hTH hp m hm point e 1)
    (d.original_unitaryFour_reduced_images h hTH hp m hm point e).1
    (d.original_unitaryFour_reduced_images h hTH hp m hm point e).2

theorem originalUnitaryFourReducedComparison_left_apply
    (x : ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0) :
    MulAut.conj ((d.originalUnitaryFourReducedComparison h hTH hp m hm point e).left x).val =
      e.left (inclusion (d.originalUnitaryFour_reduced_le h hTH hp m hm point e 0) x) :=
  e.restrictTo_left_apply _ _ _ _ _ _ _ x

theorem originalUnitaryFourReducedComparison_right_apply
    (x : ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1) :
    MulAut.conj ((d.originalUnitaryFourReducedComparison h hTH hp m hm point e).right x).val =
      e.right (inclusion (d.originalUnitaryFour_reduced_le h hTH hp m hm point e 1) x) :=
  e.restrictTo_right_apply _ _ _ _ _ _ _ x

theorem originalUnitaryFourReducedComparison_middle_apply
    (x : (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1 : Subgroup G)) :
    MulAut.conj ((d.originalUnitaryFourReducedComparison h hTH hp m hm point e).middle x).val =
      e.left ⟨x.val,d.originalUnitaryFour_reduced_le h hTH hp m hm point e 0 x.property.1⟩ :=
  e.restrictTo_middle_apply _ _ _ _ _ _ _ x

include d h hTH hp e in
/-- The broad original U₄ extension gives an ordinary comparison on its
literal two-residuals; it does not erase the original outer two-group. -/
theorem original_unitaryFour_reduced_amalgam :
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] ((T : Subgroup G) ⊓ L)) (amalgam m hm)) ∨
    Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,R] ((T : Subgroup G) ⊓ L)) (amalgam m hm).reverse) := by
  have f := d.originalUnitaryFourReducedComparison h hTH hp m hm point e
  cases point
  · exact Or.inr ⟨f.trans (OriginalUnitaryFour.intersectionIsoReverse m hm)⟩
  · exact Or.inl ⟨f.trans (OriginalUnitaryFour.intersectionIso m hm)⟩

include d h hTH hp e in
/-- Restriction to the two-residual endpoints keeps exactly the same
original selected factors as solvable residuals. -/
theorem original_unitaryFour_reduced_residuals (i : Fin 2) :
    (solvableResidual (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i)).map
      (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) i).subtype = ![L,R] i := by
  apply le_antisymm ((map_solvableResidual_mono
    (d.originalUnitaryFour_reduced_le h hTH hp m hm point e i)).trans_eq
      (d.parabolic_residuals h hTH hp i))
  have hpi : Group.IsPerfect (![L,R] i) := by
    fin_cases i
    · exact Chapter1.mem_L_isPerfect h.local_mem.1.1
    · exact hp
  let := hpi
  exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans le_sup_left)

include d h hTH hp e in
/-- The genuine native placement theorem now applies to the original
selected factors without assuming a pure original amalgam comparison. -/
theorem original_unitaryFour_involution_placement
    (x : G) (hx : x ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1) (hx2 : x^2=1) :
    (∃ g ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 0,
      g*x*g⁻¹ ∈ R.pCoreIn 2) ∨
    (∃ g ∈ ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L) 1,
      g*x*g⁻¹ ∈ L.pCoreIn 2) := by
  exact ChapterF.UnitarySource.FourPlacement.comparison_involution_to_residual_core m hm
    (ChapterF.Source.parabolic ![L,R] ((T : Subgroup G) ⊓ L)) ![L,R]
    (d.original_unitaryFour_reduced_residuals h hTH hp m hm point e)
    (d.original_unitaryFour_reduced_amalgam h hTH hp m hm point e) x hx hx2
end Preparation
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
