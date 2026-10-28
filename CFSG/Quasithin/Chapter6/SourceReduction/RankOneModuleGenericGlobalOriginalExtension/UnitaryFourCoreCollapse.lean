module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOriginalExtension.UnitaryFourLeftCore
public import Theory.GroupAction.PerfectCentralQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalRecognitionCatalogue

/-!
# Removing the original U₄ residual centralizer

The right two-core lies in the common inner Sylow and hence in L. Its
centralizer inside the selected perfect R is central in R. Thus an
S-element centralizing L fixes that core, and perfectness kills its central
automorphism displacement on R. The remaining C_S(L) centralizes both
factors and is normal in their join with S. The original zero two-core
hypothesis therefore makes C_S(L) trivial.

Consequently O₂(LS)=O₂(L), and the full original outer Sylow index is one
or two. In the index-one branch, restriction of the original marking gives
both full endpoints and the entire overlap of the ordinary U₄ amalgam,
with both inclusion squares. All statements retain arbitrary selected
perfect R, either input orientation, and q=4; neither S=T nor R=O²(H)
is assumed. The companion Chapter 12 module applies the ordinary branch
to the completed prepared recognition and restores broad markings from the
literal reduced DGS input.

The degree-two branch still requires identification of its action with
the specified graph extension. DGS exhaustion, uniqueness and final
unconditional GlobalExit remain with the source assembly.
Source: Aschbacher--Smith F.1.12, pp.263--264; 5.2.6--7, pp.650--651
(`refs/quasithin.pdf`). The argument uses the proved point-core center
and Hermitian H¹ calculations from the adjacent modules.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation

private theorem aut_eq_one_of_fixed_normal
    {X : Type*} [Group X] [Group.IsPerfect X]
    (Q : Subgroup X) [Q.Normal]
    (hc : centralizer (Q : Set X) ≤ center X)
    (a : MulAut X) (ha : ∀ x ∈ Q, a x=x) : a=1 := by
  apply MulAut.eq_one_of_central_displacement
  intro g
  apply hc
  intro x hx
  have he := ha (g*x*g⁻¹) ((inferInstance : Q.Normal).conj_mem x hx g)
  rw [map_mul,map_mul,map_inv,ha x hx] at he
  have hh := congrArg (fun y : X => g⁻¹*y*a g) he
  group at hh
  simpa only [mul_assoc,zpow_neg_one] using hh.symm

variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L W H A B R : Subgroup G} {n : ℕ}
  (d : Preparation T L H A B R) (h : Input κ T L W n)
  (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect R)
  (m : ℕ) (hm : 1 ≤ m) (point : Bool)
  (mark : OriginalUnitaryFour.Marking m hm point L R (sourceS L H))
include d h hTH hp mark

/-- The selected right core is contained in the original left factor. -/
theorem original_unitaryFour_right_core_le_left : R.pCoreIn 2 ≤ L := by
  obtain ⟨P,hP⟩ := d.sylow 1
  have hs : R.pCoreIn 2 ≤ sourceS L H ⊓ R := (pCoreIn_le_sylow R P).trans_eq hP
  rw [←d.original_unitaryFour_intersections h hTH hp m hm point mark] at hs
  exact hs.trans inf_le_right

/-- The right core detects every automorphism of the selected perfect R. -/
theorem original_unitaryFour_right_core_action_faithful :
    Function.Injective (MulAut.characteristic (pCore 2 R)) := by
  let := hp
  apply (MulAut.characteristic (pCore 2 R)).ker_eq_bot_iff.mp
  apply le_bot_iff.mp
  intro a ha
  refine aut_eq_one_of_fixed_normal (pCore 2 R) ?_ a ?_
  · intro x hx
    have hxQ := (d.hypothesisF11 h hTH).local_core_selfCentralizing 1 hx
    apply d.original_unitaryFour_core_center_central h hTH hp m hm point mark
    refine ⟨⟨x,hxQ⟩,mem_center_iff.mpr ?_,rfl⟩
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx y.val y.property)
  · intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun ha (⟨x,hx⟩ : pCore 2 R))

/-- Centralizing L forces an original S-element to centralize the whole R. -/
theorem original_unitaryFour_residual_centralizer_right :
    sourceS L H ⊓ centralizer (L : Set G) ≤ centralizer (R : Set G) := by
  rintro s ⟨hs,hc⟩
  let a := R.normalizerMonoidHom ⟨s,d.S_normalizes_right hs⟩
  have he : a=1 := d.original_unitaryFour_right_core_action_faithful h hTH hp m hm point mark (by
    rw [map_one]
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    apply Subtype.ext
    change (a x.val).val=x.val.val
    rw [normalizerMonoidHom_apply_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr ((mem_centralizer_iff.mp hc x.val.val
      (d.original_unitaryFour_right_core_le_left h hTH hp m hm point mark
        (mem_map_of_mem R.subtype x.property))).symm))
  intro x hx
  have hh := congrArg Subtype.val (DFunLike.congr_fun he (⟨x,hx⟩ : R))
  change (a ⟨x,hx⟩).val=x at hh
  rw [normalizerMonoidHom_apply_apply_coe] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

/-- The remaining residual centralizer vanishes in the original generated group. -/
theorem original_unitaryFour_residual_centralizer_eq_bot :
    sourceS L H ⊓ centralizer (L : Set G) = ⊥ := by
  let C := sourceS L H ⊓ centralizer (L : Set G)
  have hLC : L ≤ centralizer (C : Set G) := le_centralizer_iff.mp inf_le_right
  have hRC : R ≤ centralizer (C : Set G) := le_centralizer_iff.mp
    (d.original_unitaryFour_residual_centralizer_right h hTH hp m hm point mark)
  have hSL : sourceS L H ≤ normalizer (L : Set G) :=
    (sourceS_le_sylow h.sylow_normalizes hTH).trans h.sylow_normalizes
  have hSC : sourceS L H ≤ normalizer (C : Set G) :=
    (le_inf (sourceS L H).le_normalizer (hSL.trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf
  have hgen : ChapterF.Source.generated ![L,R] (sourceS L H) ≤ normalizer (C : Set G) :=
    sup_le (sup_le (hLC.trans (Subgroup.centralizer_le_normalizer _))
      (hRC.trans (Subgroup.centralizer_le_normalizer _))) hSC
  have hc : C ≤ (ChapterF.Source.generated ![L,R] (sourceS L H)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((d.hypothesisF11 h hTH).S_isP.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) hgen
  change C=⊥
  apply le_bot_iff.mp
  simpa only [pCoreIn,d.generated_twoCore_eq_bot,Subgroup.map_bot] using hc

/-- The left join has exactly the original left two-core. -/
theorem original_unitaryFour_left_core_eq :
    (L ⊔ sourceS L H).pCoreIn 2 = L.pCoreIn 2 := by
  rw [d.original_unitaryFour_left_core_factorization h hTH hp m hm point mark,
    d.original_unitaryFour_residual_centralizer_eq_bot h hTH hp m hm point mark,sup_bot_eq]

/-- The whole original outer Sylow index is one or two. -/
theorem original_unitaryFour_outer_index_one_or_two :
    ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1 ∨
    ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2 := by
  simpa only [d.original_unitaryFour_left_core_eq h hTH hp m hm point mark,
    relIndex_self,mul_one] using
    d.original_unitaryFour_outer_index_alternatives h hTH hp m hm point mark

/-- The enlarged right core has order q⁵ or 2q⁵, including q=4. -/
theorem original_unitaryFour_right_core_card :
    Nat.card ((R ⊔ sourceS L H).pCoreIn 2) = (2^m)^5 ∨
      Nat.card ((R ⊔ sourceS L H).pCoreIn 2) = 2*(2^m)^5 := by
  rw [d.original_unitaryFour_join_core_card h hTH hp m hm point mark]
  rcases d.original_unitaryFour_outer_index_one_or_two h hTH hp m hm point mark with hh | hh
  · exact Or.inl (by rw [hh,mul_one])
  · exact Or.inr (by rw [hh,mul_comm])

/-- The exact original field kernel is now the unchanged inner Sylow. -/
theorem original_unitaryFour_left_field_kernel_exact
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : (L ⧸ pCore 2 L) ≃* Theory.PSL2.Group F) :
    (originalUnitaryFourLeftFieldAction h hTH q).ker = L.subgroupOf (sourceS L H) := by
  rw [original_unitaryFour_left_field_kernel h hTH q,
    d.original_unitaryFour_left_core_eq h hTH hp m hm point mark,
    sup_eq_left.mpr (pCoreIn_le 2 L)]

/-- In the index-one branch the full original S lies in both selected residuals. -/
theorem original_unitaryFour_sourceS_le_of_index_one
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1) :
    sourceS L H ≤ R ∧ sourceS L H ≤ L := by
  have hs : sourceS L H ≤ (T : Subgroup G) ⊓ L := relIndex_eq_one.mp hi
  have hright : (T : Subgroup G) ⊓ L ≤ R := by
    rw [←d.left_intersection,d.original_unitaryFour_intersections h hTH hp m hm point mark]
    exact inf_le_right
  exact ⟨hs.trans hright,hs.trans inf_le_right⟩

open ChapterF.GreenBook.LieModels.UnitaryFour

/-- The actual order of the original S retains precisely the possible outer involution. -/
theorem original_unitaryFour_sourceS_card :
    Nat.card (sourceS L H) = (2^m)^6 ∨ Nat.card (sourceS L H) = 2*(2^m)^6 := by
  let S₀ := (T : Subgroup G) ⊓ L
  have hs : S₀ ≤ sourceS L H := d.left_intersection.symm.le.trans inf_le_left
  have hc := ((S₀.subgroupOf (sourceS L H))).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hs).toEquiv] at hc
  have hcard : Nat.card S₀=(2^m)^6 := by
    dsimp only [S₀]
    rw [←d.left_intersection]
    exact (d.original_unitaryFour_intersections_card h hTH hp m hm point mark).1
  change Nat.card S₀ * S₀.relIndex (sourceS L H) = _ at hc
  rw [hcard] at hc
  rcases d.original_unitaryFour_outer_index_one_or_two h hTH hp m hm point mark with hh | hh
  · exact Or.inl (by simpa only [S₀,hh,mul_one] using hc.symm)
  · exact Or.inr (by simpa only [S₀,hh,mul_comm] using hc.symm)

/-- Both whole endpoint maps become inner in the ordinary branch. -/
theorem original_unitaryFour_endpoints_inner_of_index_one
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1) :
    mark.left.range ≤ MulAut.innerSubgroup (ProjectiveGroup m hm) ∧
      mark.right.range ≤ MulAut.innerSubgroup (ProjectiveGroup m hm) :=
  d.original_extension_endpoints_inner h hTH hp mark
    (d.original_unitaryFour_sourceS_le_of_index_one h hTH hp m hm point mark hi).1

/-- The index-one comparison restricts the original maps on the full Borel. -/
def originalUnitaryFourOrdinaryComparison
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1) :
    RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (OriginalUnitaryFour.nativeAmalgam m hm point) :=
  mark.restrict (ChapterF.SourceCompletion.UnitaryNonbinary.four_conj_injective m hm)
    (d.original_unitaryFour_endpoints_inner_of_index_one h hTH hp m hm point mark hi)

/-- The ordinary left comparison is the original left marking. -/
theorem originalUnitaryFourOrdinaryComparison_left_apply
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1)
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 0) :
    MulAut.conj ((d.originalUnitaryFourOrdinaryComparison h hTH hp m hm point mark hi).left x).val =
      mark.left x := mark.restrict_left_apply _ _ x

/-- The ordinary right comparison is the original right marking. -/
theorem originalUnitaryFourOrdinaryComparison_right_apply
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1)
    (x : ChapterF.Source.parabolic ![L,R] (sourceS L H) 1) :
    MulAut.conj ((d.originalUnitaryFourOrdinaryComparison h hTH hp m hm point mark hi).right x).val =
      mark.right x := mark.restrict_right_apply _ _ x

/-- Every original overlap element, including its odd part, keeps its marking. -/
theorem originalUnitaryFourOrdinaryComparison_middle_apply
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1)
    (x : (ChapterF.Source.parabolic ![L,R] (sourceS L H) 0 ⊓
      ChapterF.Source.parabolic ![L,R] (sourceS L H) 1 : Subgroup G)) :
    MulAut.conj ((d.originalUnitaryFourOrdinaryComparison h hTH hp m hm point mark hi).middle x).val =
      mark.left ((sourceParabolicAmalgam ![L,R] (sourceS L H)).left x) :=
  mark.restrict_middle_apply _ _ x

private def ordinaryIntersectionIso (m : ℕ) (hm : 1 ≤ m) :
    RankTwoAmalgam.Iso (OriginalUnitaryFour.nativeAmalgam m hm false) (amalgam m hm).reverse where
  left := MulEquiv.refl _
  right := MulEquiv.refl _
  middle := MulEquiv.subgroupCongr ((inf_comm _ _).trans (exact_overlap m hm))
  left_commutes _ := rfl
  right_commutes _ := rfl

/-- The genuine ordinary comparison is obtained after proving the original orientation. -/
theorem original_unitaryFour_amalgam_of_index_one
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1) :
    Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (amalgam m hm).reverse) := by
  have ho := d.original_unitaryFour_orientation h hTH hp m hm point mark
  subst point
  exact ⟨(d.originalUnitaryFourOrdinaryComparison h hTH hp m hm false mark hi).trans
    (ordinaryIntersectionIso m hm)⟩

/-- The ordinary full original branch enters the concrete catalogue. -/
theorem concreteComparison_of_original_unitaryFour_index_one
    (hi : ((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=1) :
    ConcreteAmalgamComparison (sourceParabolicAmalgam ![L,R] (sourceS L H)) :=
  .unitary m hm (Or.inr (d.original_unitaryFour_amalgam_of_index_one h hTH hp m hm point mark hi))

/-- The original row is either the full ordinary comparison or has exact
outer degree two. Identifying the latter action with the graph extension remains. -/
theorem original_unitaryFour_comparison_or_degree_two :
    Nonempty (RankTwoAmalgam.Iso (sourceParabolicAmalgam ![L,R] (sourceS L H))
      (amalgam m hm).reverse) ∨
    (((T : Subgroup G) ⊓ L).relIndex (sourceS L H)=2 ∧
      (R.pCoreIn 2).relIndex ((R ⊔ sourceS L H).pCoreIn 2)=2) := by
  rcases d.original_unitaryFour_outer_index_one_or_two h hTH hp m hm point mark with hi | hi
  · exact Or.inl (d.original_unitaryFour_amalgam_of_index_one h hTH hp m hm point mark hi)
  · exact Or.inr ⟨hi,(d.original_unitaryFour_outer_index h hTH hp m hm point mark).symm.trans hi⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.Preparation
