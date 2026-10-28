module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.CoverReduction.Assembly.Inputs
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Planes

/-!
# The natural action kernel after centre identification

The marked outer action embeds S/(S∩L) into the two-part of Out(PSL₃(4)),
so its order is at most four. The natural action of S has order four and
kernel R=C_T(V), containing S∩L. Comparing the two orders proves R=S∩L.
The disjoint odd and even action images then identify the kernel on YS.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1136.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
open LocalCover LocalCover.SourceBorel
variable {G : Type*} [Group G] [Finite G]

/-- The two-part of the marked outer action bounds the actual Sylow index. -/
theorem sylow_card_bound {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) (r : LocalResult d I L) :
    Nat.card d.S ≤ 4 * Nat.card (d.S ⊓ L : Subgroup G) := by
  let : Group.IsPerfect L := h.perfect
  have hSI : d.S ≤ I := le_sup_right.trans h.outside.1.2
  have hIL := h.normalizes_component s.earlier
  let f : d.S →* MulAut.Outer PSL(3,r.marking.F) :=
    (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,r.marking.F))).comp
      ((markedAction r.marking).comp (inclusion (hSI.trans hIL)))
  have hk : f.ker = (d.S ⊓ L : Subgroup G).subgroupOf d.S := by
    ext x
    change QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,r.marking.F))
      (markedAction r.marking ⟨x, hIL (hSI x.property)⟩) = 1 ↔ (x : G) ∈ d.S ⊓ L
    exact (QuotientGroup.eq_one_iff _).trans
      ((markedAction_inner_iff_mem r.marking r.cover.center_core.ge h.component_le hIL
        (r.cover.overgroup_centralizer ▸ r.cover.center_plane ▸ centerImage_le L)
        (hSI x.property)).trans ⟨fun hx => ⟨x.property, hx⟩, And.right⟩)
  have hkcard : Nat.card f.ker = Nat.card (d.S ⊓ L : Subgroup G) := by
    rw [hk]
    exact Nat.card_congr (subgroupOfEquivOfLe (show d.S ⊓ L ≤ d.S from inf_le_left)).toEquiv
  have hp : IsPGroup 2 f.range := (d.T.isPGroup'.to_le (show d.S ≤ d.T from inf_le_left)).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hd : Nat.card f.range ∣ 12 := f.range.card_subgroup_dvd_card.trans
    (Matrix.PSL3Four.OuterThreeStructure.outer_card_dvd_twelve_of_card_four r.marking.card)
  have hfour : Nat.card f.range ∣ 4 := by
    rw [hn] at hd ⊢
    exact ((Nat.Coprime.pow_left n (by decide : Nat.Coprime 2 3)).dvd_mul_right).mp hd
  have hf : Nat.card f.range ≤ 4 := Nat.le_of_dvd (by decide) hfour
  have he := f.ker.card_mul_index
  rw [index_ker, hkcard] at he
  calc
    Nat.card d.S = Nat.card (d.S ⊓ L : Subgroup G) * Nat.card f.range := he.symm
    _ ≤ Nat.card (d.S ⊓ L : Subgroup G) * 4 := Nat.mul_le_mul_left _ hf
    _ = _ := Nat.mul_comm _ _

/-- The source's R and the cover's S_L coincide, by the two order bounds. -/
theorem natural_kernel_T {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) (r : LocalResult d I L) :
    (d.T : Subgroup G) ⊓ centralizer (d.V : Set G) = d.Y.pCoreIn 2 := by
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hRS : d.R ≤ d.S := by
    rw [s.earlier.local_core]
    exact le_inf inf_le_left (inf_le_right.trans ((centralizer_le (d.action.plane_le 1)).trans
      (Subgroup.centralizer_le_normalizer _)))
  let f := d.action.actor.comp (inclusion hSM)
  have hk : f.ker.map d.S.subtype = d.R := by
    rw [RankTwo.natural_restricted_actor_ker, subgroupOf_map_subtype]
    apply le_antisymm
    · exact (le_inf (inf_le_right.trans inf_le_left) inf_le_left).trans s.earlier.local_core.ge
    · exact le_inf (s.earlier.local_core.le.trans inf_le_right) hRS
  have hr : Nat.card f.range = 4 := by
    rw [RankTwo.natural_restricted_actor_range]
    exact d.action.card_image_planeStabilizer d.T d.sylow_le 1
  have he := f.ker.card_mul_index
  rw [index_ker, hr, ← card_map_of_injective d.S.subtype_injective, hk] at he
  have hbound := sylow_card_bound s h r
  have hcard : Nat.card d.R ≤ Nat.card (d.S ⊓ L : Subgroup G) := by
    rw [← he, Nat.mul_comm 4] at hbound
    exact Nat.le_of_mul_le_mul_right hbound (by decide)
  have hQR : d.S ⊓ L ≤ d.R := by
    rw [← r.cover.borel.component_core]
    exact le_sup_right.trans (s.setup I L h).component_cores_le
  have heq : d.R = d.S ⊓ L := (eq_of_le_of_card_ge hQR hcard).symm
  exact s.earlier.local_core.symm.trans (heq.trans r.cover.residual_core.symm)

/-- The odd residual image and the even Sylow image have trivial intersection,
so the pointwise kernel on YS is the same embedded two-core. -/
theorem natural_kernel_YS {d : CharacteristicTwo.LocalData G} (s : SourceInputs d)
    {I L : Subgroup G} (h : Setup d I L) (r : LocalResult d I L) :
    (d.Y ⊔ d.S) ⊓ centralizer (d.V : Set G) = d.Y.pCoreIn 2 := by
  have hTK := natural_kernel_T s h r
  have hYM : d.Y ≤ d.M := Chapter14.SourcePreliminaries.sourceResidual_le _ _
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hMY : d.M ≤ normalizer (d.Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp (residualY_normal _ _)
  have hYK : d.Y ⊓ centralizer (d.V : Set G) = d.Y.pCoreIn 2 := by
    have hh := congrArg (Subgroup.map d.Y.subtype)
      (RankTwo.residualY_centralizer_eq_twoCore d.action s.residual_image r.cover.quotient_card)
    simpa only [subgroupOf_map_subtype, inf_comm, pCoreIn] using hh
  have h3 : IsPGroup 3 (d.action.image d.Y) := IsPGroup.of_card (n := 2)
    (s.residual_image ▸ RankTwo.orthogonal_twoResidual_card)
  have h2 : IsPGroup 2 (d.action.image d.S) := IsPGroup.of_card (n := 2)
    (d.action.card_image_planeStabilizer d.T d.sylow_le 1)
  have hdis := IsPGroup.disjoint_of_ne 3 2 (by decide)
    (d.action.image d.Y) (d.action.image d.S) h3 h2
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    have hp : x ∈ (d.Y : Set G) * (d.S : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left d.Y d.S (hSM.trans hMY)]
      exact hx
    obtain ⟨y, hy, t, ht, rfl⟩ := hp
    let yM : d.M := ⟨y, hYM hy⟩
    let tM : d.M := ⟨t, hSM ht⟩
    have hyim : d.action.actor yM ∈ d.action.image d.Y := ⟨yM, hy, rfl⟩
    have htim : d.action.actor tM ∈ d.action.image d.S := ⟨tM, ht, rfl⟩
    have hz : d.action.actor (yM * tM) = 1 := by
      change yM * tM ∈ d.action.actor.ker
      rw [d.action.ker_actor]
      exact hc
    have hyinv : d.action.actor yM = (d.action.actor tM)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rwa [map_mul] at hz
    have hyzero : d.action.actor yM = 1 := hdis.le_bot
      ⟨hyim, hyinv ▸ (d.action.image d.S).inv_mem htim⟩
    have htzero : d.action.actor tM = 1 := by
      rwa [map_mul, hyzero, one_mul] at hz
    have hyC : y ∈ centralizer (d.V : Set G) := by
      have hm : yM ∈ d.action.actor.ker := hyzero
      rwa [d.action.ker_actor] at hm
    have htC : t ∈ centralizer (d.V : Set G) := by
      have hm : tM ∈ d.action.actor.ker := htzero
      rwa [d.action.ker_actor] at hm
    exact (d.Y.pCoreIn 2).mul_mem (hYK.le ⟨hy, hyC⟩) (hTK.le ⟨ht.1, htC⟩)
  · exact le_inf ((pCoreIn_le 2 d.Y).trans le_sup_left) (hTK.ge.trans inf_le_right)

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.CoverReduction.Assembly
