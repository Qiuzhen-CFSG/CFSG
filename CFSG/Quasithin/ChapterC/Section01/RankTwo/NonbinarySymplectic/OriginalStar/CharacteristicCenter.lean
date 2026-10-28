module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.Intrinsic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.CenterAction


/-!
# Original characteristic action on the full minimum-replacement center

Write T for the minimum replacement and Z for its full center, embedded in
R. Both Z and C_R(Z) are characteristic in the original radical. In the
field-sized distance-two branch, the previously proved equality C_M(Z)=T
identifies the restriction of this original action kernel to the literal
replacement overgroup M. Thus the original R intersect M acts on this same
Z with image of order q squared.

For the selected original source star, marked preservation puts R intersect
M inside the star. Its image on Z is therefore a two-group of order divisible
by q squared. Characteristicity of the star proves that every automorphism
of the ORIGINAL R normalizes this image on Z. The construction keeps the
whole center, including all component-fixed attachments; no automorphism of
T is extended to R.

This supplies an intrinsic original-radical actor for the remaining
characteristic and exchanged-kernel comparison. It does not identify the
star's entire action with the action of R intersect M, or assert preservation
of the minimum replacement's marked image.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the original star in (3.4), pp.868--869, and the radical/kernel
comparison in (3.7), pp.872--875. The minimum cut is the separate Section 7
construction, pp.932--933; its definition alone does not transfer saturation
or critical distance.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar

private theorem conjugation_kernel {G : Type*} [Group G]
    (Z : Subgroup G) [Z.Normal] :
    (MulAut.conjNormal (H := Z)).ker = centralizer (Z : Set G) := by
  ext x
  constructor
  · intro hx z hz
    have he := congrArg Subtype.val (DFunLike.congr_fun hx (⟨z,hz⟩ : Z))
    change x*z*x⁻¹=z at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hx
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change x*(z:G)*x⁻¹=(z:G)
    rw [←hx z z.property,mul_assoc,mul_inv_cancel,mul_one]

private theorem characteristic_conjugation_normalized {G : Type*} [Group G]
    (Z T : Subgroup G) [Z.Characteristic] [T.Characteristic] :
    (MulAut.characteristic Z).range ≤ normalizer
      (T.map (MulAut.conjNormal (H := Z)) : Set (MulAut Z)) := by
  rintro _ ⟨a,rfl⟩
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he : (MulAut.conj ((MulAut.characteristic Z) a)).toMonoidHom.comp
      (MulAut.conjNormal (H := Z)) =
        (MulAut.conjNormal (H := Z)).comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change a (x * a.symm (z:G) * x⁻¹) = a x * (z:G) * (a x)⁻¹
    rw [map_mul,map_mul,map_inv,a.apply_symm_apply]
  rw [map_map]
  change T.map ((MulAut.conj ((MulAut.characteristic Z) a)).toMonoidHom.comp
    (MulAut.conjNormal (H := Z))) = _
  rw [he,←map_map,characteristic_iff_map_eq.mp inferInstance a]

variable {H F : Type*} [Group H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

/-- The full center of the minimum replacement, inside the ORIGINAL R. -/
@[expose] def minimumCenter : Subgroup R :=
  d.subgroup ⊓ centralizer (d.subgroup : Set R)

/-- Characteristicity is inherited through the actual minimum subgroup. -/
instance minimumCenter_characteristic : (minimumCenter d).Characteristic := by
  let := d.characteristic
  dsimp only [minimumCenter]
  infer_instance

/-- Conjugation by the full original radical on the full replacement center. -/
@[expose] def minimumCenterAction : R →* MulAut (minimumCenter d) := MulAut.conjNormal

/-- The action uses literal conjugation in R. -/
theorem minimumCenterAction_apply (r : R) (z : minimumCenter d) :
    (minimumCenterAction d r z : R) = r * (z:R) * r⁻¹ := rfl

/-- Its kernel is the full relative centralizer in the original radical. -/
theorem minimumCenterAction_kernel :
    (minimumCenterAction d).ker = centralizer (minimumCenter d : Set R) :=
  conjugation_kernel _

/-- This kernel is preserved by every automorphism of the original R. -/
theorem minimumCenterAction_kernel_characteristic :
    (minimumCenterAction d).ker.Characteristic := by
  rw [minimumCenterAction_kernel]
  infer_instance

private theorem minimumCenter_map :
    (minimumCenter d).map R.subtype =
      (d.radical ⊓ centralizer (d.radical : Set d.overgroup)).map d.overgroup.subtype := by
  rw [minimumCenter,←map_inf_centralizer_of_injective _ R.subtype_injective,
    ←map_inf_centralizer_of_injective _ d.overgroup.subtype_injective,
    map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)]

variable [Finite H]

/-- The characteristic kernel restricts to exactly T in the replacement
overgroup. It need not equal T throughout the original radical. -/
theorem minimumCenterAction_kernel_restriction
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (((minimumCenterAction d).ker.map R.subtype).subgroupOf d.overgroup) = d.radical := by
  have hc := replacement_field_sized_radical_center_centralizer h d g hb hsize
  rw [minimumCenterAction_kernel]
  ext x
  constructor
  · rintro ⟨r,hr,he⟩
    change (r:H)=(x:H) at he
    apply hc.le
    intro z hz
    have hm : (z:H) ∈ (minimumCenter d).map R.subtype := by
      rw [minimumCenter_map]
      exact mem_map_of_mem _ hz
    obtain ⟨w,hw,hew⟩ := hm
    change (w:H)=(z:H) at hew
    apply d.overgroup.subtype_injective
    change (z:H)*(x:H)=(x:H)*(z:H)
    rw [←he,←hew]
    exact congrArg Subtype.val (hr w hw)
  · intro hx
    have hxR : (x:H) ∈ R := map_subtype_le d.subgroup hx
    refine ⟨⟨x,hxR⟩,?_,rfl⟩
    intro z hz
    have hm : (z:H) ∈
        (d.radical ⊓ centralizer (d.radical : Set d.overgroup)).map d.overgroup.subtype := by
      rw [←minimumCenter_map]
      exact mem_map_of_mem _ hz
    obtain ⟨w,hw,hew⟩ := hm
    apply R.subtype_injective
    change (z:H)*(x:H)=(x:H)*(z:H)
    rw [←hew]
    exact congrArg Subtype.val (hw.2 x hx).symm

/-- The literal original intersection R intersect M has image of order q
squared in the same original characteristic action. -/
theorem original_minimum_center_action_card
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    Nat.card ((d.overgroup.subgroupOf R).map (minimumCenterAction d)) = 2^(2*n) := by
  have hk := minimumCenterAction_kernel_restriction h d g hb
    (replacement_proper_nonsylow_card h d g hb hnsyl hne)
  have hki : (minimumCenterAction d).ker ⊓ d.overgroup.subgroupOf R = d.subgroup := by
    ext r
    constructor
    · rintro ⟨hr,hm⟩
      have hh : (⟨r,hm⟩ : d.overgroup) ∈
          ((minimumCenterAction d).ker.map R.subtype).subgroupOf d.overgroup :=
        ⟨r,hr,rfl⟩
      have hd := hk.le hh
      exact (mem_map_iff_mem R.subtype_injective).mp hd
    · intro hr
      have hm : (r:H) ∈ d.overgroup := mem_sup_right (mem_map_of_mem R.subtype hr)
      have hh := hk.ge (show (⟨r,hm⟩ : d.overgroup) ∈ d.radical from
        mem_map_of_mem R.subtype hr)
      exact ⟨(mem_map_iff_mem R.subtype_injective).mp hh,hm⟩
  rw [←relIndex_ker,←inf_relIndex_right,hki]
  have hi := replacement_proper_nonsylow_index h d g hb hnsyl hne
  have him := relIndex_map_map_of_injective d.radical (R.subgroupOf d.overgroup)
    d.overgroup.subtype_injective
  rw [map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right),
    subgroupOf_map_subtype] at him
  rw [←relIndex_map_map_of_injective d.subgroup (d.overgroup.subgroupOf R)
    R.subtype_injective,subgroupOf_map_subtype,inf_comm d.overgroup R]
  exact him.trans hi

/-- The actual selected source star acts on the full minimum center by a
two-group normalized by every restricted original automorphism. The known
order-q-squared original-intersection action embeds in this star action. -/
theorem exists_source_star_characteristic_center_action
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map
        (componentProjection h) = (R.subgroupOf K).map (componentProjection h) ∧
      (MulAut.characteristic (minimumCenter d)).range ≤ normalizer
        ((starCentralizer R Y).map (minimumCenterAction d) : Set (MulAut (minimumCenter d))) ∧
      IsPGroup 2 ((starCentralizer R Y).map (minimumCenterAction d)) ∧
      2^(2*n) ∣ Nat.card ((starCentralizer R Y).map (minimumCenterAction d)) ∧
      (((minimumCenterAction d).ker.map R.subtype).subgroupOf d.overgroup) = d.radical := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl⟩ :=
    exists_source_star_intrinsic_reduction h d
  have hBM : d.overgroup.subgroupOf R ≤ starCentralizer R Y := by
    intro r hr
    have hm : (r:H) ∈ K ⊔ (starCentralizer R Y).map R.subtype :=
      (sup_le_sup_left (map_mono hmin) K) hr
    have hh := hrest.ge (show (⟨r,hm⟩ : (K ⊔ (starCentralizer R Y).map R.subtype : Subgroup H)) ∈
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype) from r.property)
    exact (mem_map_iff_mem R.subtype_injective).mp hh
  refine ⟨P,Y,hY,hn,hmin,hmark,characteristic_conjugation_normalized _ _,
    (h.radical.isPGroup.to_subgroup _).map _,?_,
    minimumCenterAction_kernel_restriction h d g hb
      (replacement_proper_nonsylow_card h d g hb hnsyl hne)⟩
  rw [←original_minimum_center_action_card h d g hb hnsyl hne]
  exact card_dvd_of_le (map_mono hBM)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
