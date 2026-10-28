module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.AutomorphismControl
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedDisplacement

/-!
# A displacement gap for the original star on the full minimum center

Every nontrivial star actor has an image under an automorphism of the
ORIGINAL radical that moves the moving part of the minimum center. Both
that image and the minimum radical act through the original component on
the natural cover. Fixed-vector lifting and field scalars therefore give
at least q distinct commutators. Original characteristicity transports
this lower bound back to the original actor on the FULL center.

Consequently no subgroup of the star has nonzero center displacement of
order less than q. Apply this to the star's intersection with the original
two-core. Its retained component-fixed displacement E is either trivial
or has order at least q. The existing disjoint factorization gives the
exact full displacement order q |E|, hence order q or at least q squared.
The last theorem constructs the actual marked, saturated source star and
discharges the field-sized minimum-image premise in the proper nonsylow
branch. It retains all fixed attachments and the original field degree.

This sharpens the original automorphism constraint; it does not exclude
the large displacement branch. Exchanged-kernel control, minimum marked
preservation and saturation, the Sylow branch, n = 2 and final block
assembly remain open. No replacement automorphism is extended to R.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), MS3 in (2.1)(iii), p.855, the full cover in (1.5)(ii), and the
original star and fixed-kernel comparison in (3.7), pp.872--875. The minimum
cut is the separate Section 7 construction, pp.932--933; the displacement
gap here is a consequence of the original inputs, not the full (3.7).
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open scoped commutatorElement IsMulCommutative

open Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open ChapterB.QuasisimpleSource Representation.BinaryOffender Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem moving_center_displacement_card_ge
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (x : R) (hx : x ∈ starCentralizer R Y)
    (v : H) (hv : v ∈ (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H))
    (hmove : ⁅v,(x:H)⁆ ≠ 1) :
    2^n ≤ Nat.card (⁅(blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H),
      zpowers (x:H)⁆ : Subgroup H) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let := h.component_image_structure.2.1
  let hk := (QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _) hk) C
  obtain ⟨E,hE,e,he⟩ := h.centralOmega_initial_cover
  let j := ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 H)) K q
    (QuotientGroup.mk'_surjective _) hk
  have hj := ElementaryMovedCover.embedding_injective (omegaCenterIn (pCore 2 H)) K q
    (QuotientGroup.mk'_surjective _) hk
  let := h.component_normal
  have hblock : IsBlock K := ⟨inferInstance,
    (short_and_natural_of_distance_two h d g hb).1,h.component.subnormal⟩
  have hjr : j.range=(blockU K).map K.subtype :=
    (ElementaryMovedCover.embedding_range _ _ _ _ _).trans (BlockOmega.omega_commutator hblock)
  have hinner (y : H) (hy : y ∈ K ⊔ pCore 2 H) : q y ∈ C := by
    obtain ⟨k,hk,z,hz,rfl⟩ := mem_sup_of_normal_right.mp hy
    rw [map_mul,show q z=1 from (QuotientGroup.eq_one_iff _).mpr hz,mul_one]
    exact mem_map_of_mem q hk
  have hTin : d.ambient ≤ K ⊔ pCore 2 H :=
    (map_mono hmin).trans (starCentralizer_le_component_core h P Y hY)
  let β := e.groupEquiv.toMonoidHom.comp
    ((q.comp d.ambient.subtype).codRestrict C (fun y => hinner y (hTin y.property)))
  have hxin : q (x:H) ∈ C := hinner x
    (starCentralizer_le_component_core h P Y hY (mem_map_of_mem R.subtype hx))
  let γ := e.groupEquiv ⟨q (x:H),hxin⟩
  have hT (t : d.ambient) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β t) w)) =
        (t:H)*j (Multiplicative.ofAdd w)*(t:H)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv _)) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact ElementaryMovedCover.embedding_conjugate (omegaCenterIn (pCore 2 H)) K q
      (QuotientGroup.mk'_surjective _) hk (t:H) w
  have hxact (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e γ w)) =
        (x:H)*j (Multiplicative.ofAdd w)*(x:H)⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv _)) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact ElementaryMovedCover.embedding_conjugate (omegaCenterIn (pCore 2 H)) K q
      (QuotientGroup.mk'_surjective _) hk (x:H) w
  have hh := fixed_actor_displacement_card_ge (MovedSection.coverProjection s e) he
    j hj d.ambient β hT (x:H) γ hxact v (hjr.symm ▸ hv) hmove
  rwa [hjr,E.card_eq,hE] at hh

/-- Every nontrivial actor of the original star moves at least a full field
of elements of the COMPLETE minimum center. -/
theorem star_center_actor_displacement_card_ge
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (x : R) (hx : x ∈ starCentralizer R Y) (hmove : minimumCenterAction d x ≠ 1) :
    2^n ≤ Nat.card (⁅minimumCenter d,zpowers x⁆ : Subgroup R) := by
  obtain ⟨a,v,hv,hvc,_⟩ := star_center_actor_automorphism_escape h d g hb P Y hY
    hmin hrest hsize x hx hmove
  have haT : a x ∈ starCentralizer R Y := characteristic_iff_le_comap.mp
    (inferInstance : (starCentralizer R Y).Characteristic) a hx
  have hlo := moving_center_displacement_card_ge h d g hb P Y hY hmin (a x) haT v hv hvc
  have hmC : (minimumCenter d).map R.subtype =
      d.ambient ⊓ centralizer (d.ambient : Set H) := by
    dsimp only [minimumCenter]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
  have hVC : (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H) ≤
      (minimumCenter d).map R.subtype := by
    rw [hmC]
    exact le_sup_left.trans_eq (minimum_center_decomposition h d g hb hsize).1.symm
  have hle : ⁅(blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H),zpowers (a x:H)⁆ ≤
      (⁅minimumCenter d,zpowers (a x)⁆).map R.subtype := by
    rw [map_commutator,MonoidHom.map_zpowers]
    exact commutator_mono hVC le_rfl
  have hh := hlo.trans (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _))
  rw [card_map_of_injective R.subtype_injective] at hh
  have he : (⁅minimumCenter d,zpowers x⁆).map a.toMonoidHom =
      ⁅minimumCenter d,zpowers (a x)⁆ := by
    rw [map_commutator,MonoidHom.map_zpowers,characteristic_iff_map_eq.mp inferInstance a]
    rfl
  rw [←he,card_map_of_injective a.injective] at hh
  exact hh

/-- A subgroup of the original star with less than field-sized movement on
the full minimum center acts trivially. The bound concerns the whole center,
including its component-fixed attachments. -/
theorem star_small_center_displacement_centralizes
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (A : Subgroup R) (hA : A ≤ starCentralizer R Y)
    (hsmall : Nat.card (⁅minimumCenter d,A⁆ : Subgroup R) < 2^n) :
    A ≤ centralizer (minimumCenter d : Set R) := by
  rw [←minimumCenterAction_kernel]
  intro x hx
  change minimumCenterAction d x=1
  by_contra hmove
  have hlo := star_center_actor_displacement_card_ge h d g hb P Y hY hmin hrest
    hsize x (hA hx) hmove
  have hle : ⁅minimumCenter d,zpowers x⁆ ≤ ⁅minimumCenter d,A⁆ :=
    commutator_mono le_rfl ((zpowers_le).mpr hx)
  exact (not_lt_of_ge (hlo.trans (Nat.card_le_card_of_injective
    (inclusion hle) (inclusion_injective _)))) hsmall

/-- The selected marked, saturated source star has a gap in its full-center
movement: it has order q, or at least q squared. Any nonzero extra fixed-core
displacement already has order at least q. This does not eliminate the large
branch or assert minimum marked preservation. -/
theorem exists_source_star_displacement_gap
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map (componentProjection h) =
        (R.subgroupOf K).map (componentProjection h) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M) ∧
      (∀ x ∈ starCentralizer R Y, minimumCenterAction d x ≠ 1 →
        2^n ≤ Nat.card (⁅minimumCenter d,zpowers x⁆ : Subgroup R)) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let C := d.ambient ⊓ centralizer (d.ambient : Set H)
       let E := ⁅C,T ⊓ pCore 2 H⁆
       E ≤ centralizer (K : Set H) ∧ E.Normal ∧
         (E = ⊥ ∨ 2^n ≤ Nat.card E) ∧
         Nat.card (⁅C,T⁆ : Subgroup H) = 2^n * Nat.card E ∧
         (Nat.card (⁅C,T⁆ : Subgroup H) = 2^n ∨
           2^(2*n) ≤ Nat.card (⁅C,T⁆ : Subgroup H))) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hmark,hfactor,hfirst,hD,
    hdis,hcard,hjoin,hthird,hEC,hEn,hDE,hCE,hquad⟩ :=
    exists_source_star_whole_core_layers h d g hb hnsyl hne
  have hsize := replacement_proper_nonsylow_card h d g hb hnsyl hne
  let T := (starCentralizer R Y).map R.subtype
  let C := d.ambient ⊓ centralizer (d.ambient : Set H)
  let E := ⁅C,T ⊓ pCore 2 H⁆
  have hgap : E = ⊥ ∨ 2^n ≤ Nat.card E := by
    by_cases hz : E=⊥
    · exact Or.inl hz
    right
    by_contra hnot
    have hsmall : Nat.card E < 2^n := Nat.lt_of_not_ge hnot
    let Q₀ := starCentralizer R Y ⊓ (pCore 2 H).comap R.subtype
    have hmQ : Q₀.map R.subtype = T ⊓ pCore 2 H := by
      rw [map_inf _ _ _ R.subtype_injective,map_comap_eq,range_subtype,
        ←inf_assoc,inf_eq_left.mpr (map_subtype_le _)]
    have hm : ⁅minimumCenter d,Q₀⁆.map R.subtype = E := by
      rw [map_commutator,hmQ]
      dsimp only [minimumCenter,E,C]
      rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
    have hsmall' : Nat.card (⁅minimumCenter d,Q₀⁆ : Subgroup R) < 2^n := by
      rwa [←hm,card_map_of_injective R.subtype_injective] at hsmall
    have hc := star_small_center_displacement_centralizes h d g hb P Y hY hmin hrest
      hsize Q₀ inf_le_left hsmall'
    have hz' : ⁅minimumCenter d,Q₀⁆=⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr hc
    apply hz
    rw [←hm,hz',Subgroup.map_bot]
  have he : Nat.card (⁅C,T⁆ : Subgroup H) = 2^n * Nat.card E := by
    let := hEn
    rw [hCE,sup_comm,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      (by rw [normalizer_eq_top]; exact le_top) hDE.symm,hcard,Nat.mul_comm]
  refine ⟨P,Y,hY,hn,hmin,hmark,hsat,
    fun x hx hxne => star_center_actor_displacement_card_ge h d g hb P Y hY hmin hrest
      hsize x hx hxne,hEC,hEn,hgap,he,?_⟩
  rcases hgap with hz | hlo
  · left
    rw [he,hz,card_bot,Nat.mul_one]
  · right
    rw [he,two_mul,pow_add]
    exact Nat.mul_le_mul_left _ hlo
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
