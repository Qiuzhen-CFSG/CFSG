module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.CharacteristicCenter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.OriginalLayers
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer

/-!
# The original star's action on the full minimum center

Let T be the selected original characteristic star and M the minimum
replacement overgroup. Marked preservation for T gives R intersect M <= T.
The source innerness then factors T as (R intersect M)(T intersect O₂(H)).
The latter factor centralizes the whole intrinsic module U. Consequently
all its subgroup displacements by T agree with those by R intersect M.
In the proper nonsylow branch this transfers the full three-step series:
[U,T] = C_U(d), the second term D has order q, and [D,T] = 1.

Write C for the FULL center of the minimum replacement. The extra factor
E = [C,T intersect O₂(H)] is normal in H and centralizes K. The full center
has displacement [C,T] = D E, with D and E disjoint. Its second displacement
lies in E and is characteristic in the ORIGINAL R. MS3 therefore kills it.
The same characteristic argument applied to the center's Frattini subgroup
makes C elementary abelian. Hence the original star acts on C through an
elementary abelian group of order divisible by q squared.

The literal selected-star consumer retains the original quotient marking
and saturation. Every fixed attachment is retained. E itself has not been
proved trivial, and the action image has not been proved to have order
exactly q squared. Minimum marked preservation, minimum saturation and the
exchanged-kernel exclusion are still needed before the field restriction.
No automorphism of the minimum replacement is extended to the original R.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), MS3 in (2.1)(iii), p.855, the original star in (3.4), pp.868--869,
and the full-radical and fixed-kernel comparisons in (3.7), pp.872--875.
The minimum cut is the separate Section 7 construction, pp.932--933.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite H] [Finite F] [CharP F 2] in
private theorem characteristic_eq_bot_of_centralizes_component
    (A : Subgroup R) [A.Characteristic]
    (hc : A.map R.subtype ≤ centralizer (K : Set H)) : A = ⊥ := by
  have hn : (A.map R.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [←original_sup h]
    exact sup_le ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
      (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R A))
  exact h.characteristic.eq_bot_of_normal A hn

/-- The whole intrinsic core has the original ambient two-core as its exact centralizer. -/
theorem original_whole_core_centralizer
    (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    centralizer ((blockU K).map K.subtype : Set H) = pCore 2 H := by
  let := h.component_normal
  have hs := (short_and_natural_of_distance_two h d g hb).1
  have hp : IsPGroup 2 (H ⧸ K) :=
    (isPGroup_quotient_pResidual (G := H) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq h.residual_eq)
  exact le_antisymm (centralizer_blockU_le_core_of_normal K hs.fitting hp)
    (hs.normalizing_twoGroup_centralizes_blockU pCore_isPGroup
      (by rw [normalizer_eq_top]; exact le_top)
      (by rw [normalizer_eq_top]; exact le_top))

omit [Finite F] [CharP F 2] in
private theorem intrinsic_le_minimum : (blockU K).map K.subtype ≤ d.ambient := by
  let := h.component_normal
  have hp : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  rw [←d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hp,
    ←map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)]
  exact map_mono ((commutator_le_left _ _).trans (replacement_core_le h d))

/-- The full minimum center is elementary: its characteristic Frattini image centralizes the component, so original MS3 eliminates it. -/
theorem minimum_center_elementary
    (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    IsElementaryAbelian 2 (minimumCenter d) := by
  let C := minimumCenter d
  have hCQ : C.map R.subtype ≤ pCore 2 H := by
    dsimp only [C,minimumCenter]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
    exact (inf_le_right.trans (centralizer_le (intrinsic_le_minimum h d))).trans_eq
      (original_whole_core_centralizer h d g hb)
  let f : C →* pCore 2 H := (R.subtype.comp C.subtype).codRestrict _
    (fun c => hCQ (mem_map_of_mem R.subtype c.property))
  let : Fact (IsPGroup 2 C) := ⟨h.radical.isPGroup.to_subgroup C⟩
  let : Fact (IsPGroup 2 (pCore 2 H)) := ⟨pCore_isPGroup⟩
  let U := (blockU K).map K.subtype
  have hs := (short_and_natural_of_distance_two h d g hb).1
  let : IsElementaryAbelian 2 (blockU K) := hs.elementary
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map K.subtype
  let := h.component_normal
  have hp : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hphi : (frattini (pCore 2 H)).map (pCore 2 H).subtype ≤ centralizer (K : Set H) :=
    frattini_image_le_centralizer_of_elementary_commutator (pCore 2 H) K U pCore_isPGroup
      (MSCentralOrbit.commutatorCore_eq_intrinsic K hp).le
      (original_whole_core_centralizer h d g hb).ge
  let J := (frattini C).map C.subtype
  have hm : J.map R.subtype = ((frattini C).map f).map (pCore 2 H).subtype := by
    dsimp only [J]
    rw [map_map,map_map]
    rfl
  have hJ : J = ⊥ := characteristic_eq_bot_of_centralizes_component h J
    (hm.trans_le ((map_mono (frattini_map_le_of_isPGroup (p := 2) f)).trans hphi))
  have hCphi : frattini C = ⊥ := (map_eq_bot_iff_of_injective _ C.subtype_injective).mp hJ
  have hpow (c : C) : c^2 = 1 := by
    have hh := pth_power_mem_frattini_of_isPGroup (p := 2) c
    rwa [hCphi] at hh
  exact { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

/-- Every original two-core actor moves the full minimum center only into the component centralizer. The three-subgroups argument retains the entire center. -/
theorem minimum_center_core_displacement_centralizes
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (Q₀ : Subgroup H) (hQ₀ : Q₀ ≤ pCore 2 H) :
    ⁅d.ambient ⊓ centralizer (d.ambient : Set H),Q₀⁆ ≤ centralizer (K : Set H) := by
  let := h.component_normal
  let U := (blockU K).map K.subtype
  let Z₀ := d.ambient ⊓ centralizer (d.ambient : Set H)
  have hZU : Z₀ ≤ centralizer (U : Set H) :=
    inf_le_right.trans (centralizer_le (intrinsic_le_minimum h d))
  have hZQ : Z₀ ≤ pCore 2 H := hZU.trans_eq (original_whole_core_centralizer h d g hb)
  have hQU : pCore 2 H ≤ centralizer (U : Set H) :=
    (original_whole_core_centralizer h d g hb).ge
  have hp : IsPPerfect 2 K := by
    rw [←h.residual_eq]
    exact isPPerfect_pResidual 2
  have hQK : ⁅pCore 2 H,K⁆ = U := MSCentralOrbit.commutatorCore_eq_intrinsic K hp
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply commutator_commutator_eq_bot_of_rotate
  · exact commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono hQ₀ le_rfl).trans_eq hQK).trans (le_centralizer_iff.mp hZU))
  · rw [commutator_comm K (d.ambient ⊓ centralizer (d.ambient : Set H))]
    exact commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono hZQ le_rfl).trans_eq hQK).trans
        (le_centralizer_iff.mp (hQ₀.trans hQU)))

omit h [Finite H] [Field F] [Finite F] [CharP F 2] in
private theorem star_contains_original_intersection
    (Y : Subgroup R) (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :
    R ⊓ d.overgroup ≤ (starCentralizer R Y).map R.subtype := by
  intro x hx
  have hxM : x ∈ K ⊔ (starCentralizer R Y).map R.subtype :=
    (sup_le_sup_left (map_mono hmin) K) hx.2
  exact hrest.ge (show (⟨x,hxM⟩ : (K ⊔ (starCentralizer R Y).map R.subtype : Subgroup H)) ∈
    R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype) from hx.1)

/-- The source star factors through the original radical restricted to the minimum overgroup and its own intersection with the ORIGINAL two-core. -/
theorem star_factorization_over_minimum
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype)) :
    let T := (starCentralizer R Y).map R.subtype
    (∀ x ∈ T, ∃ b ∈ R ⊓ d.overgroup, ∃ q ∈ T ⊓ pCore 2 H, b*q=x) ∧
      T = (R ⊓ d.overgroup) ⊔ (T ⊓ pCore 2 H) := by
  let T := (starCentralizer R Y).map R.subtype
  have hBT := star_contains_original_intersection d Y hmin hrest
  have hTR : T ≤ R := map_subtype_le _
  have hf : ∀ x ∈ T, ∃ b ∈ R ⊓ d.overgroup, ∃ q ∈ T ⊓ pCore 2 H, b*q=x := by
    intro x hx
    obtain ⟨k,hk,q,hq,he⟩ := mem_sup_of_normal_right.mp
      (starCentralizer_le_component_core h P Y hY hx)
    have hkR : k ∈ R := by
      have hh := R.mul_mem (hTR hx) (R.inv_mem (h.radical.twoCore_le hq))
      rwa [←he,mul_inv_cancel_right] at hh
    have hkB : k ∈ R ⊓ d.overgroup := ⟨hkR,mem_sup_left hk⟩
    have hqT : q ∈ T := by
      have hh := T.mul_mem (T.inv_mem (hBT hkB)) hx
      rwa [←he,inv_mul_cancel_left] at hh
    exact ⟨k,hkB,q,⟨hqT,hq⟩,he⟩
  refine ⟨hf,le_antisymm ?_ (sup_le hBT inf_le_left)⟩
  intro x hx
  obtain ⟨b,hb,q,hq,rfl⟩ := hf x hx
  exact mul_mem_sup hb hq

/-- Every subgroup of the whole intrinsic module has the same displacement under the full star as under R intersect M. -/
theorem star_commutator_eq_original_intersection
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (A : Subgroup H) (hA : A ≤ (blockU K).map K.subtype) :
    ⁅A,(starCentralizer R Y).map R.subtype⁆ = ⁅A,R ⊓ d.overgroup⁆ := by
  have hc : pCore 2 H ≤ centralizer ((blockU K).map K.subtype : Set H) :=
    (original_whole_core_centralizer h d g hb).ge
  obtain ⟨hf,he⟩ := star_factorization_over_minimum h d P Y hY hmin hrest
  apply le_antisymm
  · apply commutator_le.mpr
    intro a ha x hx
    obtain ⟨b,hb,q,hq,rfl⟩ := hf x hx
    have haq : Commute a q := hc hq.2 a (hA ha)
    rw [commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_commute.mpr haq,mul_one,mul_inv_cancel_right]
    exact commutator_mem_commutator ha hb
  · exact commutator_mono le_rfl (star_contains_original_intersection d Y hmin hrest)

private theorem star_center_displacement
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hnsyl : ¬ ∃ S : Sylow 2 (Theory.SpecificGroups.SymplecticFour.Sp F),
      (S : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp F)) =
        (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    let T := (starCentralizer R Y).map R.subtype
    let C := d.ambient ⊓ centralizer (d.ambient : Set H)
    let D := ⁅C,R ⊓ d.overgroup⁆
    let E := ⁅C,T ⊓ pCore 2 H⁆
    E ≤ centralizer (K : Set H) ∧ E.Normal ∧ Disjoint D E ∧ ⁅C,T⁆ = D ⊔ E := by
  let T := (starCentralizer R Y).map R.subtype
  let C := d.ambient ⊓ centralizer (d.ambient : Set H)
  let B := R ⊓ d.overgroup
  let D := ⁅C,B⁆
  let Q₀ := T ⊓ pCore 2 H
  let E := ⁅C,Q₀⁆
  have hEC : E ≤ centralizer (K : Set H) :=
    minimum_center_core_displacement_centralizes h d g hb Q₀ inf_le_right
  have hRT : R ≤ normalizer (T : Set H) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R (starCentralizer R Y))
  let := d.characteristic
  have hRd : R ≤ normalizer (d.ambient : Set H) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R d.subgroup)
  have hRE : R ≤ normalizer (E : Set H) := by
    intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    dsimp only [E,C,Q₀]
    rw [map_commutator,←map_inf_centralizer_of_injective _ (MulAut.conj r).injective,
      map_inf _ _ _ (MulAut.conj r).injective,
      mem_normalizer_iff_map_conj_eq.mp (hRd hr),
      mem_normalizer_iff_map_conj_eq.mp (hRT hr),
      mem_normalizer_iff_map_conj_eq.mp (show r ∈ normalizer (pCore 2 H : Set H) by
        rw [normalizer_eq_top]; trivial)]
  have hEn : E.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [←original_sup h]
    exact sup_le ((le_centralizer_iff.mp hEC).trans (Subgroup.centralizer_le_normalizer _)) hRE
  let := hEn
  obtain ⟨hdis,hcard,hDU,hjoin⟩ := original_proper_nonsylow_center_overlap h d g hb hnsyl hne
  have hUn : (blockU K).map K.subtype |>.Normal := by
    let := h.component_normal
    infer_instance
  let := hUn
  have hDU' : D ≤ (blockU K).map K.subtype := hDU.trans (commutator_le_left _ _)
  have hDE : Disjoint D E := by
    apply disjoint_iff_inf_le.mpr
    intro x hx
    exact disjoint_iff_inf_le.mp hdis ⟨hx.1,⟨hDU' hx.1,hEC hx.2⟩⟩
  have hQDc : Q₀ ≤ centralizer (D : Set H) :=
    inf_le_right.trans ((original_whole_core_centralizer h d g hb).ge.trans
      (centralizer_le hDU'))
  have hfactor : T = B ⊔ Q₀ := (star_factorization_over_minimum h d P Y hY hmin hrest).2
  have hTD : T ≤ normalizer (D : Set H) := by
    rw [hfactor]
    exact sup_le (normalizer_commutator_ge_right C B)
      (hQDc.trans (Subgroup.centralizer_le_normalizer _))
  have hTDE : T ≤ normalizer ((D ⊔ E : Subgroup H) : Set H) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hTD hx),
      mem_normalizer_iff_map_conj_eq.mp (show x ∈ normalizer (E : Set H) by
        rw [normalizer_eq_top]; trivial)]
  have hBT := star_contains_original_intersection d Y hmin hrest
  change E ≤ centralizer (K : Set H) ∧ E.Normal ∧ Disjoint D E ∧ ⁅C,T⁆ = D ⊔ E
  refine ⟨hEC,hEn,hDE,le_antisymm ?_ ?_⟩
  · conv_lhs => rw [hfactor,commutator_comm]
    exact commutator_sup_le_of_relative_normal T B Q₀ C (D ⊔ E)
      hTDE hBT inf_le_left
      (by rw [commutator_comm]; exact le_sup_left)
      (by rw [commutator_comm]; exact le_sup_right)
  · exact sup_le (commutator_mono le_rfl hBT) (commutator_mono le_rfl inf_le_left)

/-- The actual saturated source star supplies the full intrinsic displacement series and a quadratic action on the entire minimum center. The possible extra fixed-core displacement remains explicit in the conclusion. -/
theorem exists_source_star_whole_core_layers
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
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       let U := (blockU K).map K.subtype
       let D := ⁅⁅U,T⁆,T⁆
       let C := d.ambient ⊓ centralizer (d.ambient : Set H)
       let E := ⁅C,T ⊓ pCore 2 H⁆
       ∃ hs : Input (K.subgroupOf M) (T.subgroupOf M) n F,
         hs.quotientEquiv = (subgroupOfCoreQuotientEquiv le_sup_left).trans h.quotientEquiv ∧
         T.subgroupOf M = R.subgroupOf M ∧
         (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M ∧
         (T.subgroupOf K).map (componentProjection h) =
           (R.subgroupOf K).map (componentProjection h) ∧
         T = (R ⊓ d.overgroup) ⊔ (T ⊓ pCore 2 H) ∧
         ⁅U,T⁆ = U ⊓ centralizer (d.ambient : Set H) ∧
         D = ⁅d.ambient ⊓ centralizer (d.ambient : Set H),R ⊓ d.overgroup⁆ ∧
         Disjoint D (U ⊓ centralizer (K : Set H)) ∧ Nat.card D = 2^n ∧
         D ⊔ (U ⊓ centralizer (K : Set H)) = ⁅U,d.ambient⁆ ∧ ⁅D,T⁆ = ⊥ ∧
         E ≤ centralizer (K : Set H) ∧ E.Normal ∧ Disjoint D E ∧ ⁅C,T⁆ = D ⊔ E ∧
         ⁅⁅C,T⁆,T⁆ = ⊥) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl⟩ :=
    exists_source_star_intrinsic_reduction h d
  let T := (starCentralizer R Y).map R.subtype
  let U := (blockU K).map K.subtype
  let B := R ⊓ d.overgroup
  have hcomm := star_commutator_eq_original_intersection h d g hb P Y hY hmin hrest
  have hfirst : ⁅U,T⁆ = ⁅U,B⁆ := hcomm U le_rfl
  obtain ⟨hfirstB,hsecondB,hdis,hcard,hjoin,hthirdB⟩ :=
    original_proper_nonsylow_displacement_layers h d g hb hnsyl hne
  have hfirstU : ⁅U,T⁆ ≤ U := hfirst.trans_le (hfirstB.trans_le inf_le_left)
  have hsecond : ⁅⁅U,T⁆,T⁆ = ⁅⁅U,B⁆,B⁆ := (hcomm _ hfirstU).trans (by rw [hfirst])
  have hsecondU : ⁅⁅U,T⁆,T⁆ ≤ U := by
    rw [hsecond]
    exact le_sup_left.trans_eq hjoin |>.trans
      (le_normalizer_iff_commutator_le_left.mp (by
        let := h.component_normal
        exact (map_subtype_le d.subgroup).trans
          ((show R ≤ normalizer (K : Set H) from by rw [normalizer_eq_top]; exact le_top).trans
            (normalizer_le_normalizer_characteristic_image K (blockU K)))))
  refine ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hmark,
    (star_factorization_over_minimum h d P Y hY hmin hrest).2,
    hfirst.trans hfirstB,hsecond.trans hsecondB,?_,?_,?_,?_,?_⟩
  · change Disjoint ⁅⁅U,T⁆,T⁆ _
    rw [hsecond]
    exact hdis
  · change Nat.card (⁅⁅U,T⁆,T⁆ : Subgroup H) = _
    rw [hsecond]
    exact hcard
  · change ⁅⁅U,T⁆,T⁆ ⊔ _ = _
    rw [hsecond]
    exact hjoin
  · rw [hcomm _ hsecondU,hsecond]
    exact hthirdB
  · let C := d.ambient ⊓ centralizer (d.ambient : Set H)
    let E := ⁅C,T ⊓ pCore 2 H⁆
    obtain ⟨hEC,hEn,hDE,hCE⟩ := star_center_displacement h d g hb P Y hY hmin hrest hnsyl hne
    have hD : ⁅⁅U,T⁆,T⁆ = ⁅C,B⁆ := hsecond.trans hsecondB
    have hDT : ⁅⁅C,B⁆,T⁆ = ⊥ := by
      rw [←hD,hcomm _ hsecondU,hsecond]
      exact hthirdB
    change E ≤ centralizer (K : Set H) ∧ E.Normal ∧
      Disjoint ⁅⁅U,T⁆,T⁆ E ∧ ⁅C,T⁆ = ⁅⁅U,T⁆,T⁆ ⊔ E ∧ ⁅⁅C,T⁆,T⁆ = ⊥
    refine ⟨hEC,hEn,hD ▸ hDE,?_,?_⟩
    · rw [hD]
      exact hCE
    · let := hEn
      have hCE' : ⁅C,T⁆ = ⁅C,B⁆ ⊔ E := hCE
      have hbound : ⁅⁅C,T⁆,T⁆ ≤ E := by
        rw [hCE']
        exact commutator_sup_le_of_relative_normal (⊤ : Subgroup H) ⁅C,B⁆ E T E
          (by rw [normalizer_eq_top]) le_top le_top (hDT.le.trans bot_le)
          (commutator_le_left _ _)
      let J := ⁅⁅minimumCenter d,starCentralizer R Y⁆,starCentralizer R Y⁆
      have hm : J.map R.subtype = ⁅⁅C,T⁆,T⁆ := by
        dsimp only [J,minimumCenter,C,T]
        rw [map_commutator,map_commutator,
          ←map_inf_centralizer_of_injective _ R.subtype_injective]
      have hj : J = ⊥ := characteristic_eq_bot_of_centralizes_component h J
        (hm.trans_le (hbound.trans hEC))
      rw [←hm,hj,Subgroup.map_bot]

private theorem star_center_action_elementary
    (g : Geometry d.radical) (hb : g.b d.radical = 2) (Y : Subgroup R)
    (hq : ⁅⁅d.ambient ⊓ centralizer (d.ambient : Set H),
        (starCentralizer R Y).map R.subtype⁆,(starCentralizer R Y).map R.subtype⁆ = ⊥) :
    IsElementaryAbelian 2 ((starCentralizer R Y).map (minimumCenterAction d)) := by
  let C := minimumCenter d
  let T := starCentralizer R Y
  let : IsElementaryAbelian 2 C := minimum_center_elementary h d g hb
  have hquad : ⁅⁅C,T⁆,T⁆ = ⊥ := by
    apply map_injective R.subtype_injective
    rw [map_commutator,map_commutator,Subgroup.map_bot]
    dsimp only [C,minimumCenter,T]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
    exact hq
  have hWC : ⁅C,T⁆ ≤ C := commutator_le_left _ _
  have hWT : ⁅C,T⁆ ≤ centralizer (T : Set R) :=
    commutator_eq_bot_iff_le_centralizer.mp hquad
  have hpow (x : T.map (minimumCenterAction d)) : x^2=1 := by
    obtain ⟨r,hr,he⟩ := x.property
    apply Subtype.ext
    change (x : MulAut C)^2=1
    rw [←he,←map_pow]
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change r^2 * (c:R) * (r^2)⁻¹ = (c:R)
    have hw : ⁅r,(c:R)⁆ ∈ ⁅C,T⁆ :=
      commutator_comm T C ▸ commutator_mem_commutator hr c.property
    have hcomm : Commute r ⁅r,(c:R)⁆ := hWT hw r hr
    have hsq : ⁅r^2,(c:R)⁆=1 := by
      rw [pow_two,commutatorElement_mul_left_eq_conj_mul,hcomm.eq,
        mul_inv_cancel_right,←pow_two]
      exact elemPow_eq_one_of_isElementaryAbelian _ (hWC hw)
    have hc := commutatorElement_eq_one_iff_commute.mp hsq
    rw [hc.eq,mul_inv_cancel_right]
  exact { toIsMulCommutative := ⟨⟨fun a b => (Commute.of_orderOf_dvd_two
    (fun x => orderOf_dvd_of_pow_eq_one (hpow x)) a b).eq⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

/-- The selected original star acts on the full minimum center by an elementary abelian group of order divisible by q squared, with the original marking and star saturation discharged. -/
theorem exists_source_star_elementary_center_action
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
      IsElementaryAbelian 2 (minimumCenter d) ∧
      IsElementaryAbelian 2 ((starCentralizer R Y).map (minimumCenterAction d)) ∧
      2^(2*n) ∣ Nat.card ((starCentralizer R Y).map (minimumCenterAction d)) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hmark,hfactor,hfirst,hD,
    hdis,hcard,hjoin,hthird,hEC,hEn,hDE,hCE,hquad⟩ :=
    exists_source_star_whole_core_layers h d g hb hnsyl hne
  refine ⟨P,Y,hY,hn,hmin,hmark,hsat,minimum_center_elementary h d g hb,
    star_center_action_elementary h d g hb Y hquad,?_⟩
  have hBT := star_contains_original_intersection d Y hmin hrest
  have hBM : d.overgroup.subgroupOf R ≤ starCentralizer R Y := by
    intro r hr
    exact (mem_map_iff_mem R.subtype_injective).mp (hBT ⟨r.property,hr⟩)
  rw [←original_minimum_center_action_card h d g hb hnsyl hne]
  exact card_dvd_of_le (map_mono hBM)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
