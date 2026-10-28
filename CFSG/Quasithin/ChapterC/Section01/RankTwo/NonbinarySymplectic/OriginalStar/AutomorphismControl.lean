module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.CenterFactors
public import Theory.GroupTheory.AutomorphismInvariantNormalKernel

/-!
# Original automorphisms detect the full center action

Let T be the selected original star, C the full minimum-replacement center,
and V its moving part. The largest subgroup of C intersect C_H(K) that is
characteristic in the ORIGINAL radical R is trivial, by MS3. More generally,
let J be the characteristic core in R of C_T(V). The fixed-factor
calculation puts [C,J] inside C_H(K). Both C and J are characteristic in R,
so MS3 gives [C,J] = 1. Hence J is exactly C_T(C), with the full center and
all fixed attachments retained.

It follows that every nontrivial actor of T on C has an image under an
actual automorphism of R that moves V. This image lies outside the extra
fixed-core action factor. Consequently that factor has trivial intersection
under all conjugations by restricted original automorphisms. The final
consumer constructs the marked, saturated source star and discharges the
field-sized premise from the proper nonsylow branch, retaining the exact
q-squared times fixed-factor order formula.

These results compare the factors under original automorphisms; they do not
assert that the extra factor itself is trivial. Exchanged-kernel exclusion,
minimum marked preservation and saturation, the Sylow branch and the field
restriction remain separate. No automorphism of the minimum replacement is
extended to R.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), MS3 in (2.1)(iii), printed p.855, and the original star and full-kernel
comparisons in (3.7), pp.872--875. The minimum cut is the separate Section 7
construction, pp.932--933. The characteristic-core argument above is an
original-radical consequence of these inputs, not a restatement of (3.7).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open NilesRankOneKernel
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

private theorem core_le {G : Type*} [Group G] (A : Subgroup G) :
    automorphismCore A ≤ A := by
  have hh := iInf_le (fun a : MulAut G => A.map a.toMonoidHom) (MulEquiv.refl G)
  change automorphismCore A ≤ A.map (MonoidHom.id G) at hh
  simpa only [Subgroup.map_id] using hh

private theorem le_core {G : Type*} [Group G] (A J : Subgroup G)
    [J.Characteristic] (hJA : J ≤ A) : J ≤ automorphismCore A := by
  apply le_iInf
  intro a
  rw [←characteristic_iff_map_eq.mp (inferInstance : J.Characteristic) a]
  exact map_mono hJA

include h in
omit [Finite H] [Finite F] [CharP F 2] in
private theorem characteristic_centralizing_eq_bot (J : Subgroup R) [J.Characteristic]
    (hc : J.map R.subtype ≤ centralizer (K : Set H)) : J = ⊥ := by
  have hn : (J.map R.subtype).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_le_iff.mp
    rw [←original_sup h]
    exact sup_le ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
      (R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R J))
  exact h.characteristic.eq_bot_of_normal J hn

include h in
omit [Finite H] [Finite F] [CharP F 2] in
/-- No nontrivial part of the complete component-fixed center is preserved
by every automorphism of the ORIGINAL radical. -/
theorem minimum_fixed_center_automorphism_core_eq_bot :
    automorphismCore (minimumCenter d ⊓
      (centralizer (K : Set H)).comap R.subtype) = ⊥ := by
  apply characteristic_centralizing_eq_bot h
  exact (map_mono ((core_le _).trans inf_le_right)).trans
    (map_comap_le _ _)

include h in
/-- The largest original-characteristic subgroup of the star fixing its
moving center is exactly the kernel on the FULL minimum center. -/
theorem star_moving_kernel_automorphism_core
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
    automorphismCore (starCentralizer R Y ⊓
      (centralizer (V : Set H)).comap R.subtype) =
      starCentralizer R Y ⊓ (minimumCenterAction d).ker := by
  let T := starCentralizer R Y
  let C := minimumCenter d
  let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
  let A := T ⊓ (centralizer (V : Set H)).comap R.subtype
  let J := automorphismCore A
  have hmC : C.map R.subtype = d.ambient ⊓ centralizer (d.ambient : Set H) := by
    dsimp only [C,minimumCenter]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
  have hJ : J ≤ A := core_le A
  have hmA : A.map R.subtype =
      T.map R.subtype ⊓ centralizer (V : Set H) := by
    rw [map_inf _ _ _ R.subtype_injective,map_comap_eq,range_subtype,
      ←inf_assoc,inf_eq_left.mpr (map_subtype_le _)]
  have hfactor := (star_center_fixed_factor_control h d g hb P Y hY hmin hrest hsize).2.2
  have hcentral : ⁅C,J⁆.map R.subtype ≤ centralizer (K : Set H) := by
    rw [map_commutator,hmC]
    apply (commutator_mono le_rfl (map_mono hJ)).trans
    rw [hmA,hfactor]
    let C₀ := d.ambient ⊓ centralizer (d.ambient : Set H)
    let Q₀ := T.map R.subtype ⊓ pCore 2 H
    let N := centralizer (K : Set H)
    let := h.component_normal
    have hN : N.Normal := by dsimp only [N]; infer_instance
    let := hN
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (⊤ : Subgroup H)
      Q₀ (T.map R.subtype ⊓ centralizer (C₀ : Set H)) C₀ N
      (by rw [normalizer_eq_top]) le_top le_top
    · rw [commutator_comm]
      exact minimum_center_core_displacement_centralizes h d g hb Q₀ inf_le_right
    · exact (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right).le.trans bot_le
  have hzero : ⁅C,J⁆ = ⊥ := characteristic_centralizing_eq_bot h _ hcentral
  have hJC : J ≤ centralizer (C : Set R) := by
    rw [commutator_comm] at hzero
    exact commutator_eq_bot_iff_le_centralizer.mp hzero
  change J = T ⊓ (minimumCenterAction d).ker
  apply le_antisymm
  · exact le_inf (hJ.trans inf_le_left) (hJC.trans_eq (minimumCenterAction_kernel d).symm)
  · let := minimumCenterAction_kernel_characteristic d
    apply le_core A
    apply le_inf inf_le_left
    intro x hx
    have hxc : x ∈ centralizer (C : Set R) :=
      (minimumCenterAction_kernel d).le hx.2
    have hVC : V ≤ C.map R.subtype := by
      rw [hmC]
      exact le_sup_left.trans_eq (minimum_center_decomposition h d g hb hsize).1.symm
    intro v hv
    obtain ⟨c,hc,rfl⟩ := hVC hv
    exact congrArg Subtype.val (hxc c hc)

include h in
/-- Every nontrivial full-center actor in the star has an ORIGINAL radical
automorphic image that moves the moving part of that same center. -/
theorem star_center_actor_automorphism_escape
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n)
    (x : R) (hx : x ∈ starCentralizer R Y) (hmove : minimumCenterAction d x ≠ 1) :
    ∃ a : MulAut R, ∃ v ∈ (blockU K).map K.subtype ⊓
        centralizer (d.ambient : Set H),
      ⁅v,(a x : H)⁆ ≠ 1 ∧
      minimumCenterAction d (a x) ∉
        (starCentralizer R Y ⊓ (pCore 2 H).comap R.subtype).map (minimumCenterAction d) := by
  classical
  let T := starCentralizer R Y
  let C := minimumCenter d
  let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
  let A := T ⊓ (centralizer (V : Set H)).comap R.subtype
  have hnot : ¬ ∀ a : MulAut R, a x ∈ A := by
    intro hall
    have hxcore : x ∈ automorphismCore A := by
      apply mem_iInf.mpr
      intro a
      exact ⟨a.symm x,hall a.symm,a.apply_symm_apply x⟩
    have he := star_moving_kernel_automorphism_core h d g hb P Y hY hmin hrest hsize
    change automorphismCore A = T ⊓ (minimumCenterAction d).ker at he
    exact hmove (he.le hxcore).2
  obtain ⟨a,ha⟩ := not_forall.mp hnot
  have haT : a x ∈ T := characteristic_iff_le_comap.mp
    (inferInstance : T.Characteristic) a hx
  have hv : ∃ v ∈ V, ⁅v,(a x : H)⁆ ≠ 1 := by
    by_contra hno
    push Not at hno
    exact ha ⟨haT,fun v hv => (commutatorElement_eq_one_iff_commute.mp (hno v hv)).eq⟩
  obtain ⟨v,hv,hvc⟩ := hv
  refine ⟨a,v,hv,hvc,?_⟩
  rintro ⟨q,hq,heq⟩
  have hQV : (q:H) ∈ centralizer (V : Set H) :=
    ((original_whole_core_centralizer h d g hb).ge.trans
      (centralizer_le (show V ≤ (blockU K).map K.subtype from inf_le_left))) hq.2
  have hVC : V ≤ C.map R.subtype := by
    dsimp only [C,minimumCenter]
    rw [←map_inf_centralizer_of_injective _ R.subtype_injective]
    exact le_sup_left.trans_eq (minimum_center_decomposition h d g hb hsize).1.symm
  obtain ⟨c,hc,hcv⟩ := hVC hv
  have hval := congrArg (fun b : MulAut C => ((b ⟨c,hc⟩ : R) : H)) heq
  change (q:H)*(c:H)*(q:H)⁻¹=(a x:H)*(c:H)*(a x:H)⁻¹ at hval
  change (c:H)=v at hcv
  rw [hcv,←hQV v hv,mul_assoc,mul_inv_cancel,mul_one] at hval
  exact hvc (commutatorElement_eq_one_iff_commute.mpr
    (mul_inv_eq_iff_eq_mul.mp hval.symm).symm)

include h in
/-- The fixed-core action factor has trivial intersection over all
conjugates by the restrictions of ORIGINAL radical automorphisms. -/
theorem star_fixed_action_automorphism_intersection
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
        (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    let Q₀ := starCentralizer R Y ⊓ (pCore 2 H).comap R.subtype
    let C := minimumCenter d
    (⨅ a : MulAut R, (Q₀.map (minimumCenterAction d)).comap
      (MulAut.conj ((MulAut.characteristic C) a)).toMonoidHom) = ⊥ := by
  classical
  let Q₀ := starCentralizer R Y ⊓ (pCore 2 H).comap R.subtype
  let C := minimumCenter d
  apply bot_unique
  intro x hx
  change x=1
  by_contra hxne
  have hxQ : x ∈ Q₀.map (minimumCenterAction d) := by
    have hh := mem_iInf.mp hx (1 : MulAut R)
    change (MulAut.conj ((MulAut.characteristic C) 1)) x ∈ Q₀.map (minimumCenterAction d) at hh
    rw [map_one, map_one] at hh
    exact hh
  obtain ⟨q,hq,heq⟩ := hxQ
  obtain ⟨a,v,hv,hvc,hout⟩ := star_center_actor_automorphism_escape h d g hb P Y hY hmin
    hrest hsize q hq.1 (fun hz => hxne (heq.symm.trans hz))
  have he : (MulAut.conj ((MulAut.characteristic C) a)) (minimumCenterAction d q) =
      minimumCenterAction d (a q) := by
    apply MulEquiv.ext
    intro c
    apply Subtype.ext
    change a (q * a.symm (c:R) * q⁻¹) = a q * (c:R) * (a q)⁻¹
    rw [map_mul,map_mul,map_inv,a.apply_symm_apply]
  have ha := mem_iInf.mp hx a
  change (MulAut.conj ((MulAut.characteristic C) a)) x ∈ Q₀.map (minimumCenterAction d) at ha
  rw [←heq,he] at ha
  exact hout ha

include h in
/-- The selected marked and saturated source star has no nontrivial
extra actor confined to the fixed factor under all ORIGINAL automorphisms.
The same star retains its exact action-factor order and its full kernel. -/
theorem exists_source_star_original_automorphism_control
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
      (let T := starCentralizer R Y
       let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
       let V := (blockU K).map K.subtype ⊓ centralizer (d.ambient : Set H)
       let θ := minimumCenterAction d
       automorphismCore (minimumCenter d ⊓
         (centralizer (K : Set H)).comap R.subtype) = ⊥ ∧
       automorphismCore (T ⊓ (centralizer (V : Set H)).comap R.subtype) = T ⊓ θ.ker ∧
       (⨅ a : MulAut R, (Q₀.map θ).comap
         (MulAut.conj ((MulAut.characteristic (minimumCenter d)) a)).toMonoidHom) = ⊥ ∧
       Nat.card (T.map θ) = 2^(2*n) * Nat.card (Q₀.map θ) ∧
       ∀ x ∈ T, θ x ≠ 1 → ∃ a : MulAut R, ∃ v ∈ V,
         ⁅v,(a x : H)⁆ ≠ 1 ∧ θ (a x) ∉ Q₀.map θ) := by
  obtain ⟨P,Y,hY,hn,hmin,hs,hquot,hrest,hsat,hinner,hmark,hsyl⟩ :=
    exists_source_star_intrinsic_reduction h d
  have hsize := replacement_proper_nonsylow_card h d g hb hnsyl hne
  exact ⟨P,Y,hY,hn,hmin,hmark,hsat,minimum_fixed_center_automorphism_core_eq_bot h d,
    star_moving_kernel_automorphism_core h d g hb P Y hY hmin hrest hsize,
    star_fixed_action_automorphism_intersection h d g hb P Y hY hmin hrest hsize,
    (star_center_action_direct_factors h d g hb P Y hY hmin hrest hnsyl hne).2.2.2,
    fun x hx hmove => star_center_actor_automorphism_escape h d g hb P Y hY hmin hrest
      hsize x hx hmove⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
