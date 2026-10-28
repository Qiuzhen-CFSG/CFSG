module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.ExchangedAction
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even

/-!
# Original-star mixed commutators at the retained critical automorphism

Write T for the selected original star in R, Q₀ = T intersect O₂(H),
T₀ = T intersect K, and U for the complete intrinsic moving core.
The original symplectic multiplier gives K intersect O₂(H) = U. The
literal star restriction gives T = T₀ Q₀ and T₀ intersect Q₀ = U.
We also identify Q₀, through the actual inclusions, with the full two-core
of K T; its component-fixed part is retained.

In the nonsylow branch the original marked radical is a point or plane
radical, so [T,T] lies in Q₀. Since T is characteristic in the ORIGINAL R,
its derived group lies in Q₀ and in a(Q₀) for every a in Aut(R). The entire
U centralizes Q₀. Consequently [a(U),T₀] lies in U, and the three-subgroups
identity gives [a(U),Q₀,T₀] = 1. Applying the same calculation to a inverse
and mapping back proves the opposite triple. The common displacement
[U,a(U)] centralizes T.

The final theorem applies these identities to the same original star and
original automorphism selected by the critical kernel comparison. It keeps
the original quotient marking, genuine star saturation and literal minimum
graph critical path. No automorphism of the minimum radical is extended.

This is the moving-module part of MS93 (3.7)(1), printed p.873, with the
complete U and both complete original cores. It is not yet the assertion
for the full Z layers. In particular the extra fixed-core action on the
full minimum center is not excluded. The next source comparison is (3.7)(2),
pp.873--874, using the actual dual cover and both original core kernels;
the minimum radical's order-q image cannot replace the full radical in
that argument. Minimum marked preservation and saturation, the Sylow
branch, the field restriction and final block assembly remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.6)--(3.7), printed pp.870--877. The perfect-central-cover
calculation also appears for the minimum graph in
SaturatedDistanceTwo/ComponentIntersection; here it is applied directly to
the original component, without assuming saturation of that minimum cut.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
private theorem symplectic_kernel_eq_commutator
    {F E : Type*} [Field F] [Finite F] [CharP F 2] [Group E] [Group.IsPerfect E]
    (hF : 3 < Nat.card F) (f : E →* Sp F) (hf : Function.Surjective f)
    (N : Subgroup E) [N.Normal] (hN : N ≤ f.ker)
    (hc : ⁅f.ker, (⊤ : Subgroup E)⁆ ≤ N) : f.ker = N := by
  let φ := QuotientGroup.lift N f hN
  have hφ : Function.Surjective φ := QuotientGroup.lift_surjective_of_surjective N f hf hN
  have hcentral : φ.ker ≤ center (E ⧸ N) := by
    intro x hx
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective N x
    have hx' : x ∈ f.ker := hx
    apply mem_center_iff.mpr
    intro y
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective N y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    have hc' : ⁅(⊤ : Subgroup E),f.ker⁆ ≤ N := by rwa [commutator_comm]
    exact (QuotientGroup.eq_one_iff _).mpr (hc' (commutator_mem_commutator (mem_top y) hx'))
  let C : PerfectCentralCovering.Cover (E ⧸ N) (Sp F) :=
    { φ with surjective := hφ, isPerfect := inferInstance, ker_le_center := hcentral }
  have hi := CentralCovers.Even.cover_injective hF C
  apply le_antisymm _ hN
  intro x hx
  apply (QuotientGroup.eq_one_iff _).mp
  apply hi
  exact (show φ (QuotientGroup.mk' N x) = 1 from hx).trans (map_one φ).symm


private theorem characteristic_pair_triples {G : Type*} [Group G]
    (T U Q B : Subgroup G) [T.Characteristic] [Q.Normal] [B.Normal]
    (hUQ : U ≤ Q) (hQT : Q ≤ T) (hBT : B ≤ T) (hBQ : B ⊓ Q = U)
    (hT : T = B ⊔ Q) (hderived : ⁅T,T⁆ ≤ Q)
    (hcentral : U ≤ centralizer (Q : Set G)) (a : MulAut G) :
    ⁅U.map a.toMonoidHom,B⁆ ≤ U ∧
      ⁅⁅U.map a.toMonoidHom,Q⁆,B⁆ = ⊥ ∧
      ⁅U,U.map a.toMonoidHom⁆ ≤ centralizer (T : Set G) := by
  have hUT : U.map a.toMonoidHom ≤ T :=
    (map_mono (hUQ.trans hQT)).trans_eq
      (characteristic_iff_map_eq.mp inferInstance a)
  have hfirst : ⁅U.map a.toMonoidHom,B⁆ ≤ U := by
    exact (le_inf (commutator_le_right _ _)
      ((commutator_mono hUT hBT).trans hderived)).trans_eq hBQ
  have hderived' : ⁅T,T⁆ ≤ Q.map a.toMonoidHom := by
    have hh := map_mono (f := a.toMonoidHom) hderived
    rwa [map_commutator,characteristic_iff_map_eq.mp inferInstance a] at hh
  have hcentral' : U.map a.toMonoidHom ≤
      centralizer (Q.map a.toMonoidHom : Set G) :=
    (map_mono hcentral).trans (map_centralizer_le_centralizer_image _ _)
  have h1 : ⁅⁅Q,B⁆,U.map a.toMonoidHom⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (((commutator_mono hQT hBT).trans hderived').trans
        (le_centralizer_iff.mp hcentral'))
  have h2 : ⁅⁅B,U.map a.toMonoidHom⁆,Q⁆ = ⊥ := by
    rw [commutator_comm B]
    exact commutator_eq_bot_iff_le_centralizer.mpr (hfirst.trans hcentral)
  have hreverse := commutator_commutator_eq_bot_of_rotate h1 h2
  refine ⟨hfirst,hreverse,?_⟩
  have hB : ⁅U,U.map a.toMonoidHom⁆ ≤ centralizer (B : Set G) := by
    rw [commutator_comm U]
    exact (commutator_mono le_rfl hUQ).trans
      (commutator_eq_bot_iff_le_centralizer.mp hreverse)
  have hUn : U.Normal := hBQ ▸ inferInstance
  let := hUn
  have hQ : ⁅U,U.map a.toMonoidHom⁆ ≤ centralizer (Q : Set G) :=
    (commutator_le_left _ _).trans hcentral
  apply le_centralizer_iff.mpr
  rw [hT]
  exact sup_le (le_centralizer_iff.mp hB) (le_centralizer_iff.mp hQ)

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite H] in
/-- The original perfect component has no extra two-core above its
intrinsic commutator core, by the multiplier of the marked Sp₄(F). -/
theorem original_component_core_eq_moving : pCore 2 K = blockU K := by
  let : Group.IsPerfect K := h.component.perfect
  have hF : 3 < Nat.card F := by
    rw [h.field_card]
    exact lt_of_lt_of_le (by decide : 3 < 2^2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) h.nonbinary)
  have hk := componentProjection_kernel h
  have he := symplectic_kernel_eq_commutator hF (componentProjection h)
    (componentProjection_surjective h) (blockU K)
    (blockU_le_core.trans_eq hk.symm) (by rw [hk]; exact le_rfl)
  exact hk.symm.trans he

include d in
private theorem original_marked_nonsylow_commutative
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    IsMulCommutative ((R.subgroupOf K).map (componentProjection h)) := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  rcases original_marked_radical_alternatives h d with ⟨u,hu⟩ | hs
  · let D := (R.subgroupOf K).map (componentProjection h)
    let e := D.equivMapOfInjective (MulAut.conj u).toMonoidHom (MulAut.conj u).injective
    have he : IsMulCommutative (D.map (MulAut.conj u).toMonoidHom) := by
      rcases hu with ⟨hp,_⟩ | ⟨hp,_⟩
      · rw [hp]
        infer_instance
      · rw [hp]
        infer_instance
    let := he
    exact ⟨⟨fun x y => e.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
  · exact (hnsyl hs).elim


private theorem original_component_inf_core :
    K ⊓ pCore 2 H = (blockU K).map K.subtype := by
  rw [←original_component_core_eq_moving h,
    pCore_subnormal_eq_comap 2 h.component_normal.isSubnormal,
    map_comap_eq,range_subtype]

include d in
private theorem star_derived_le_original_core
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    ⁅(starCentralizer R Y).map R.subtype,(starCentralizer R Y).map R.subtype⁆ ≤ pCore 2 H := by
  let D := (R.subgroupOf K).map (componentProjection h)
  let : IsMulCommutative D := original_marked_nonsylow_commutative h d hnsyl
  have hderived : ⁅K ⊓ R,K ⊓ R⁆ ≤ pCore 2 H := by
    apply commutator_le.mpr
    intro x hx y hy
    let xK : K := ⟨x,hx.1⟩
    let yK : K := ⟨y,hy.1⟩
    have hxD : componentProjection h xK ∈ D := mem_map_of_mem _ hx.2
    have hyD : componentProjection h yK ∈ D := mem_map_of_mem _ hy.2
    have hc : Commute (componentProjection h xK) (componentProjection h yK) :=
      congrArg Subtype.val (mul_comm (⟨_,hxD⟩ : D) ⟨_,hyD⟩)
    have hk : ⁅xK,yK⁆ ∈ pCore 2 K := by
      rw [←componentProjection_kernel h]
      change componentProjection h ⁅xK,yK⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_commute.mpr hc
    have hh := (pCoreIn_le_of_subnormal 2 h.component.subnormal)
      (mem_map_of_mem K.subtype hk)
    exact hh
  let T := (starCentralizer R Y).map R.subtype
  let q := QuotientGroup.mk' (pCore 2 H)
  have him : T.map q ≤ (K ⊓ R).map q := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨k,hk,r,hr,he⟩ := mem_sup_of_normal_right.mp
      (starCentralizer_le_component_core h P Y hY hx)
    have hkR : k ∈ R := by
      have hh := R.mul_mem ((map_subtype_le _) hx) (R.inv_mem (h.radical.twoCore_le hr))
      rwa [←he,mul_inv_cancel_right] at hh
    refine ⟨k,⟨hk,hkR⟩,?_⟩
    have hq : q r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    rw [←he,map_mul,hq,mul_one]
  have hzero : ⁅T,T⁆.map q = ⊥ := by
    apply le_bot_iff.mp
    rw [map_commutator]
    apply (commutator_mono him him).trans
    rw [←map_commutator,map_le_iff_le_comap]
    change ⁅K ⊓ R,K ⊓ R⁆ ≤ q.ker
    rw [QuotientGroup.ker_mk']
    exact hderived
  exact ((Subgroup.map_eq_bot_iff _).mp hzero).trans_eq (QuotientGroup.ker_mk' _)

/-- The original nonsylow star satisfies the moving-module clauses of
MS93 (3.7)(1) for every automorphism of the original radical. Both full
original two-cores, including their fixed parts, are used in the triples. -/
theorem star_original_moving_triples
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hmin : d.subgroup ≤ starCentralizer R Y)
    (hrest : (((starCentralizer R Y).map R.subtype).subgroupOf
      (K ⊔ (starCentralizer R Y).map R.subtype)) =
      R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype))
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) (a : MulAut R) :
    let T := starCentralizer R Y
    let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
    let T₀ := T ⊓ K.comap R.subtype
    let U₀ := ((blockU K).map K.subtype).subgroupOf R
    ⁅U₀.map a.toMonoidHom,T₀⁆ ≤ U₀ ∧
      ⁅⁅U₀.map a.toMonoidHom,Q₀⁆,T₀⁆ = ⊥ ∧
      ⁅U₀,U₀.map a.toMonoidHom⁆ ≤ centralizer (T : Set R) := by
  let := h.component_normal
  let T := starCentralizer R Y
  let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
  let T₀ := T ⊓ K.comap R.subtype
  let U₀ := ((blockU K).map K.subtype).subgroupOf R
  have hUT : U₀ ≤ T := by
    have hp : IsPPerfect 2 K := by
      rw [←h.residual_eq]
      exact isPPerfect_pResidual 2
    have hminU : (blockU K).map K.subtype ≤ d.ambient := by
      rw [←d.commutatorCore_eq_intrinsic_of_sup (original_sup h) hp,
        ←map_subgroupOf_eq_of_le (show d.ambient ≤ d.overgroup from le_sup_right)]
      exact map_mono ((commutator_le_left _ _).trans (replacement_core_le h d))
    intro x hx
    exact hmin ((mem_map_iff_mem R.subtype_injective).mp (hminU hx))
  have hUQ : U₀ ≤ Q₀ := le_inf hUT (fun _ hx => (original_component_inf_core h).ge hx |>.2)
  have hBQ : T₀ ⊓ Q₀ = U₀ := by
    ext x
    constructor
    · rintro ⟨⟨_,hxK⟩,_,hxQ⟩
      exact (original_component_inf_core h).le ⟨hxK,hxQ⟩
    · intro hx
      have hh := (original_component_inf_core h).ge hx
      exact ⟨⟨hUT hx,hh.1⟩,hUT hx,hh.2⟩
  have hT : T = T₀ ⊔ Q₀ := by
    apply le_antisymm _ (sup_le inf_le_left inf_le_left)
    intro x hx
    obtain ⟨k,hk,q,hq,he⟩ := mem_sup_of_normal_right.mp
      (starCentralizer_le_component_core h P Y hY (mem_map_of_mem R.subtype hx))
    change k*q=(x:H) at he
    have hkR : k ∈ R := by
      have hh := R.mul_mem x.property (R.inv_mem (h.radical.twoCore_le hq))
      rwa [←he,mul_inv_cancel_right] at hh
    have hqR : q ∈ R := h.radical.twoCore_le hq
    have hqT : (⟨q,hqR⟩ : R) ∈ T := by
      have hn : (⟨k,hkR⟩ : R) ∈ T := by
        have hkM : k ∈ K ⊔ (starCentralizer R Y).map R.subtype := mem_sup_left hk
        have hh := hrest.ge (show (⟨k,hkM⟩ : ↥(K ⊔ (starCentralizer R Y).map R.subtype : Subgroup H)) ∈
          R.subgroupOf (K ⊔ (starCentralizer R Y).map R.subtype) from hkR)
        exact (mem_map_iff_mem R.subtype_injective).mp hh
      have hh : (⟨k,hkR⟩ : R) * ⟨q,hqR⟩ ∈ T := by
        have hh : (⟨k,hkR⟩ : R) * ⟨q,hqR⟩ = x := Subtype.ext he
        exact hh.symm ▸ hx
      exact (T.mul_mem_cancel_left hn).mp hh
    have hkT : (⟨k,hkR⟩ : R) ∈ T := by
      have hh := T.mul_mem hx (T.inv_mem hqT)
      have he' : x*(⟨q,hqR⟩ : R)⁻¹ = ⟨k,hkR⟩ := by
        apply Subtype.ext
        change (x:H)*q⁻¹=k
        rw [←he,mul_inv_cancel_right]
      exact he' ▸ hh
    have he' : (⟨k,hkR⟩ : R)*⟨q,hqR⟩=x := Subtype.ext he
    rw [←he']
    exact mul_mem_sup (show (⟨k,hkR⟩ : R) ∈ T₀ from ⟨hkT,hk⟩)
      (show (⟨q,hqR⟩ : R) ∈ Q₀ from ⟨hqT,hq⟩)
  have hderived : ⁅T,T⁆ ≤ Q₀ := by
    apply le_inf
    · exact (Subgroup.commutator_le_sup _ _).trans (sup_idem T).le
    · apply map_le_iff_le_comap.mp
      rw [map_commutator]
      exact star_derived_le_original_core h d P Y hY hnsyl
  have hcentral : U₀ ≤ centralizer (Q₀ : Set R) := by
    intro u hu q hq
    apply R.subtype_injective
    exact ((original_whole_core_centralizer h d g hb).ge hq.2 u hu).symm
  exact characteristic_pair_triples T U₀ Q₀ T₀ hUQ inf_le_left inf_le_left hBQ hT hderived hcentral a

/-- The full two-core of the literal original star overgroup is exactly
its intersection with the original ambient two-core. -/
theorem star_core_eq_original_intersection
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hn : Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R))) :
    let T := (starCentralizer R Y).map R.subtype
    let M := K ⊔ T
    (pCore 2 M).map M.subtype = T ⊓ pCore 2 H := by
  obtain ⟨original,hpos,_⟩ := h.positive_even_geometry
  obtain ⟨hnM,hcut,_⟩ := star_pair_core_le h original hpos P Y hY hn
  let T := (starCentralizer R Y).map R.subtype
  let M := K ⊔ T
  have he : (pCore 2 M).map M.subtype = M ⊓ pCore 2 H := by
    rw [pCore_subnormal_eq_comap 2 hnM.isSubnormal,map_comap_eq,range_subtype]
  have hT : (pCore 2 M).map M.subtype ≤ T := by
    have hh := map_mono (f := M.subtype) hcut
    rwa [map_subgroupOf_eq_of_le (show T ≤ M from le_sup_right)] at hh
  exact le_antisymm (le_inf hT (he.le.trans inf_le_right))
    ((le_inf (inf_le_left.trans le_sup_right) inf_le_right).trans_eq he.symm)

/-- The selected marked, saturated star and the same original automorphism
which gives the critical pair satisfy the original moving-module triples.
No saturation of the minimum replacement is used. -/
theorem exists_source_star_original_paired_triples
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    ∃ P : Sylow 2 (Ltilde R (alpha R)), ∃ Y : Subgroup R, ∃ a : MulAut R,
      Y.map (embedS R) = componentSylowSeed R (alpha R) P ∧
      Q R (beta R) ≤ normalizer (Y.map (embedS R) : Set (FreeAmalgam R)) ∧
      d.subgroup ≤ starCentralizer R Y ∧
      (((starCentralizer R Y).map R.subtype).subgroupOf K).map (componentProjection h) =
        (R.subgroupOf K).map (componentProjection h) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       (normalizer (T.subgroupOf M : Set M)).pCoreIn 2 = T.subgroupOf M) ∧
      (let z := act d.radical (minimumAutomorphismElement d a)⁻¹ (alpha d.radical)
       Adjacent d.radical z (beta d.radical) ∧
       ¬ U d.radical z ≤ Q d.radical (alpha d.radical) ∧
       Nonempty (CriticalPath d.radical g (alpha d.radical) z)) ∧
      (let T := (starCentralizer R Y).map R.subtype
       let M := K ⊔ T
       (pCore 2 M).map M.subtype = T ⊓ pCore 2 H) ∧
      (let T := starCentralizer R Y
       let Q₀ := T ⊓ (pCore 2 H).comap R.subtype
       let T₀ := T ⊓ K.comap R.subtype
       let U₀ := ((blockU K).map K.subtype).subgroupOf R
       ⁅U₀.map a.toMonoidHom,T₀⁆ ≤ U₀ ∧
       ⁅U₀,T₀.map a.toMonoidHom⁆ ≤ U₀.map a.toMonoidHom ∧
       ⁅⁅U₀.map a.toMonoidHom,Q₀⁆,T₀⁆ = ⊥ ∧
       ⁅⁅U₀,Q₀.map a.toMonoidHom⁆,T₀.map a.toMonoidHom⁆ = ⊥ ∧
       ⁅U₀,U₀.map a.toMonoidHom⁆ ≤ centralizer (T : Set R)) := by
  obtain ⟨P,Y,a,hY,hn,hmin,hmark,hsat,hcrit,_⟩ :=
    exists_source_star_critical_exchange_control h d g hb hnsyl hne
  obtain ⟨original,hpos,_⟩ := h.positive_even_geometry
  have hrest := (star_radical_saturated_of_marked_image_eq h original hpos P Y hY hn hmark).1
  have forward := star_original_moving_triples h d g hb P Y hY hmin hrest hnsyl a
  have backward := star_original_moving_triples h d g hb P Y hY hmin hrest hnsyl a.symm
  have hcomp : a.toMonoidHom.comp a.symm.toMonoidHom = MonoidHom.id R :=
    MonoidHom.ext a.apply_symm_apply
  have hbmove := map_mono (f := a.toMonoidHom) backward.1
  rw [map_commutator,map_map,hcomp,Subgroup.map_id] at hbmove
  have hbtriple := congrArg (fun J : Subgroup R => J.map a.toMonoidHom) backward.2.1
  rw [map_commutator,map_commutator,map_map,hcomp,Subgroup.map_id,Subgroup.map_bot] at hbtriple
  exact ⟨P,Y,a,hY,hn,hmin,hmark,hsat,hcrit,
    star_core_eq_original_intersection h P Y hY hn,
    forward.1,hbmove,forward.2.1,hbtriple,forward.2.2⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
