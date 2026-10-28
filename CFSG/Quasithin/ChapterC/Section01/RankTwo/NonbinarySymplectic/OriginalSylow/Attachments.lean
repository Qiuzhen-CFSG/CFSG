module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.AttachmentsOverlap
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourEquality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFourEquality

/-!
# Equality of complete fixed attachments for the original Sylow radical

The generic original root geometry identifies an unequal opposite attachment
with the root overlap. Its movement under the actual common radical is both
contained in and disjoint from that attachment, hence trivial. The literal
root-normalizer action would then bound the original marked radical by q
squared, contradicting its Sylow order q to the fourth power.

The complete natural-cover kernels, original radical and original quotient
marking remain present. The internal import reuses the representation-theoretic
root actor bound. Source: MS93 (3.7)(4), printed p.875.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
variable (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include h hshort hinner hsy

omit hshort hsy in
private theorem original_critical_root_overlap_actor_bound
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n)
    (hzero :
      let S := stabilizer R a
      let T := (Q R a ⊔ Z R z).subgroupOf S
      let B := ((normalizer (T : Set S)).pCoreIn 2).map S.subtype
      ⁅U R a ⊓ centralizer
        ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)),
        B ⊓ Q R t⁆=⊥) :
    (Q R a).relIndex (Q R t) ≤ (2^n)^2 := by
  let := h.component_normal
  let q := QuotientGroup.mk' (pCore 2 H)
  let C := K.map q
  let : C.Normal := h.component_image_structure.2.1
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 H)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans h.centralOmega_centralizer.symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : C = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (C) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  rw [h.field_card] at haq hzq
  have hZS : Z R z ≤ stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS κ hκQ).trans (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color)
    h.nonbinary hFc s e he h.component_image_structure.2.2.2.2
    j hj hjr δ (fun x v => hconj (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  let S := stabilizer R a
  have hUS : U R a ≤ S := (U_le_Z a).trans (Z_le_stabilizer R a)
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  have hTS : Q R a ⊔ Z R z ≤ S := sup_le hQS hZS
  let U₀ := (U R a).subgroupOf S
  let T₀ := (Q R a ⊔ Z R z).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U R a
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have haction (x : S) (w : s.space.toSubmodule) :
      jS (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x*jS (Multiplicative.ofAdd w)*x⁻¹ := by
    apply Subtype.ext
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hγβ (x : Z R z) : γ (inclusion hZS x)=β x := by
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hQker : (Q R a).subgroupOf S = γ.ker := by
    rw [hγker,←hκQ,subgroupOf_map_subtype_eq]
  have hZimage : ((Z R z).subgroupOf S).map γ=β.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,hγβ ⟨x.val,hx⟩ |>.symm⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZS x,x.property,hγβ x⟩
  have hTimage : T₀.map γ=β.range := by
    change ((Q R a ⊔ Z R z).subgroupOf S).map γ=β.range
    rw [subgroupOf_sup hQS hZS,Subgroup.map_sup,hQker,
      show γ.ker.map γ=⊥ from (Subgroup.map_eq_bot_iff _).mpr le_rfl,bot_sup_eq,hZimage]
  let := finite_stabilizer R a
  have hγonto : Function.Surjective γ := by
    intro x
    obtain ⟨y,hy⟩ := hκ (e.groupEquiv.symm x).val
    exact ⟨y,(congrArg e.groupEquiv (Subtype.ext hy)).trans (e.groupEquiv.apply_symm_apply x)⟩
  have hγp : IsPGroup 2 γ.ker := by
    rw [←hQker]
    exact (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le
      a path.start_color).comap_subtype
  have hγT : γ.ker ≤ T₀ := by
    rw [←hQker]
    intro x hx
    exact (show Q R a ≤ Q R a ⊔ Z R z from le_sup_left) hx
  have hEdge : Q R t ≤ S := fun _ hx => hx.2 _ (adjacent_symm R hat)
  let J := (Q R t).subgroupOf S
  have hJ : IsPGroup 2 J := by
    have hh : IsPGroup 2 (Q R t) := by
      obtain ⟨u,⟨hau,htu⟩ | ⟨hau,htu⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
      · have ht : hVertex R u = act R u (beta R) := by simp [beta,act_hVertex]
        rw [htu,ht,Q_act,Q_beta]
        exact (h.radical.isPGroup.map _).map _
      · have hc := path.start_color
        rw [hau] at hc
        cases hc
    exact hh.comap_subtype
  have hJT : ⁅J,T₀⁆ ≤ γ.ker := by
    rw [←hQker]
    apply (map_le_map_iff_of_injective S.subtype_injective).mp
    rw [map_commutator,map_subgroupOf_eq_of_le hEdge,
      map_subgroupOf_eq_of_le hTS,map_subgroupOf_eq_of_le hQS,commutator_comm]
    exact commutator_sup_le_of_relative_normal S (Q R a) (Z R z)
      (Q R t) (Q R a) (Q_normalized R a) hQS hZS
      (le_normalizer_iff_commutator_le_left.mp (hEdge.trans (Q_normalized R a)))
      (original_full_radical_centralizes_critical_root h hinner path hb hat hzt hcritical).1
  have hz : ⁅U₀ ⊓ centralizer (T₀ : Set S),(normalizer (T₀ : Set S)).pCoreIn 2 ⊓ J⁆=⊥ := by
    apply map_injective S.subtype_injective
    rw [map_commutator,←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
      map_inf _ _ _ S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS,
      map_subgroupOf_eq_of_le hEdge,Subgroup.map_bot]
    exact hzero
  have hh := SaturatedDistanceTwo.root_overlap_actor_bound hFc h.nonbinary U₀ T₀ J
    (MovedSection.coverProjection s e) he jS
    (fun x y hxy => hj (congrArg Subtype.val hxy)) hjSr γ haction hγonto hγp hγT
    (by rw [hTimage]; exact hβcard) (by rw [hTimage]; exact hβdim)
    (by rw [hTimage]; exact hβquad) hJ hJT hz
  have hc : Nat.card (J.map γ)=(Q R a).relIndex (Q R t) := by
    have hh := Sp4Four.SourceComparison.quotient_image_card _ _ _ hEdge γ
      (by rw [hγker,hκQ])
    rwa [MonoidHom.range_comp,inclusion_range] at hh
  rwa [hc,hFc] at hh

/-- Source (3.7)(4) for an actual critical image of order q: the two
complete moving-cover attachments agree for the original Sylow star. -/
theorem original_source_four_of_field_critical
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
  classical
  by_contra hne
  let S := stabilizer R a
  let T := (Q R a ⊔ Z R z).subgroupOf S
  let B := ((normalizer (T : Set S)).pCoreIn 2).map S.subtype
  let P := B ⊓ Q R t
  let V := Z R a ⊓ Z R z
  let W := ⁅Z R a,Z R z⁆
  let A' := U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R))
  have hC : U R a ⊓ centralizer
      ((Q R a ⊔ Z R z : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) =
      U R a ⊓ centralizer (Z R z : Set (FreeAmalgam R)) := by
    apply le_antisymm (inf_le_inf_left _ (centralizer_le
      (show Z R z ≤ Q R a ⊔ Z R z from le_sup_right)))
    apply le_inf inf_le_left
    apply le_centralizer_iff.mpr
    refine sup_le ?_ (le_centralizer_iff.mp inf_le_right)
    exact le_centralizer_iff.mp ((inf_le_left.trans (U_le_Z a)).trans
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a path.start_color)))
  have he : A' = ⁅U R a ⊓ centralizer
      (Z R z : Set (FreeAmalgam R)),B⁆ := by
    have hh := original_critical_opposite_fixed_eq_root_overlap h hshort hinner path hb hat hzt hcritical hne
    dsimp only at hh
    rwa [hC] at hh
  obtain ⟨⟨_,_,hDW⟩,_⟩ := original_critical_root_overlap_geometry h hshort hinner path hb hat hzt hcritical
  rw [hC] at hDW
  have hm : ⁅U R a ⊓ centralizer
      (Z R z : Set (FreeAmalgam R)),P⁆ ≤ W :=
    (commutator_mono le_rfl inf_le_left).trans hDW
  have hVm : ⁅V,P⁆=⁅U R a ⊓ centralizer
      (Z R z : Set (FreeAmalgam R)),P⁆ :=
    original_critical_common_overlap_movement h hshort hinner hsy g hb path hat hzt hcritical P inf_le_right
  obtain ⟨B₀,hB₀,hmem,_,_,hdis⟩ :=
    original_source_four_common_overlap_centralizer h hshort hinner hsy g hb path hat hzt hcritical
  have hPB : P ≤ B₀ := by
    intro b hbP
    refine (hmem b).mpr ⟨hbP.2,?_⟩
    have hh : ⁅P,V⁆ ≤ W := by rw [commutator_comm,hVm]; exact hm
    exact fun v hv => commutator_le.mp hh b hbP v hv
  have hdisP : Disjoint ⁅V,P⁆ A' := hdis.mono_left (commutator_mono le_rfl hPB)
  have hleA : ⁅V,P⁆ ≤ A' := by
    rw [hVm,he]
    exact commutator_mono le_rfl inf_le_left
  have hz : ⁅V,P⁆=⊥ := by
    apply le_bot_iff.mp
    exact (le_inf le_rfl hleA).trans (disjoint_iff_inf_le.mp hdisP)
  have hbnd := original_critical_root_overlap_actor_bound h hinner path hb hat hzt hcritical (by
    dsimp only
    rw [hC]
    exact hVm.symm ▸ hz)
  rw [original_sylow_full_radical_card h hinner hsy path.start_color hat] at hbnd
  have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
  exact (not_le_of_gt (Nat.pow_lt_pow_right hq (by decide : 2 < 4))) hbnd


/-- MS93 (3.7)(4) on the literal original Sylow star: complete fixed
attachments agree at every critical pair. -/
theorem original_source_four_fixed_attachments
    (g : Geometry R) (hb : g.b R=2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
  exact original_source_four_of_field_critical h hshort hinner hsy g hb path hat hzt
    (original_critical_indices_eq_field_of_full_sylow h hshort hinner hsy path hb hat hzt).1

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
