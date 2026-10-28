module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoPointDisplacement
public import Theory.Representation.SymplecticFourOrthogonalCover.RootNormalizerFixed
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.TwoNormalizer
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore

/-!
# Full original radical centrality at a field-sized critical image

The original critical image is a full root in the same natural cover as the
endpoint action. The full midpoint radical normalizes it and, as a two-group,
centralizes it. Fixed-vector lifting centralizes the complete covered moving
commutator as well. The entire original endpoint kernel is retained.

Source: MS93 (3.7)(1), printed p.873, the order-q branch.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource OriginalStar
open Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hinner : K ⊔ pCore 2 H = ⊤)
include h hinner

private theorem critical_root_full_radical
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    ⁅Z R z,Q R t⁆ ≤ Q R a ∧
      Q R t ≤ centralizer
        ((⁅U R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  let := h.component_image_structure.2.1
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : K.map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (K.map (QuotientGroup.mk' (pCore 2 H))) (fun x => hCtop ▸ mem_top (κ x))
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
  have hTS : Q R t ≤ S := (original_edge_le_stabilizer R hat)
  let U₀ := (U R a).subgroupOf S
  let T₀ := (Q R t).subgroupOf S
  let A₀ := (Z R z).subgroupOf S
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

  have hn : T₀ ≤ normalizer (A₀ : Set S) := by
    apply (comap_mono ((original_edge_le_stabilizer R hzt).trans (Z_normalized R z))).trans
    exact le_normalizer_comap S.subtype
  have hP : IsPGroup 2 T₀ := by
    have hp : IsPGroup 2 (Q R t) := by
      obtain ⟨u,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
      swap
      · cases path.start_color
      have he := Q_act R u (beta R)
      simp only [beta,act_hVertex,one_mul] at he
      rw [he]
      change IsPGroup 2 ((Q R (beta R)).map _)
      rw [Q_beta]
      exact (h.radical.isPGroup.map (embedM R)).map _
    exact hp.comap_subtype
  have hTmap : T₀.map S.subtype = Q R t := map_subgroupOf_eq_of_le hTS
  have hAmap : A₀.map S.subtype = Z R z := map_subgroupOf_eq_of_le hZS
  have hfixed := embedded_two_normalizer_centralizes_displacement U₀ A₀ T₀ hP hn
    (MovedSection.coverProjection s e) he jS hjSr γ haction
    (by rw [hZimage]; exact hβdim.le)
  have hh := (map_mono (f := S.subtype) hfixed).trans
    (map_centralizer_le_centralizer_image _ S.subtype)
  rw [hTmap,←coe_map,map_commutator,map_subgroupOf_eq_of_le hUS,hAmap] at hh
  refine ⟨?_,hh⟩
  let f := (commutator (Sp E.Carrier)).subtype.comp γ
  have hfg : f.ker=γ.ker := MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective
  have hAf : A₀.map f=β.range.map (commutator (Sp E.Carrier)).subtype := by
    rw [←map_map,hZimage]
  have hc : T₀.map f ≤ centralizer (A₀.map f : Set (Sp E.Carrier)) := by
    apply two_subgroup_normalizing_displacement_line_centralizes _ _ (hP.map f)
      ((map_mono hn).trans (le_normalizer_map f))
    · rw [hAf,card_map_of_injective (commutator (Sp E.Carrier)).subtype_injective]
      exact hβcard
    · rw [hAf]
      exact hβdim
    · rw [hAf]
      exact hβquad
  have hk : ⁅A₀,T₀⁆ ≤ γ.ker := by
    rw [←hfg]
    change ⁅A₀,T₀⁆ ≤ (⊥ : Subgroup (Sp E.Carrier)).comap f
    rw [←map_le_iff_le_comap,map_commutator]
    exact (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)).le
  have hm := map_mono (f := S.subtype) hk
  rw [map_commutator,hAmap,hTmap,←hQker,map_subgroupOf_eq_of_le hQS] at hm
  exact hm

/-- With an actual critical image of order q, the whole common radical
centralizes that image and the full covered moving commutator. This
includes the Sylow alternative and retains the original core kernel. -/
theorem original_full_radical_centralizes_critical_root
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a) = 2^n) :
    ⁅Z R z,Q R t⁆ ≤ Q R a ∧
      ⁅Z R a,Q R t⁆ ≤ Q R z ∧
      Q R t ≤ centralizer
        ((⁅U R a,Z R z⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
      Q R t ≤ centralizer
        ((⁅U R z,Z R a⁆ : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hzq := (h.original_small_critical_indices_eq_field path (by omega) (by
    rw [hcritical,h.field_card]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2.trans h.field_card
  have h1 := critical_root_full_radical h hinner path hb hat hzt hcritical
  have h2 := critical_root_full_radical h hinner rev hb hzt hat hzq
  exact ⟨h1.1,h2.1,h1.2,h2.2⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
