module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.CriticalLayers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.ComponentIntersection
public import Theory.Representation.SymplecticFourOrthogonalCover.RootNormalizerFixed
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.TwoNormalizer

/-!
# The full radical normalizes an actual critical root

When the critical Z-image has order q, reciprocal critical indices identify
it with a full long root in the same natural cover used by the whole vertex
stabilizer. The common radical normalizes that root because it normalizes
the opposite Z-layer. A two-group normalizing a full root centralizes it,
so its mixed commutator lies in the entire original endpoint kernel.

The radical also fixes the root displacement line. Fixed-vector lifting
through the original symplectic cover then centralizes the full moving
commutator, including its central covering kernel. On both sides this puts
the T₀-displacements in U and makes their following Q-commutators trivial.
Using Z = U Z_t, the complete critical commutator lies in the actual
midpoint omega-center.

This proves the component-displacement clause of MS93 (3.7)(1), printed
p.873, for an order-q critical image in all full-radical alternatives,
including Sylow. It does not prove the reversed triples or the large-image
Sylow case. The critical image of order q must still be constructed by
(3.7)(6); the full radical is never assumed to have that order.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource
open Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem critical_root_full_radical
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    ⁅Z d.radical z,Q d.radical t⁆ ≤ Q d.radical a ∧
      Q d.radical t ≤ centralizer
        ((⁅U d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.start_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop : replacementComponent d = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 d.overgroup)
    have hh := congrArg (fun A : Subgroup d.overgroup => A.map q)
      (replacement_inner_of_positive h d g (by omega))
    rw [Subgroup.map_sup,show (pCore 2 d.overgroup).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (replacementComponent d) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  obtain ⟨haq,hzq⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)
  have hZS : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZS)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZS κ hκQ).trans (hzq.trans hFc.symm)
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ (fun x v => hconj (inclusion hZS x) v) hδcard (haq.trans hFc.symm)
  let S := stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQS : Q d.radical a ≤ S := fun _ hx => hx.1
  have hTS : Q d.radical t ≤ S := c.edge_le
  let U₀ := (U d.radical a).subgroupOf S
  let T₀ := (Q d.radical t).subgroupOf S
  let A₀ := (Z d.radical z).subgroupOf S
  let jS := j.codRestrict S (fun w => hUS (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  have hjSr : jS.range=U₀ := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      change j w ∈ U d.radical a
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
  have hγβ (x : Z d.radical z) : γ (inclusion hZS x)=β x := by
    exact (congrArg e.groupEquiv
      (show κC (inclusion hZS x)=e.groupEquiv.symm (β x) from
        Subtype.ext (hβmark x).symm)).trans (e.groupEquiv.apply_symm_apply _)
  have hQker : (Q d.radical a).subgroupOf S = γ.ker := by
    rw [hγker,←hκQ,subgroupOf_map_subtype_eq]
  have hZimage : ((Z d.radical z).subgroupOf S).map γ=β.range := by
    apply le_antisymm
    · rintro _ ⟨x,hx,rfl⟩
      exact ⟨⟨x.val,hx⟩,hγβ ⟨x.val,hx⟩ |>.symm⟩
    · rintro _ ⟨x,rfl⟩
      exact ⟨inclusion hZS x,x.property,hγβ x⟩

  have hn : T₀ ≤ normalizer (A₀ : Set S) := by
    apply (comap_mono (c'.edge_le.trans (Z_normalized d.radical z))).trans
    exact le_normalizer_comap S.subtype
  have hP : IsPGroup 2 T₀ := by
    have hp : IsPGroup 2 (Q d.radical t) := by
      rw [←c.radical_eq]
      exact (replacement_isPGroup h d).map c.embedding
    exact hp.comap_subtype
  have hTmap : T₀.map S.subtype = Q d.radical t := map_subgroupOf_eq_of_le hTS
  have hAmap : A₀.map S.subtype = Z d.radical z := map_subgroupOf_eq_of_le hZS
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
theorem full_radical_centralizes_critical_root
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    ⁅Z d.radical z,Q d.radical t⁆ ≤ Q d.radical a ∧
      ⁅Z d.radical a,Q d.radical t⁆ ≤ Q d.radical z ∧
      Q d.radical t ≤ centralizer
        ((⁅U d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      Q d.radical t ≤ centralizer
        ((⁅U d.radical z,Z d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hzq := (replacement_critical_indices_eq_field_of_small h d path (by omega) (by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith)).2
  have h1 := critical_root_full_radical h d path hb c c' hcritical
  have h2 := critical_root_full_radical h d rev hb c' c hzq
  exact ⟨h1.1,h2.1,h1.2,h2.2⟩

/-- The component displacement clause of (3.7)(1) and the midpoint
containment of the critical commutator, with no parabolic restriction.
The order-q premise is on the critical Z-image, never on the full radical. -/
theorem critical_root_component_displacements
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    ⁅Z d.radical z,componentRadical d a t⁆ ≤ U d.radical a ∧
      ⁅⁅Z d.radical z,componentRadical d a t⁆,Q d.radical a⁆ = ⊥ ∧
      ⁅Z d.radical a,componentRadical d z t⁆ ≤ U d.radical z ∧
      ⁅⁅Z d.radical a,componentRadical d z t⁆,Q d.radical z⁆ = ⊥ ∧
      ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical t := by
  have hZaT : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1 < g.b d.radical
    omega
  have hZzT : Z d.radical z ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b d.radical
    omega
  obtain ⟨hza,haz,hmove,_⟩ := full_radical_centralizes_critical_root h d path hb c c' hcritical
  have hUa : ⁅Z d.radical z,componentRadical d a t⁆ ≤ U d.radical a := by
    rw [←c.componentRadical_inf_core g hb path.start_color]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp
      (hZzT.trans c.componentRadical_normalized)) ((commutator_mono le_rfl inf_le_left).trans hza)
  have hUz : ⁅Z d.radical a,componentRadical d z t⁆ ≤ U d.radical z := by
    rw [←c'.componentRadical_inf_core g hb path.end_color]
    exact le_inf (le_normalizer_iff_commutator_le_right.mp
      (hZaT.trans c'.componentRadical_normalized)) ((commutator_mono le_rfl inf_le_left).trans haz)
  refine ⟨hUa,commutator_eq_bot_iff_le_centralizer.mpr
    ((hUa.trans (U_le_Z a)).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a path.start_color))),
    hUz,commutator_eq_bot_iff_le_centralizer.mpr
    ((hUz.trans (U_le_Z z)).trans (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z path.end_color))),?_⟩
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases he : color d.radical t <;> simp_all [path.start_color]
  have hZt : Z d.radical t = omegaCenter (Q d.radical t) := by simp [Z,ht,edgeOmega]
  have hcenter : Z d.radical t ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  have hcentral : ⁅Z d.radical a,Z d.radical z⁆ ≤
      centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    rw [Z_eq_moving_sup_edge_of_critical_index h d path hb hat hcritical]
    apply commutator_sup_le_of_relative_normal (Q d.radical t) _ _ _ _
      ((Q d.radical t).le_normalizer.trans (normalizer_le_normalizer_centralizer _)) ((U_le_Z a).trans hZaT)
      (hZt ▸ omegaCenter_le _) (le_centralizer_iff.mp hmove)
    exact (commutator_eq_bot_iff_le_centralizer.mpr
      (hcenter.trans (centralizer_le hZzT))).le.trans bot_le
  have hRa : ⁅Z d.radical a,Z d.radical z⁆ ≤ Z d.radical a := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_right.mp
      (hZzT.trans (c.edge_le.trans (Z_normalized d.radical a)))
  have hZaX := g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]
    change 0 < g.b d.radical
    omega)
  rw [hZt]
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZaT (hRa hx),
    (mem_omegaCenter_iff.mp (hZaX (hRa hx))).2.1,hcentral hx⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
