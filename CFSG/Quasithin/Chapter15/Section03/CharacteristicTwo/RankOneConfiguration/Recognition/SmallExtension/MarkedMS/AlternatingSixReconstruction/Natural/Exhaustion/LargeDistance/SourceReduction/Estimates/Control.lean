module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.CriticalImages
public import Theory.GroupTheory.Commutator.NormalClosure
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# The complete derived critical estimates

The actual opposite endpoint image is a self-centralizing even four-group.
The source Frattini condition forces Y to centralize the initial X-layer;
at the far vertex this puts Y in that X-layer times the far two-core.
The core centralizes the far X-layer, giving the source commutator bound
without a separate source-(3.3) hypothesis.

Uniqueness of the endpoint offender makes its image normal in the first
edge and common to every critical endpoint through that edge. These facts
lift to the literal X-commutator. Vertex normality would force its nonzero
quadratic action to vanish by simple-quotient normal generation and
p-residual commutator idempotence. Thus all of (2.3)(c,d) hold on the
original characteristic replacement. The final application supplies
distance four, critical escape and relative midpoint normality.

No natural subgroup, split cover, full symmetric action or Sylow radical
is assumed. Source: MS93 (2.3), pp.857--859, and the first paragraph of
(3.8), p.877. The remaining radius-two contradiction and Section5 argument
belong to the same final owner, qt-e-ms-small-a6-exhaustion-large-distance.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  (h : SmallMSPair κ L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)
local notation "π" => projection h e hz hn d

private theorem reverse_pair
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    CriticalPair d.radical b a ((replacementGeometry h d).exists_critical b
      (critical_endpoint_color d.radical a ha _ hc)) := by
  apply critical_reverse d.radical (replacementGeometry h d)
    (edgeCentralizerCondition h e hz hn d himage) a ha _ b
      (critical_endpoint_color d.radical a ha _ hc) hc
  rw [(replacementGeometry h d).distance_constant a ha]
  exact replacementDistance_pos h d

private theorem endpoint_le_stabilizer
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    X d.radical b ≤ stabilizer d.radical a := by
  obtain ⟨t,hat,ht⟩ := exists_adjacent_dist_sub_one d.radical a b (by
    rw [hc.1,(replacementGeometry h d).distance_constant a ha]
    exact replacementDistance_pos h d)
  exact (critical_edge_data h e hz hn d himage a ha b hc t hat ht).1.trans
    (CriticalCriterion.edge_le_stabilizer d.radical ha hat)

private theorem commutator_join_kernel
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    ⁅X d.radical a,X d.radical b⁆ = ⁅X d.radical a,X d.radical b ⊔ Q d.radical a⁆ :=
  commutator_eq_of_centralizing_sup (sup_comm _ _) (Q_le_centralizer_X d.radical a)
    ((endpoint_le_stabilizer h e hz hn d himage a ha b hc).trans (X_normalized d.radical a))

/-- The source's auxiliary subgroup is normal relative to the literal edge kernel. -/
theorem critical_commutator_normal_edge
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hat : Adjacent d.radical a t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist a b) :
    ((⁅X d.radical a,X d.radical b⁆).subgroupOf (Q d.radical t)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [commutator_join_kernel h e hz hn d himage a ha b hc]
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (critical_join_normalized h e hz hn d himage a ha b hc t hat ht hg),
    mem_normalizer_iff_map_conj_eq.mp (X_normalized d.radical a
      (CriticalCriterion.edge_le_stabilizer d.radical ha hat hg))]

/-- All critical pairs through the same oriented edge have exactly the same
auxiliary commutator, not just a common abstract isomorphism type. -/
theorem critical_commutator_common
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hat : Adjacent d.radical a t)
    (ht : (cosetGraph d.radical).dist t b + 1 = (cosetGraph d.radical).dist a b)
    (c : Vertex d.radical)
    (hcc : CriticalPair d.radical a c ((replacementGeometry h d).exists_critical a ha))
    (htc : (cosetGraph d.radical).dist t c + 1 = (cosetGraph d.radical).dist a c) :
    ⁅X d.radical a,X d.radical b⁆ = ⁅X d.radical a,X d.radical c⁆ := by
  rw [commutator_join_kernel h e hz hn d himage a ha b hc,
    critical_join_common h e hz hn d himage a ha b hc t hat ht c hcc htc,
    ← commutator_join_kernel h e hz hn d himage a ha c hcc]

/-- The actual source Frattini premise forces the actor to centralize X. -/
theorem frattini_join_centralizes
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hbt : Adjacent d.radical b t)
    (ht : (cosetGraph d.radical).dist a t + 1 = (cosetGraph d.radical).dist a b)
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ Q d.radical t)
    (hPhi : frattini (Y ⊔ X d.radical a : Subgroup (FreeAmalgam d.radical)) = ⊥) :
    Y ≤ centralizer (X d.radical a : Set (FreeAmalgam d.radical)) := by
  have hbcol := critical_endpoint_color d.radical a ha _ hc
  have hrev := reverse_pair h e hz hn d himage a ha b hc
  have hX : X d.radical a ≤ Q d.radical t :=
    (critical_edge_data h e hz hn d himage b hbcol a hrev t hbt (by
      simpa only [SimpleGraph.dist_comm] using ht)).1
  have htcol : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hbt
    cases hh' : color d.radical t <;> simp_all
  have hpT : IsPGroup 2 (Q d.radical t) := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common d.radical b t).mp hbt
    · rw [hg.2]
      have hh := Q_act d.radical g (beta d.radical)
      simp only [beta,act_hVertex,one_mul] at hh
      rw [hh]
      change IsPGroup 2 ((Q d.radical (beta d.radical)).map _)
      rw [Q_beta]
      exact ((replacement_radical_isPGroup h d).map (embedM d.radical)).map _
    · rw [hg.1] at hbcol
      cases hbcol
  have hJ : Y ⊔ X d.radical a ≤ Q d.radical t := sup_le hY hX
  let := finite_stabilizer d.radical t
  let : Finite (Y ⊔ X d.radical a : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hJ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  let : Fact (IsPGroup 2 (Y ⊔ X d.radical a : Subgroup (FreeAmalgam d.radical))) :=
    ⟨hpT.to_le hJ⟩
  let := (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hPhi
  intro y hy x hx
  exact congrArg Subtype.val (mul_comm
    (⟨x,mem_sup_right hx⟩ : (Y ⊔ X d.radical a : Subgroup (FreeAmalgam d.radical)))
    ⟨y,mem_sup_left hy⟩)

/-- Self-centralization of the actual endpoint image proves the required
far-endpoint bound directly under the literal Frattini premise. -/
theorem critical_commutator_bound
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha))
    (t : Vertex d.radical) (hbt : Adjacent d.radical b t)
    (ht : (cosetGraph d.radical).dist a t + 1 = (cosetGraph d.radical).dist a b)
    (Y : Subgroup (FreeAmalgam d.radical)) (hY : Y ≤ Q d.radical t)
    (hPhi : frattini (Y ⊔ X d.radical a : Subgroup (FreeAmalgam d.radical)) = ⊥) :
    ⁅Y,X d.radical b⁆ ≤ ⁅X d.radical a,X d.radical b⁆ := by
  have hbcol := critical_endpoint_color d.radical a ha _ hc
  have hrev := reverse_pair h e hz hn d himage a ha b hc
  have hC := frattini_join_centralizes h e hz hn d himage a ha b hc t hbt ht Y hY hPhi
  have hYS : Y ≤ stabilizer d.radical b :=
    hY.trans (CriticalCriterion.edge_le_stabilizer d.radical hbcol hbt)
  have hJ : Y ≤ X d.radical a ⊔ Q d.radical b :=
    (le_inf hYS hC).trans (critical_centralizer_le_join h e hz hn d himage b hbcol a hrev)
  rw [commutator_comm Y,commutator_comm (X d.radical a),
    commutator_join_kernel h e hz hn d himage b hbcol a hrev]
  exact commutator_mono le_rfl hJ

private theorem native_quadratic_not_normal
    (himage : (π).range = alternatingGroup (Fin 6))
    (W A : Subgroup d.overgroup) [W.Normal] (hpW : IsPGroup 2 W)
    (hcore : pCore 2 d.overgroup ≤ centralizer (W : Set d.overgroup))
    (hA : ¬ A ≤ pCore 2 d.overgroup) (hquad : ⁅W,A⁆ ≤ centralizer (A : Set d.overgroup))
    (hne : ⁅W,A⁆ ≠ ⊥) : ¬ (⁅W,A⁆).Normal := by
  intro hD
  let D := ⁅W,A⁆
  let : D.Normal := hD
  let N := normalClosure (A : Set d.overgroup)
  let q : d.overgroup →* alternatingGroup (Fin 6) :=
    (π).codRestrict _ (fun m => himage ▸ ⟨m,rfl⟩)
  have hq : Function.Surjective q := by
    intro y
    have hy : (y : Equiv.Perm (Fin 6)) ∈ (π).range := by rw [himage]; exact y.property
    obtain ⟨m,hm⟩ := hy
    exact ⟨m,Subtype.ext hm⟩
  have hk : q.ker = pCore 2 d.overgroup := by
    rw [← projection_kernel h e hz hn d]
    ext m
    exact Subtype.ext_iff
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : (N.map q).Normal := Normal.map inferInstance q hq
  have htop : N.map q = ⊤ := by
    rcases (inferInstance : (N.map q).Normal).eq_bot_or_eq_top with hzN | htN
    · exact False.elim (hA (le_normalClosure.trans (by
        simpa only [hk] using (Subgroup.map_eq_bot_iff N).mp hzN)))
    · exact htN
  have hNQ : N ⊔ pCore 2 d.overgroup = ⊤ := by
    have hh := congrArg (Subgroup.comap q) htop
    simpa only [comap_map_eq,hk,comap_top] using hh
  have hKN : pResidual 2 d.overgroup ≤ N :=
    le_normal_of_isPPerfect_of_le_sup_pGroup (pResidual 2 d.overgroup) N
      (pCore 2 d.overgroup) (isPPerfect_pResidual 2) pCore_isPGroup (hNQ ▸ le_top)
  have hNC : N ≤ centralizer (D : Set d.overgroup) :=
    normalClosure_le_normal (fun _ ha => (le_centralizer_iff.mp hquad) ha)
  have hWD : ⁅W,pResidual 2 d.overgroup⁆ ≤ D :=
    (commutator_mono le_rfl hKN).trans
      (commutator_normalClosure_le_of_normal W A D le_rfl)
  have hWK : ⁅W,pResidual 2 d.overgroup⁆ = ⊥ := by
    have hid := commutator_isPPerfect_idempotent (pResidual 2 d.overgroup) W
      (isPPerfect_pResidual 2) hpW le_normalizer_of_normal
    apply le_bot_iff.mp
    rw [← hid]
    exact (commutator_mono hWD le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr
        (le_centralizer_iff.mp (hKN.trans hNC))).le
  have hKQ : pResidual 2 d.overgroup ⊔ pCore 2 d.overgroup = ⊤ := by
    rw [replacement_residual h d]
    apply top_unique
    intro x _
    have hx : π x ∈ (replacementComponent d).map π := by
      rw [component_image,← himage]
      exact ⟨x,rfl⟩
    have hh : x ∈ ((replacementComponent d).map π).comap π := hx
    rwa [comap_map_eq,projection_kernel] at hh
  have hall : (⊤ : Subgroup d.overgroup) ≤ centralizer (W : Set d.overgroup) := by
    rw [← hKQ]
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hWK)) hcore
  exact hne (commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (le_top.trans hall)))

include h in
private theorem local_embedding (a : Vertex d.radical) (ha : color d.radical a = false) :
    ∃ f : d.overgroup →* FreeAmalgam d.radical, Function.Injective f ∧
      f.range = stabilizer d.radical a ∧ (pCore 2 d.overgroup).map f = Q d.radical a := by
  obtain ⟨g,rfl⟩ := exists_mVertex_of_color d.radical ha
  refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical),
    (MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical), ?_, ?_⟩
  · rw [MonoidHom.range_comp]
    exact (stabilizer_mVertex d.radical g).symm
  · rw [← Subgroup.map_map,← Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    have hh := Q_act d.radical g (alpha d.radical)
    simpa only [alpha,act_mVertex,one_mul] using hh.symm

/-- Vertex normality of the critical commutator would make its nonzero
quadratic action trivial, by normal generation in the actual simple quotient. -/
theorem critical_commutator_not_normal_vertex
    (himage : (π).range = alternatingGroup (Fin 6))
    (a : Vertex d.radical) (ha : color d.radical a = false) (b : Vertex d.radical)
    (hc : CriticalPair d.radical a b ((replacementGeometry h d).exists_critical a ha)) :
    ¬ ((⁅X d.radical a,X d.radical b⁆).subgroupOf (stabilizer d.radical a)).Normal := by
  obtain ⟨f,hf,hrange,hcore⟩ := local_embedding h d a ha
  have hX : X d.radical a ≤ stabilizer d.radical a :=
    (omegaCenter_le _).trans (fun _ hx => hx.1)
  have hA := endpoint_le_stabilizer h e hz hn d himage a ha b hc
  let W := (X d.radical a).comap f
  let A := (X d.radical b).comap f
  have hWmap : W.map f = X d.radical a := by
    rw [map_comap_eq,hrange,inf_eq_right.mpr hX]
  have hAmap : A.map f = X d.radical b := by
    rw [map_comap_eq,hrange,inf_eq_right.mpr hA]
  let : W.Normal := by
    constructor
    intro w hw m
    change f (m*w*m⁻¹) ∈ X d.radical a
    simpa only [map_mul,map_inv] using le_normalizer_iff.mp
      (X_normalized d.radical a) (f m) (hrange ▸ ⟨m,rfl⟩) (f w) hw
  have hpW : IsPGroup 2 W := pCore_isPGroup.to_le (by
    apply (Subgroup.map_le_map_iff_of_injective hf).mp
    rw [hWmap,hcore]
    exact omegaCenter_le _)
  have hDmap : (⁅W,A⁆).map f = ⁅X d.radical a,X d.radical b⁆ := by
    rw [map_commutator,hWmap,hAmap]
  have hCA : pCore 2 d.overgroup ≤ centralizer (W : Set d.overgroup) := by
    intro q hq w hw
    apply hf
    simpa only [map_mul] using (Q_le_centralizer_X d.radical a
      (hcore ▸ mem_map_of_mem f hq)) (f w) hw
  have hAout : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    have hbcol := critical_endpoint_color d.radical a ha _ hc
    have hZ := (replacementGeometry h d).omega_bound b hbcol (by
      rw [(replacementGeometry h d).distance_constant b hbcol]
      exact replacementDistance_pos h d)
    exact (reverse_pair h e hz hn d himage a ha b hc).2
      (hZ.trans (hAmap ▸ hcore ▸ map_mono hh))
  have hDle := (critical_X_commutator h d e hz hn himage a ha b hc).1
  have hquad : ⁅W,A⁆ ≤ centralizer (A : Set d.overgroup) := by
    intro x hx y hy
    apply hf
    have hx' : f x ∈ X d.radical b := (hDle (hDmap ▸ mem_map_of_mem f hx)).2
    have hcomm := (mem_omegaCenter_iff.mp hx').2.2 (f y) (omegaCenter_le _ hy)
    simpa only [map_mul] using hcomm
  have hne : ⁅W,A⁆ ≠ ⊥ := by
    intro hh
    exact (critical_X_commutator h d e hz hn himage a ha b hc).2
      (by rw [← hDmap,hh,Subgroup.map_bot])
  intro hnorm
  apply native_quadratic_not_normal h e hz hn d himage W A hpW hCA hAout hquad hne
  have hnorm' := (normal_subgroupOf_iff_le_normalizer (hDle.trans inf_le_left |>.trans hX)).mp hnorm
  constructor
  intro x hx m
  apply (mem_map_iff_mem hf).mp
  rw [hDmap]
  simpa only [map_mul,map_inv] using le_normalizer_iff.mp hnorm'
    (f m) (hrange ▸ ⟨m,rfl⟩) (f x) (hDmap ▸ mem_map_of_mem f hx)

/-- The complete source-(2.3)(c,d) estimates on the original replacement. -/
theorem criticalEstimates
    (himage : (π).range = alternatingGroup (Fin 6)) : CriticalEstimates h d := by
  refine ⟨?_, ?_⟩
  · intro a ha b hc
    refine ⟨X d.radical b, le_rfl, ?_, ?_⟩
    · have hrev := reverse_pair h e hz hn d himage a ha b hc
      have hbcol := critical_endpoint_color d.radical a ha _ hc
      have hZ := (replacementGeometry h d).omega_bound b hbcol (by
        rw [(replacementGeometry h d).distance_constant b hbcol]
        exact replacementDistance_pos h d)
      exact fun hh => hrev.2 (hZ.trans hh)
    · intro t ht Y hY hPhi
      exact (critical_commutator_bound h e hz hn d himage a ha b hc t ht.1 ht.2 Y hY hPhi).trans
        le_sup_left
  · intro a ha b hc t hat ht
    refine ⟨(critical_X_commutator h d e hz hn himage a ha b hc).1.trans inf_le_left,
      critical_commutator_normal_edge h e hz hn d himage a ha b hc t hat ht,
      critical_commutator_not_normal_vertex h e hz hn d himage a ha b hc, ?_⟩
    intro ha' c hcc htc
    have hdist : (cosetGraph d.radical).dist a c = (replacementGeometry h d).b d.radical :=
      hcc.1.trans ((replacementGeometry h d).distance_constant a ha')
    exact (critical_commutator_common h e hz hn d himage a ha b hc t hat ht c hcc
      (htc.trans hdist.symm)).le

/-- The actual A₆ replacement now has distance four, escape and midpoint
normality, with no missing critical-estimate callback. -/
theorem fourGeometry_of_alternating
    (himage : (π).range = alternatingGroup (Fin 6))
    (hb : 2 < replacementDistance h d) : FourGeometry h d :=
  fourGeometry h e hz hn d himage hb (criticalEstimates h e hz hn d himage)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
