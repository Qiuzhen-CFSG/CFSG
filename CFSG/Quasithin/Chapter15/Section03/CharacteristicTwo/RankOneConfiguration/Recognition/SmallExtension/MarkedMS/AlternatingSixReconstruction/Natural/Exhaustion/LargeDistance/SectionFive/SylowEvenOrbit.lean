module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowKernelPair
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowNormalizer
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowActor
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowMovingLine

/-!
# Even actors from moving critical lines

Above distance four, let T be the first-edge relative normalizer inside the
starting stabilizer, E the T-orbit of the full endpoint seed, and W = [E,T].
If T moves a small critical line, W escapes the starting two-core: otherwise
T would normalize the critical commutator, whose order two makes T fix it.
The actual symmetric image of W is an even two-group. Cauchy's theorem gives
an even involution in that image, without asserting an involutory lift.

The orbit normality and its previously proved quadratic action put W inside
E and retain quadratic action on the entire starting seed. The even image
supplies an actual neighboring edge whose relative normalizer generates the
starting stabilizer with W. Transport carries the critical path, the whole
endpoint orbit and this generation equation to every original component
vertex. The final application uses the literal restriction of the original
Sylow subgroup, identified with T by the proved radical-normalizer equality.
Both moving covers and their full central attachments are retained.

This supplies the even actor and neighboring-edge generation in the moving
small-line branch. The predecessor-radius commutator estimate, non-elementary
shifts and terminal exclusions remain to be established.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the local generation and backward-selection arguments in (5.5)--(5.8),
printed pp.915--920. The actor construction uses the actual relative
normalizer and full endpoint orbit from `SylowKernelPair`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowEvenOrbit

private theorem map_orbit {H K : Type*} [Group H] [Group K]
    (A T : Subgroup H) (f : H →* K) :
    (componentOrbit A T).map f = componentOrbit (A.map f) (T.map f) := by
  change (⨆ t : T, A.map (MulAut.conj (t : H)).toMonoidHom).map f = _
  rw [←conjugateSpanBy_eq_iSup_conj,map_conjugateSpanBy,conjugateSpanBy_eq_iSup_conj]
  rfl

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- Movement of the critical line forces the endpoint-orbit commutator
outside the actual starting two-core. -/
theorem moving_orbit_commutator_not_le_core_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a) ≤ centralizer
        ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let E := componentOrbit (Z d.radical a') T
    ¬ ⁅E,T⁆ ≤ Q d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  let E := componentOrbit (Z d.radical a') T
  change ¬ ⁅E,T⁆ ≤ Q d.radical a
  intro hcore
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ p.start_color
    (by rw [(replacementGeometry h d).distance_constant _ p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hcomm : ⁅T,Z d.radical a'⁆ ≤ centralizer (Z d.radical a : Set _) := by
    rw [commutator_comm]
    exact ((commutator_mono (le_componentOrbit _ _) le_rfl).trans hcore).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
  have hnorm : T ≤ normalizer ((⁅Z d.radical a,Z d.radical a'⁆ :
      Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rw [commutator_comm (Z d.radical a)]
    exact SylowNormalizer.fixed_mod_central_normalizes (Z d.radical a') (Z d.radical a) T
      (hAG.trans (Z_normalized d.radical a))
      (inf_le_right.trans (Z_normalized d.radical a)) hcomm
  exact hmove (hnorm.trans (normalizer_le_centralizer_of_card_two _
    (small_critical_commutator_card s hc p hsmall)))

include e hz hn in
/-- The actual orbit commutator acts quadratically on the full seed and
has an even involution in its literal symmetric quotient image. -/
theorem moving_base_orbit_even_actor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ≤ centralizer
        ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)
    let E := componentOrbit (Z d.radical a') T
    let W := ⁅E,T⁆
    W ≤ E ∧ W ≤ stabilizer d.radical (alpha d.radical) ∧
      ⁅⁅Z d.radical (alpha d.radical),W⁆,W⁆ = ⊥ ∧
      ∃ x ∈ graphImage (fullSymmetricAction_knownSimple h e hz hn d (by omega)) W,
        orderOf x = 2 ∧ x ∈ alternatingGroup (Fin 6) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  let E := componentOrbit (Z d.radical a') T
  let W := ⁅E,T⁆
  let f := embedM d.radical
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  have hAG := critical_Z_le_stabilizer d.radical (replacementGeometry h d) _ rfl
    (replacementDistance_pos h d) p.critical
  have hAT : Z d.radical a' ≤ T := le_inf
    (((le_componentOrbit _ _).trans hi.1).trans (Q d.radical (p.walk.getVert 1)).le_normalizer) hAG
  have hET : E ≤ T := (componentOrbit_le_sup _ _).trans (sup_le hAT le_rfl)
  have hWE : W ≤ E := le_normalizer_iff_commutator_le_left.mp hi.2.1
  have hWG : W ≤ stabilizer d.radical (alpha d.radical) := hWE.trans (hET.trans inf_le_right)
  have hmE : (E.comap f).map f = E := map_comap_eq_self
    ((hET.trans inf_le_right).trans_eq (stabilizer_m_base d.radical))
  have hmT : (T.comap f).map f = T := map_comap_eq_self
    ((show T ≤ stabilizer d.radical (alpha d.radical) from inf_le_right).trans_eq
      (stabilizer_m_base d.radical))
  have hmW : (W.comap f).map f = W := map_comap_eq_self
    (hWG.trans_eq (stabilizer_m_base d.radical))
  have hcomap : W.comap f = ⁅E.comap f,T.comap f⁆ := by
    apply map_injective (embedM_injective d.radical)
    rw [hmW,map_commutator,hmE,hmT]
  have heven : graphImage s W ≤ alternatingGroup (Fin 6) := by
    rw [graphImage,hcomap,map_commutator]
    exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
  have hpT := SylowMovingLine.first_edge_normalizer_isPGroup
    (e := e) (hz := hz) (hn := hn) hb p
  have hpW : IsPGroup 2 (graphImage s W) :=
    ((hpT.comap_of_injective f (embedM_injective d.radical)).of_injective
      (inclusion (comap_mono (hWE.trans hET))) (inclusion_injective _)).map s.projection
  have hnW : graphImage s W ≠ ⊥ := by
    intro hh
    have hker : W.comap f ≤ s.projection.ker := (Subgroup.map_eq_bot_iff _).mp hh
    rw [s.projection_kernel] at hker
    have hWQ := map_mono (f := f) hker
    rw [hmW,←Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)] at hWQ
    exact moving_orbit_commutator_not_le_core_knownSimple
      (e := e) (hz := hz) (hn := hn) hb p hsmall hmove hWQ
  have hdvd : 2 ∣ Nat.card (graphImage s W) := hpW.card_eq_or_dvd.resolve_left
    (fun hc => hnW (card_eq_one.mp hc))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := graphImage s W) 2 hdvd
  refine ⟨hWE,hWG,?_,x,x.property,?_,heven x.property⟩
  · apply le_antisymm ?_ bot_le
    exact (commutator_mono (commutator_mono le_rfl hWE) hWE).trans_eq
      (SylowKernelPair.small_seed_orbit_quadratic_knownSimple
        (e := e) (hz := hz) (hn := hn) hb p hsmall).1
  · exact (Subgroup.orderOf_coe x).trans hx

include e hz hn in
/-- The constructed even actor discharges the even-image premise of
relative-normalizer generation at the original base vertex. -/
theorem moving_base_orbit_generating_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)) ≤ centralizer
        ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical (alpha d.radical)
    let E := componentOrbit (Z d.radical a') T
    let W := ⁅E,T⁆
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  obtain ⟨_,hWG,_,x,hx,hxo,hxeven⟩ := moving_base_orbit_even_actor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove
  obtain ⟨⟨P,hP⟩,_,_⟩ := SylowTerminal.four_lt_original_sylow_non_elementary_image_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  exact SylowActor.generating_neighbor_of_even_actor s (by omega) P hP _ hWG x hx hxo hxeven

include e hz hn in
/-- At every original component vertex, the same orbit commutator escapes
the starting core and generates with a neighboring relative normalizer. -/
theorem moving_orbit_generating_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hmove : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a) ≤ centralizer
        ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
      stabilizer d.radical a
    let E := componentOrbit (Z d.radical a') T
    let W := ⁅E,T⁆
    W ≤ E ∧ W ≤ stabilizer d.radical a ∧
      ⁅⁅Z d.radical a,W⁆,W⁆ = ⊥ ∧ (¬ W ≤ Q d.radical a) ∧
      ∃ t, Adjacent d.radical a t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical a) ⊔ W = stabilizer d.radical a := by
  let T := normalizer (Q d.radical (p.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical a
  let E := componentOrbit (Z d.radical a') T
  let W := ⁅E,T⁆
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hrestore (v : Vertex d.radical) : act d.radical g (act d.radical g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hex : ∃ q : CriticalPath d.radical (replacementGeometry h d)
      (act d.radical g⁻¹ a) (act d.radical g⁻¹ a'),
      ∀ i, q.walk.getVert i = act d.radical g⁻¹ (p.walk.getVert i) :=
    ⟨p.act g⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hbase] at hex
  obtain ⟨q,hq⟩ := hex
  have hsmallq : (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (Z d.radical (alpha d.radical)) < 4 := by
    rw [←hbase,Q_act,Z_act,inv_inv,
      relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hsmall
  let Tq := normalizer (Q d.radical (q.walk.getVert 1) : Set (FreeAmalgam d.radical)) ⊓
    stabilizer d.radical (alpha d.radical)
  let Eq := componentOrbit (Z d.radical (act d.radical g⁻¹ a')) Tq
  let Wq := ⁅Eq,Tq⁆
  let f := (MulAut.conj g⁻¹).toMonoidHom
  have he : act d.radical g (alpha d.radical) = a := by rw [←hbase,hrestore]
  have hT : Tq.map f = T := by
    change (normalizer (Q d.radical (q.walk.getVert 1) : Set _) ⊓
      stabilizer d.radical (alpha d.radical)).map f = T
    rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      ←Q_act,←stabilizer_act,he,hq,hrestore]
  have hZ : (Z d.radical (alpha d.radical)).map f = Z d.radical a := by
    rw [←Z_act,he]
  have hZa' : (Z d.radical (act d.radical g⁻¹ a')).map f = Z d.radical a' := by
    rw [←Z_act,hrestore]
  have hE : Eq.map f = E := by rw [map_orbit,hZa',hT]
  have hW : Wq.map f = W := by rw [map_commutator,hE,hT]
  have hmoveq : ¬ Tq ≤ centralizer ((⁅Z d.radical (alpha d.radical),
      Z d.radical (act d.radical g⁻¹ a')⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hf
    have hh := (map_mono (f := f) hf).trans (map_centralizer_le_centralizer_image _ _)
    change Tq.map f ≤ centralizer
      ((⁅Z d.radical (alpha d.radical),Z d.radical (act d.radical g⁻¹ a')⁆).map f : Set _) at hh
    rw [hT,map_commutator,hZ,hZa'] at hh
    exact hmove hh
  obtain ⟨hWE,hWG,hquad,_⟩ := moving_base_orbit_even_actor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q hsmallq hmoveq
  obtain ⟨t,hat,hgen⟩ := moving_base_orbit_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb q hsmallq hmoveq
  change Wq ≤ Eq at hWE
  change Wq ≤ stabilizer d.radical (alpha d.radical) at hWG
  change ⁅⁅Z d.radical (alpha d.radical),Wq⁆,Wq⁆ = ⊥ at hquad
  change (normalizer (Q d.radical t : Set _) ⊓
    stabilizer d.radical (alpha d.radical)) ⊔ Wq = _ at hgen
  refine ⟨?_,?_,?_,moving_orbit_commutator_not_le_core_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove,act d.radical g t,?_,?_⟩
  · have hh := map_mono (f := f) hWE
    rwa [hW,hE] at hh
  · have hh := map_mono (f := f) hWG
    rwa [hW,←stabilizer_act,he] at hh
  · have hh := congrArg (Subgroup.map f) hquad
    rwa [map_commutator,map_commutator,hZ,hW,Subgroup.map_bot] at hh
  · simpa only [he] using (adjacent_act_iff d.radical g _ _).mpr hat
  · have hh := congrArg (Subgroup.map f) hgen
    rw [Subgroup.map_sup,map_inf _ _ _ (MulAut.conj g⁻¹).injective,
      map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,
      ←Q_act,←stabilizer_act,he,hW] at hh
    exact hh

include e hz hn in
/-- Application to the literal restricted original Sylow: its endpoint-orbit
commutator lies in the first-edge kernel and generates with a selected
neighboring relative normalizer, while escaping the starting two-core. -/
theorem original_sylow_moving_orbit_generating_neighbor_knownSimple
    (hb : 4 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hfirst : p.walk.getVert 1 = beta d.radical)
    (hmove : ¬ ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical) ≤
      centralizer ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ :
        Subgroup (FreeAmalgam d.radical)) : Set _)) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    let W := ⁅componentOrbit (Z d.radical a') T,T⁆
    W ≤ Q d.radical (beta d.radical) ∧ (¬ W ≤ Q d.radical (alpha d.radical)) ∧
      ∃ t, Adjacent d.radical (alpha d.radical) t ∧
        (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
          stabilizer d.radical (alpha d.radical)) ⊔ W = stabilizer d.radical (alpha d.radical) := by
  have hT := SylowSmallNormalizer.four_lt_base_edge_normalizer_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  have hmove' : ¬ (normalizer (Q d.radical (p.walk.getVert 1) : Set _) ⊓
      stabilizer d.radical (alpha d.radical)) ≤ centralizer
        ((⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rwa [hfirst,hT]
  have hg := moving_orbit_generating_neighbor_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hsmall hmove'
  have hi := SylowKernelPair.small_seed_orbit_identifications_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p
  dsimp only at hg hi ⊢
  rw [hfirst,hT] at hg hi
  exact ⟨hg.1.trans hi.1,hg.2.2.2.1,hg.2.2.2.2⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowEvenOrbit
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
