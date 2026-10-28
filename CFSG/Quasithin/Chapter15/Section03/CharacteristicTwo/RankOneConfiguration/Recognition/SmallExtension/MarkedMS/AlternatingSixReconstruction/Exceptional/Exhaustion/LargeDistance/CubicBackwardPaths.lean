module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCoordinatedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.RadiusObstruction

/-!
# Actual critical shifts retaining the cubic kernel

An escaping two-subgroup has relative normal closure generating with any
incident edge kernel. This uses the original quasisimple component and
retains its central cubic quotient. A nonnormal neighboring seed join then
has a conjugate moved by that same actor.

For a large critical image, the checked restricted-actor construction gives
an escaping two-subgroup of the reverse moving cover whose commutator with
the radius intersection lies in the starting seed. Containment of the chosen
backward seed in the second-predecessor kernel would force the forbidden
normalization. Thus the new path is genuinely critical. Its first edge is
the prescribed edge transported by the same conjugator, and every overlap
vertex is retained. Reversing the original walk constructs the forward shift
and the second radius escape. Both cover orders sixteen and thirty-two are
handled, with no faithful-kernel or full point-core assumption.

The whole-core and literal C.1.32 applications discharge the actor,
normal-generation and displacement premises in this large-image branch.
The small-image shifted-path exclusion, the coordinated R4/R6 calculations
of (5.11), the distance-four exclusion (5.12), and final reconstruction stay
with qt-e-ms-small-a6-reconstruction. Independent natural exhaustion stays
with qt-e-ms-small-a6-exhaustion-large-distance.

Source: MS93 (2.1)(iii),(vii), p.856; (5.2), pp.912--915; the backward
noncontainment argument of (5.7), p.919, used for the shifts in (5.11),
pp.923--924. The geometric argument adapts Sp4Four.DistanceReduction's
RadiusObstruction and Backward, with the actual cubic-kernel actor supplied
by CubicRestrictedActor.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NormalizerTransfer
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => edge L R
local notation "π" => CubicAction.projection h e hz hk

omit hk in
include h e hz in
/-- The normal closure of any escaping two-subgroup generates with every
incident edge kernel. The relative component retains its cubic center. -/
theorem two_subgroup_conjugates_edge_generation
    {a t : Vertex T} (ha : color T a = false) (hat : Adjacent T a t)
    (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a)
    (hAtwo : IsPGroup 2 A) (hAQ : ¬ A ≤ Q T a) :
    conjugatesIn A (stabilizer T a) ⊔ Q T t = stabilizer T a := by
  let N := conjugatesIn A (stabilizer T a)
  have hNG : N ≤ stabilizer T a := conjugatesIn_le _ _ hA
  have hAN : A ≤ N := by
    intro x hx
    apply le_iSup (fun g : stabilizer T a => rightConjugate A g) (1 : stabilizer T a)
    exact ⟨x,hx,by simp⟩
  obtain ⟨i,hi,hir,hiL,_,hiQ⟩ := CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison.vertex_coordinates_with_kernel
    T h.relative_radical.isPGroup h.relative_radical.twoCore_le ha
  let N₀ := N.comap i
  let A₀ := A.comap i
  let : N₀.Normal := by
    constructor
    intro n hn g
    change i (g*n*g⁻¹) ∈ N
    rw [map_mul,map_mul,map_inv]
    exact le_normalizer_iff.mp (conjugatesIn_normalized A (stabilizer T a))
      (i g) (hir ▸ (show i g ∈ i.range from ⟨g,rfl⟩)) (i n) hn
  have hNm : N₀.map i = N := map_comap_eq_self (hNG.trans_eq hir.symm)
  have hAm : A₀.map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hA₀Q : ¬ A₀ ≤ pCore 2 M := by
    intro hn
    apply hAQ
    have hh := map_mono (f := i) hn
    rwa [hAm,hiQ] at hh
  have hKN : L.subgroupOf (L ⊔ R) ≤ N₀ ⊔ pCore 2 M :=
    component_le_normal_of_two_subgroup h e hz _ A₀ le_sup_right
      (hAtwo.comap_of_injective i hi) hA₀Q ((comap_mono hAN).trans le_sup_left)
  have hLN : Ltilde T a ≤ N ⊔ Q T a := by
    have hh := map_mono (f := i) hKN
    rw [←h.relative_residual,hiL,Subgroup.map_sup,hNm,hiQ] at hh
    exact hh
  have ht : color T t = true := by
    have hn := adjacent_color_ne T hat
    cases hc : color T t <;> simp_all
  have hgen : pResidual 2 M ⊔ T = ⊤ := by
    rw [h.relative_residual]
    exact (codisjoint_subgroupOf_sup L R).eq_top
  have htG : Q T t ≤ stabilizer T a := fun _ hx => hx.2 _ (adjacent_symm T hat)
  apply le_antisymm (sup_le hNG htG)
  rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation T hgen ha hat]
  exact sup_le (hLN.trans (sup_le_sup_left (Q_le_adjacent_h T ht hat) N)) le_sup_right

omit hk in
include h e hz in
/-- At any prescribed incident edge a neighboring seed join has a single
conjugate which the given escaping two-subgroup fails to normalize. -/
theorem exists_neighbor_seed_join_escape
    (hb : 2 < sourceDistance h) {a t : Vertex T}
    (ha : color T a = false) (hat : Adjacent T a t) (hne : Z T a ≠ ⊥)
    (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a)
    (hAtwo : IsPGroup 2 A) (hAQ : ¬ A ≤ Q T a) :
    ∃ d, Adjacent T d t ∧
      ∃ g ∈ stabilizer T a,
        ¬ A ≤ normalizer
          ((Z T d ⊔ Z T a).map (MulAut.conj g⁻¹).toMonoidHom : Set (FreeAmalgam T)) := by
  obtain ⟨d,hdt,hn⟩ :=
    CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.exists_neighbor_seed_join_not_normalized
      h.relative_characteristic (sourceGeometry h) hb ha hat hne
  have ht : color T t = true := by
    have hh := adjacent_color_ne T hat
    cases hc : color T t <;> simp_all
  have hd : color T d = false := by
    have hh := adjacent_color_ne T hdt
    cases hc : color T d <;> simp_all
  have hZaQ : Z T a ≤ Q T a :=
    ((sourceGeometry h).omega_bound a ha (by
      rw [(sourceGeometry h).distance_constant a ha]
      exact sourceDistance_pos h)).trans (omegaCenter_le _)
  have hZdQ : Z T d ≤ Q T d :=
    ((sourceGeometry h).omega_bound d hd (by
      rw [(sourceGeometry h).distance_constant d hd]
      exact sourceDistance_pos h)).trans (omegaCenter_le _)
  let N := Z T d ⊔ Z T a
  have hNQ : N ≤ Q T t :=
    sup_le (hZdQ.trans (Q_le_adjacent_h T ht hdt)) (hZaQ.trans (Q_le_adjacent_h T ht hat))
  have htG : Q T t ≤ stabilizer T a := fun _ hx => hx.2 _ (adjacent_symm T hat)
  have hNn : Q T t ≤ normalizer (N : Set (FreeAmalgam T)) :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt
  have hnG : ¬ (N.subgroupOf (stabilizer T a)).Normal := fun hh =>
    hn ((normal_subgroupOf_iff_le_normalizer (hNQ.trans htG)).mp hh)
  obtain ⟨g,hg,hgN,_⟩ := simultaneous_escape A (stabilizer T a) (Q T t) N N
    htG hNQ hNQ (normal_subgroupOf_of_le_normalizer hNn)
    (normal_subgroupOf_of_le_normalizer hNn) hnG hnG
    (two_subgroup_conjugates_edge_generation h e hz ha hat A hA hAtwo hAQ)
  exact ⟨d,hdt,g,hg,hgN⟩

omit hk in
include h e hz in
/-- A controlled escaping subactor constructs an actual backward critical
path, with the prescribed edge transported by the same local conjugator. -/
theorem backward_path_of_controlled_subactor
    (hb : 2 < sourceDistance h) {a c t : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c) (hat : Adjacent T a t)
    (A : Subgroup (FreeAmalgam T)) (hA : A ≤ stabilizer T a)
    (hAtwo : IsPGroup 2 A) (hAQ : ¬ A ≤ Q T a)
    (hdisp : ⁅V T a ⊓ Q T (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z T a) :
    ∃ d, Adjacent T d t ∧ ∃ g ∈ stabilizer T a,
      ∃ q : CriticalPath T (sourceGeometry h)
        (act T g d) (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = act T g t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        ¬ A ≤ normalizer
          ((Z T (act T g d) ⊔ Z T a : Subgroup (FreeAmalgam T)) : Set (FreeAmalgam T)) := by
  have hne : Z T a ≠ ⊥ := fun he => p.critical.2 (he ▸ bot_le)
  obtain ⟨d,hdt,g,hg,hescape⟩ := exists_neighbor_seed_join_escape h e hz hb
    p.start_color hat hne A hA hAtwo hAQ
  have hga : act T g a = a := hg
  have hatg : Adjacent T a (act T g t) := by
    rw [←hga]
    exact (adjacent_act_iff T g _ _).mpr hat
  have hdtg : Adjacent T (act T g d) (act T g t) := (adjacent_act_iff T g _ _).mpr hdt
  rw [Subgroup.map_sup,←Z_act,←Z_act,hga] at hescape
  have hV : Z T (act T g d) ≤ V T a :=
    le_sup_left.trans (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hatg hdtg)
  have hn : ¬ Z T (act T g d) ≤ Q T (p.walk.getVert (p.walk.length-2)) := by
    intro hbad
    apply hescape
    have hzZ := hA.trans (Z_normalized T a)
    have hd : ⁅A,Z T (act T g d)⁆ ≤ Z T a := by
      rw [commutator_comm]
      exact (commutator_mono (le_inf hV hbad) le_rfl).trans hdisp
    apply le_normalizer_iff.mpr
    intro z hz y hy
    have hm : (Z T (act T g d) ⊔ Z T a).map (MulAut.conj z).toMonoidHom ≤
        Z T (act T g d) ⊔ Z T a := by
      rw [Subgroup.map_sup]
      apply sup_le
      · rintro _ ⟨v,hv,rfl⟩
        have hc := hd (commutator_mem_commutator hz hv)
        change z*v*z⁻¹ ∈ Z T (act T g d) ⊔ Z T a
        rw [show z*v*z⁻¹ = ⁅z,v⁆*v by simp [commutatorElement_def,mul_assoc]]
        exact mul_mem (mem_sup_right hc) (mem_sup_left hv)
      · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hzZ hz)]
        exact le_sup_right
    exact hm (mem_map_of_mem (MulAut.conj z).toMonoidHom hy)
  obtain ⟨q,hq,hover⟩ :=
    CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      (sourceGeometry h) (by change 2 ≤ sourceDistance h; omega) p hatg hdtg hn
  exact ⟨d,hdt,g,hg,q,hq,hover,hescape⟩

include h e hz hk in
private theorem controlled_subactor_base
    {c : Vertex T} (p : CriticalPath T (sourceGeometry h) (alpha T) c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T (alpha T))) :
    ∃ A : Subgroup (FreeAmalgam T), A ≤ U T c ∧ IsPGroup 2 A ∧
      ¬ A ≤ Q T (alpha T) ∧
      ⁅V T (alpha T) ⊓ Q T (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z T (alpha T) := by
  obtain ⟨A,hAU,hdisp,a,haA,ha2,_⟩ := critical_radius_even_actor h e hz hk p hforward
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.end_color
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le
    (hAU.trans (DistanceEight.U_le_Z T c))
  refine ⟨A,hAU,IsElementaryAbelian.isPGroup 2 A,?_,hdisp⟩
  intro hAQ
  have hcom : A.comap (embedM T) ≤ pCore 2 M := by
    have hh := comap_mono (f := embedM T) hAQ
    rwa [Q_alpha_comap T h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
  have hzero : (A.comap (embedM T)).map π = ⊥ := by
    apply (Subgroup.map_eq_bot_iff _).mpr
    rw [CubicAction.projection_kernel h e hz hk]
    exact hcom.trans le_sup_right
  have ha1 : a = 1 := mem_bot.mp (hzero ▸ haA)
  rw [ha1,orderOf_one] at ha2
  contradiction

include h e hz hk in
/-- At every original vertex a large critical image supplies a controlled
escaping two-subgroup of the reverse moving cover. Both full cover orders
and the original cubic kernel are retained by the actor construction. -/
theorem large_critical_controlled_subactor
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T a)) :
    ∃ A : Subgroup (FreeAmalgam T), A ≤ U T c ∧ IsPGroup 2 A ∧
      ¬ A ≤ Q T a ∧
      ⁅V T a ⊓ Q T (p.walk.getVert (p.walk.length-2)),A⁆ ≤ Z T a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color T p.start_color
  have hbase : act T g⁻¹ a = alpha T := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have hpact : ∃ p₀ : CriticalPath T (sourceGeometry h)
      (act T g⁻¹ a) (act T g⁻¹ c),
      (∀ n, p₀.walk.getVert n = act T g⁻¹ (p.walk.getVert n)) ∧
      p₀.walk.length = p.walk.length :=
    ⟨p.act g⁻¹,fun n => by simp only [CriticalPath.act,actWalk_getVert],
      actWalk_length T g⁻¹ p.walk⟩
  rw [hbase] at hpact
  obtain ⟨p₀,hvert,hlen⟩ := hpact
  have hf : 4 ≤ (Q T (act T g⁻¹ c)).relIndex (Z T (alpha T)) := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hforward
  obtain ⟨A₀,hAU,hAtwo,hAQ,hdisp⟩ := controlled_subactor_base h e hz hk p₀ hf
  let f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom
  let A := A₀.comap f
  have hAm : A.map f = A₀ := map_comap_eq_self_of_surjective (MulAut.conj (g⁻¹)⁻¹).surjective _
  refine ⟨A,?_,hAtwo.comap_of_injective f (MulAut.conj (g⁻¹)⁻¹).injective,?_,?_⟩
  · apply (map_le_map_iff_of_injective (f := f) (MulAut.conj (g⁻¹)⁻¹).injective).mp
    rw [hAm]
    simpa only [U_act] using hAU
  · intro hn
    apply hAQ
    have hh := map_mono (f := f) hn
    rw [hAm,←Q_act,hbase] at hh
    exact hh
  · apply (map_le_map_iff_of_injective (f := f) (MulAut.conj (g⁻¹)⁻¹).injective).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj (g⁻¹)⁻¹).injective,hAm]
    rw [hlen,hvert,←hbase,V_act,Q_act,Z_act] at hdisp
    exact hdisp

include h e hz hk in
/-- The source large-image backward shift is constructed at any prescribed
incident edge. One conjugator transports that edge and the backward seed;
the entire overlap with the original critical walk is literal. -/
theorem large_critical_backward_path
    {a c t : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hat : Adjacent T a t)
    (hforward : 4 ≤ (Q T c).relIndex (Z T a)) :
    ∃ d, Adjacent T d t ∧ ∃ g ∈ stabilizer T a,
      ∃ q : CriticalPath T (sourceGeometry h)
        (act T g d) (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = act T g t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  obtain ⟨A,hAU,hAtwo,hAQ,hdisp⟩ := large_critical_controlled_subactor h e hz hk p hforward
  have hAG : A ≤ stabilizer T a :=
    (hAU.trans (DistanceEight.U_le_Z T c)).trans
      (critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
        (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
        p.critical)
  obtain ⟨d,hdt,g,hg,q,hq,hover,_⟩ := backward_path_of_controlled_subactor
    h e hz (distance_gt_two h e hz hk) p hat A hAG hAtwo hAQ hdisp
  exact ⟨d,hdt,g,hg,q,hq,hover⟩

include h e hz hk in
/-- On the same large-image critical walk the full starting radius escapes
the second predecessor of its endpoint, without a new source premise. -/
theorem large_critical_radius_escape
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T a)) :
    ¬ V T a ≤ Q T (p.walk.getVert (p.walk.length-2)) := by
  have hlen : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
  have hat : Adjacent T a (p.walk.getVert 1) := by
    apply (cosetGraph_adj T _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hlen
  obtain ⟨d,hdt,g,hg,q,_,_⟩ := large_critical_backward_path h e hz hk p hat hforward
  have hga : act T g a = a := hg
  have had : (cosetGraph T).dist (act T g d) a ≤ 2 := by
    rw [←hga,dist_act]
    exact CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hdt
  have hZV : Z T (act T g d) ≤ V T a := le_iSup_of_le _ (le_iSup_of_le had le_rfl)
  exact fun hn => q.critical.2 (hZV.trans hn)

include h e hz hk in
/-- The forward shift uses the literal reverse of the original walk. Its
initial overlap is the original path with its first two edges removed. -/
theorem large_critical_forward_path
    {a c t : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hct : Adjacent T c t)
    (hforward : 4 ≤ (Q T c).relIndex (Z T a)) :
    ∃ d, Adjacent T d t ∧ ∃ g ∈ stabilizer T c,
      ∃ q : CriticalPath T (sourceGeometry h)
        (p.walk.getVert 2) (act T g d),
        q.walk.getVert (q.walk.length-1) = act T g t ∧
        ∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2) := by
  have hb := distance_gt_two h e hz hk
  have hlen : 2 ≤ p.walk.length := by
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    omega
  let rev : CriticalPath T (sourceGeometry h) c a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) c p.end_color p.critical⟩
  have hr : 4 ≤ (Q T a).relIndex (Z T c) :=
    reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hforward
  have hend : rev.walk.getVert (rev.walk.length-2) = p.walk.getVert 2 := by
    change p.walk.reverse.getVert (p.walk.reverse.length-2) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,Nat.sub_sub_self hlen]
  have hshift := large_critical_backward_path h e hz hk rev hct hr
  rw [hend] at hshift
  obtain ⟨d,hdt,g,hg,q,hq,hover⟩ := hshift
  let fwd : CriticalPath T (sourceGeometry h) (p.walk.getVert 2) (act T g d) :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) _ q.end_color q.critical⟩
  have hqLen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
  refine ⟨d,hdt,g,hg,fwd,?_,?_⟩
  · change q.walk.reverse.getVert (q.walk.reverse.length-1) = _
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
      Nat.sub_sub_self (by omega : 1 ≤ q.walk.length)]
    exact hq
  · intro i hi
    change q.walk.reverse.getVert i = _
    rw [SimpleGraph.Walk.getVert_reverse,hqLen]
    have hi' : p.walk.length-i = (p.walk.length-i-2)+2 := by omega
    rw [hi',hover (p.walk.length-i-2) (by
      change p.walk.length-i-2 ≤ p.walk.reverse.length-2
      rw [SimpleGraph.Walk.length_reverse]
      omega)]
    change p.walk.reverse.getVert (p.walk.length-i-2) = _
    rw [SimpleGraph.Walk.getVert_reverse]
    congr 1
    omega

include h e hz hk in
/-- Large critical images give both source escapes on the same path. -/
theorem large_critical_radius_escapes
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hforward : 4 ≤ (Q T c).relIndex (Z T a)) :
    ¬ V T a ≤ Q T (p.walk.getVert (p.walk.length-2)) ∧
      ¬ V T c ≤ Q T (p.walk.getVert 2) := by
  refine ⟨large_critical_radius_escape h e hz hk p hforward,?_⟩
  let rev : CriticalPath T (sourceGeometry h) c a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
        a p.start_color (by
          rw [(sourceGeometry h).distance_constant a p.start_color]
          exact sourceDistance_pos h) c p.end_color p.critical⟩
  have hr : 4 ≤ (Q T a).relIndex (Z T c) :=
    reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hforward
  have hh := large_critical_radius_escape h e hz hk rev hr
  change ¬ V T c ≤ Q T (p.walk.reverse.getVert (p.walk.reverse.length-2)) at hh
  have hlen : 2 ≤ p.walk.length := by
    have hh : p.walk.length = sourceDistance h := p.length_eq_b
    have hb := distance_gt_two h e hz hk
    omega
  rwa [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,Nat.sub_sub_self hlen] at hh

omit hk in
include h e hz in
/-- The whole-core alternative carries both actual shifts in every large
critical-image case. The small-image shifted-path and terminal distance-four
exclusions remain with this reconstruction owner. -/
theorem coreExhaustion_or_cubic_large_critical_shifts :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a c : Vertex T, ∀ p : CriticalPath T (sourceGeometry h) a c,
        4 ≤ (Q T c).relIndex (Z T a) →
        (¬ V T a ≤ Q T (p.walk.getVert (p.walk.length-2)) ∧
          ¬ V T c ≤ Q T (p.walk.getVert 2)) ∧
        (∀ t, Adjacent T a t →
          ∃ d, Adjacent T d t ∧ ∃ g ∈ stabilizer T a,
            ∃ q : CriticalPath T (sourceGeometry h)
              (act T g d) (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 1 = act T g t ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (∀ t, Adjacent T c t →
          ∃ d, Adjacent T d t ∧ ∃ g ∈ stabilizer T c,
            ∃ q : CriticalPath T (sourceGeometry h)
              (p.walk.getVert 2) (act T g d),
              q.walk.getVert (q.walk.length-1) = act T g t ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,?_⟩
    intro a c p hf
    exact ⟨large_critical_radius_escapes h e hz hk p hf,
      fun _ ht => large_critical_backward_path h e hz hk p ht hf,
      fun _ ht => large_critical_forward_path h e hz hk p ht hf⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application of the constructed forward and backward
critical paths. No restricted-actor or displacement premise remains. -/
theorem rankTwo_or_cubic_large_critical_shifts :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a c : Vertex T, ∀ p : CriticalPath T (sourceGeometry h) a c,
        4 ≤ (Q T c).relIndex (Z T a) →
        (¬ V T a ≤ Q T (p.walk.getVert (p.walk.length-2)) ∧
          ¬ V T c ≤ Q T (p.walk.getVert 2)) ∧
        (∀ t, Adjacent T a t →
          ∃ d, Adjacent T d t ∧ ∃ g ∈ stabilizer T a,
            ∃ q : CriticalPath T (sourceGeometry h)
              (act T g d) (p.walk.getVert (p.walk.length-2)),
              q.walk.getVert 1 = act T g t ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (∀ t, Adjacent T c t →
          ∃ d, Adjacent T d t ∧ ∃ g ∈ stabilizer T c,
            ∃ q : CriticalPath T (sourceGeometry h)
              (p.walk.getVert 2) (act T g d),
              q.walk.getVert (q.walk.length-1) = act T g t ∧
              ∀ i ≤ p.walk.length-2, q.walk.getVert i = p.walk.getVert (i+2)) :=
  (coreExhaustion_or_cubic_large_critical_shifts h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
