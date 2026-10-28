module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CriticalCover
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.RadiusCentrality

/-!
# Point-core radius control without splitting the central cover

The literal natural quotient of the whole moved subgroup transports a
commutator centralizer to the pointwise fixer of its moved image. The
order-four quadratic point-core calculation then bounds the acting image.
Pullback through the original quotient and free-amalgam maps bounds the
whole endpoint commutator, including the possible central attachment.

The actual radius-two application supplies the centralizing commutator and
edge placement from the critical path. It supplies the point-core commutator estimate used in the proof of
MS93 (5.2)(i) for either moved order. Point-core containment and the displayed
critical index remain explicit; this does not assert the distance exclusion.
Source: MS93 (3.3), (5.2)(i), printed pp.866--867,913--914.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

/-- A subgroup of any edge at the base vertex has its marked image in a
conjugate point core whenever the radical does. The conjugator comes from
that actual edge, rather than a new choice of quotient coordinates. -/
theorem graphImage_le_pointCore_of_le_edge (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (t : Vertex d.radical) (hat : Adjacent d.radical (alpha d.radical) t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAt : A ≤ Q d.radical t) :
    ∃ v : S, graphImage s A ≤ pointCore.map (MulAut.conj v).toMonoidHom := by
  obtain ⟨g,hg|hg⟩ := edge_transitive d.radical hat (base_adjacent d.radical)
  · have hgM : g ∈ (embedM d.radical).range := by
      change g ∈ Mbar d.radical
      rw [← stabilizer_m_base d.radical]
      exact hg.1
    obtain ⟨m,rfl⟩ := hgM
    have hQt : (Q d.radical t).map
        (MulAut.conj ((embedM d.radical m)⁻¹)).toMonoidHom =
          d.radical.map (embedM d.radical) := by
      rw [← Q_act,hg.2]
      exact Q_beta d.radical
    have hAm (x : d.overgroup) (hx : x ∈ A.comap (embedM d.radical)) :
        m⁻¹*x*m ∈ d.radical := by
      have hh := ((map_mono hAt).trans_eq hQt) (mem_map_of_mem
        (MulAut.conj ((embedM d.radical m)⁻¹)).toMonoidHom hx)
      obtain ⟨r,hr,he⟩ := hh
      have heq : r = m⁻¹*x*m := by
        apply embedM_injective d.radical
        change embedM d.radical r = (embedM d.radical m)⁻¹ *
          embedM d.radical x * ((embedM d.radical m)⁻¹)⁻¹ at he
        simpa only [map_mul,map_inv,inv_inv] using he
      exact heq ▸ hr
    refine ⟨s.projection m * u,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨r,hr,he⟩ := hR (mem_map_of_mem s.projection (hAm x hx))
    refine ⟨r,hr,?_⟩
    change (s.projection m*u)*r*(s.projection m*u)⁻¹=s.projection x
    have he' : u*r*u⁻¹ = (s.projection m)⁻¹*s.projection x*s.projection m := by
      change u*r*u⁻¹ = s.projection (m⁻¹*x*m) at he
      simpa only [map_mul,map_inv] using he
    calc
      (s.projection m*u)*r*(s.projection m*u)⁻¹ =
          s.projection m*(u*r*u⁻¹)*(s.projection m)⁻¹ := by group
      _ = s.projection x := by rw [he']; group
  · have hh : color d.radical (beta d.radical) = false := by
      change color d.radical (hVertex d.radical 1) = false
      rw [← hg.1,action_preserves_color]
      rfl
    cases hh

/-- The opposite critical index is at most four in the point-core branch,
including the order-thirty-two nonsplit cover. -/
theorem critical_opposite_index_le_four (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    (Q d.radical (alpha d.radical)).relIndex (Z d.radical a') ≤ 4 := by
  have hp := replacementDistance_pos h d
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hat : Adjacent d.radical (alpha d.radical) (p.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i:=0) (by omega))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hAt : Z d.radical a' ≤ Q d.radical (p.walk.getVert 1) := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical a' p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,
      SimpleGraph.dist_comm,p.dist_end (i:=1)]
    change p.walk.length-1 < replacementDistance h d
    omega
  obtain ⟨v,hv⟩ := graphImage_le_pointCore_of_le_edge s u hR _ hat _ hAt
  have hbound := QuadraticPointCore.conjugate_core_bound _ v hv
    (critical_opposite_image_quadratic s hc p)
  rwa [graphImage_card s _ ((critical_Z_le_stabilizer d.radical
    (replacementGeometry h d) (alpha d.radical) rfl hp p.critical))] at hbound

/-- The full point core acts nonquadratically on the entire moved cover,
regardless of whether its order is sixteen or thirty-two. -/
theorem moved_double_commutator_ne_bot (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom) :
    ⁅⁅replacementMoved d,d.radical⁆,d.radical⁆ ≠ ⊥ := by
  intro hzero
  have hquad := image_quadratic_of_commutator s d.radical
    (commutator_eq_bot_iff_le_centralizer.mp hzero)
  have hbound := QuadraticPointCore.conjugate_core_bound _ u hfull.le hquad
  rw [hfull,card_map_of_injective (MulAut.conj u).injective,pointCore_card] at hbound
  omega

/-- The same obstruction on every literal edge of the replacement graph. -/
theorem edge_double_commutator_ne_bot (hc : DistanceTwo.CentralLayer d) (u : S)
    (hfull : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ⁅⁅U d.radical a,Q d.radical t⁆,Q d.radical t⁆ ≠ ⊥ := by
  have hbase : ⁅⁅U d.radical (alpha d.radical),Q d.radical (beta d.radical)⁆,
      Q d.radical (beta d.radical)⁆ ≠ ⊥ := by
    rw [hc.U_eq_moved,Q_beta,←map_commutator,←map_commutator]
    intro hz
    apply moved_double_commutator_ne_bot s u hfull
    apply map_injective (embedM_injective d.radical)
    simpa only [Subgroup.map_bot] using hz
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    intro hz
    apply hbase
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    rw [map_commutator,map_commutator,←U_act,←Q_act]
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul,Subgroup.map_bot]
    exact hz
  · rw [hg.1] at ha
    cases ha

/-- The order-four critical image controls its moving-space centralizer,
using only the surjective projection of the entire cover. -/
theorem moving_commutator_image_control (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A Y : Subgroup d.overgroup) (hA : A ≤ d.radical) (hY : Y ≤ d.radical)
    (hcard : 4 ≤ Nat.card (A.map s.projection))
    (hAA : ⁅replacementMoved d,A⁆ ≤ centralizer (A : Set d.overgroup))
    (hAY : ⁅replacementMoved d,A⁆ ≤ centralizer (Y : Set d.overgroup)) :
    Y.map s.projection ≤ A.map s.projection := by
  have hq := image_quadratic_of_commutator s A hAA
  have hAc := (map_mono hA).trans hR
  have horder : Nat.card (A.map s.projection) = 4 :=
    Nat.le_antisymm (QuadraticPointCore.conjugate_core_bound _ u hAc hq) hcard
  rw [← QuadraticPointCore.conjugate_four_moved_fixer _ u hAc hq horder]
  exact fun y hy => ⟨((map_mono hY).trans hR) hy,
    (image_centralizes_moved s A Y hAY hy).2⟩

/-- Radius elements in the penultimate kernel centralize the actual critical
commutator. This uses only the strict large-distance hypothesis. -/
theorem critical_radius_intersection_centralizes {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hb : 2 < replacementDistance h d) :
    V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      centralizer ((⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical)) := by
  have hcomm : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    (critical_Z_commutator_le_moving (h := h) p).trans inf_le_left |>.trans (DistanceEight.U_le_Z d.radical a)
  have hQ : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  exact ((inf_le_left.trans (V_le_Q d.radical p.start_color hb)).trans hQ).trans
    (centralizer_le hcomm)

/-- The finite point-core fixer calculation for actual embedded edge subgroups. -/
theorem edge_moving_image_control (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A Y : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical (beta d.radical)) (hY : Y ≤ Q d.radical (beta d.radical))
    (hcard : 4 ≤ (Q d.radical (alpha d.radical)).relIndex A)
    (hAA : ⁅(replacementMoved d).map (embedM d.radical),A⁆ ≤ centralizer (A : Set (FreeAmalgam d.radical)))
    (hAY : ⁅(replacementMoved d).map (embedM d.radical),A⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical))) :
    Y ≤ Q d.radical (alpha d.radical) ⊔ A := by
  let A₀ := A.comap (embedM d.radical)
  let Y₀ := Y.comap (embedM d.radical)
  have hQ : Q d.radical (beta d.radical) = d.radical.map (embedM d.radical) := Q_beta d.radical
  have hA₀ : A₀ ≤ d.radical := by
    intro x hx
    obtain ⟨r,hr,he⟩ := (hA.trans_eq hQ) hx
    exact (embedM_injective d.radical he) ▸ hr
  have hY₀ : Y₀ ≤ d.radical := by
    intro x hx
    obtain ⟨r,hr,he⟩ := (hY.trans_eq hQ) hx
    exact (embedM_injective d.radical he) ▸ hr
  have hmapA : A₀.map (embedM d.radical) = A := by
    apply map_comap_eq_self
    exact hA.trans (hQ ▸ map_le_range (embedM d.radical) d.radical)
  have hmapY : Y₀.map (embedM d.radical) = Y := by
    apply map_comap_eq_self
    exact hY.trans (hQ ▸ map_le_range (embedM d.radical) d.radical)
  have hcard₀ : 4 ≤ Nat.card (A₀.map s.projection) := by
    rw [Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←hmapA,
      relIndex_map_map_of_injective _ _ (embedM_injective d.radical),←s.projection_kernel,
      relIndex_ker] at hcard
    exact hcard
  have hc (B : Subgroup d.overgroup) (D : Subgroup (FreeAmalgam d.radical))
      (hBD : B.map (embedM d.radical) = D)
      (hC : ⁅(replacementMoved d).map (embedM d.radical),A⁆ ≤ centralizer (D : Set (FreeAmalgam d.radical))) :
      ⁅(replacementMoved d),A₀⁆ ≤ centralizer (B : Set d.overgroup) := by
    intro x hx b hb
    apply embedM_injective d.radical
    simp only [map_mul]
    have hx' : embedM d.radical x ∈ ⁅(replacementMoved d).map (embedM d.radical),A⁆ := by
      rw [←hmapA,←map_commutator]
      exact mem_map_of_mem _ hx
    exact hC hx' _ (hBD ▸ mem_map_of_mem (embedM d.radical) hb)
  have hm := moving_commutator_image_control s u hR A₀ Y₀ hA₀ hY₀ hcard₀
    (hc A₀ A hmapA hAA) (hc Y₀ Y hmapY hAY)
  have hle : Y₀ ≤ pCore 2 d.overgroup ⊔ A₀ := by
    have hc := comap_mono (f := s.projection) hm
    rw [comap_map_eq,comap_map_eq,s.projection_kernel] at hc
    exact (show Y₀ ≤ Y₀ ⊔ pCore 2 d.overgroup from le_sup_left).trans
      (hc.trans (sup_comm _ _).le)
  rw [←hmapY,Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d),←hmapA,←Subgroup.map_sup]
  exact map_mono hle

/-- An edge actor centralizing the critical moving image has no larger
commutator on the actual Z-layer than the marked critical subgroup. -/
theorem edge_commutator_control (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (A Y : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical (beta d.radical)) (hY : Y ≤ Q d.radical (beta d.radical))
    (hcard : 4 ≤ (Q d.radical (alpha d.radical)).relIndex A)
    (hAA : ⁅(replacementMoved d).map (embedM d.radical),A⁆ ≤ centralizer (A : Set (FreeAmalgam d.radical)))
    (hAY : ⁅(replacementMoved d).map (embedM d.radical),A⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical (alpha d.radical),Y⁆ ≤ ⁅Z d.radical (alpha d.radical),A⁆ := by
  have hn : A ≤ normalizer (Z d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    (hA.trans (fun _ hx => hx.2 _ (adjacent_symm d.radical (base_adjacent d.radical)))).trans
      (Z_normalized d.radical (alpha d.radical))
  have hc : Q d.radical (alpha d.radical) ≤ centralizer (Z d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical (alpha d.radical) rfl))
  rw [commutator_eq_of_centralizing_sup rfl hc hn]
  exact commutator_mono le_rfl (edge_moving_image_control s u hR A Y hA hY hcard hAA hAY)

/-- The same finite calculation at any actual edge of the source graph. -/
theorem edge_commutator_control_at (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (c t : Vertex d.radical) (hcol : color d.radical c = false) (hct : Adjacent d.radical c t)
    (A Y : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ Q d.radical t) (hY : Y ≤ Q d.radical t)
    (hcard : 4 ≤ (Q d.radical c).relIndex A)
    (hAA : ⁅U d.radical c,A⁆ ≤ centralizer (A : Set (FreeAmalgam d.radical)))
    (hAY : ⁅U d.radical c,A⁆ ≤ centralizer (Y : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical c,Y⁆ ≤ ⁅Z d.radical c,A⁆ := by
  obtain ⟨g,hg | hg⟩ := edge_transitive d.radical hct (base_adjacent d.radical)
  · let e := (MulAut.conj g⁻¹).toMonoidHom
    have hQ : (Q d.radical c).map e = Q d.radical (alpha d.radical) := by rw [←Q_act,hg.1]; rfl
    have hQt : (Q d.radical t).map e = Q d.radical (beta d.radical) := by rw [←Q_act,hg.2]; rfl
    have hU : (U d.radical c).map e = (replacementMoved d).map (embedM d.radical) := by
      rw [←U_act,hg.1]
      exact hc.U_eq_moved
    have hZ : (Z d.radical c).map e = Z d.radical (alpha d.radical) := by rw [←Z_act,hg.1]; rfl
    have hC (B : Subgroup (FreeAmalgam d.radical))
        (hB : ⁅U d.radical c,A⁆ ≤ centralizer (B : Set (FreeAmalgam d.radical))) :
        ⁅(replacementMoved d).map (embedM d.radical),A.map e⁆ ≤ centralizer (B.map e : Set (FreeAmalgam d.radical)) := by
      rw [←hU,←map_commutator]
      exact (map_mono hB).trans (map_centralizer_le_centralizer_image _ e)
    have hi : 4 ≤ (Q d.radical (alpha d.radical)).relIndex (A.map e) := by
      rw [←hQ,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
      exact hcard
    have hh := edge_commutator_control s u hR (A.map e) (Y.map e)
      ((map_mono hA).trans_eq hQt) ((map_mono hY).trans_eq hQt) hi
      (hC A hAA) (hC Y hAY)
    rw [←hZ,←map_commutator,←map_commutator] at hh
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp hh
  · have hn : color d.radical (beta d.radical) = false := by
      change color d.radical (hVertex d.radical 1) = false
      rw [←hg.1,action_preserves_color,hcol]
    cases hn

open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
/-- For either central cover in the point-core branch, the whole opposite Z-layer satisfies
the commutator bound used in MS93 (5.2)(i). -/
theorem critical_radius_commutator_le_Z (hc : DistanceTwo.CentralLayer d) (u : S)
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hcard : 4 ≤ (Q d.radical a').relIndex (Z d.radical a)) :
    ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)),Z d.radical a'⁆ ≤ Z d.radical a := by
  have hl : 2 < p.walk.length := by
    rw [p.length_eq_b]
    exact hb
  let t := p.walk.getVert (p.walk.length-1)
  have hct : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hct
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have het : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i:=p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hAt : Z d.radical a ≤ Q d.radical t := by
    apply Z_le_Q_of_dist_lt d.radical a ((replacementGeometry h d).exists_critical a p.start_color)
    rw [(replacementGeometry h d).distance_constant a p.start_color]
    change (cosetGraph d.radical).dist a (p.walk.getVert (p.walk.length-1)) <
      (replacementGeometry h d).b d.radical
    rw [p.dist_start (Nat.sub_le _ _),←p.length_eq_b]
    omega
  have hYt : V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical t :=
    inf_le_right.trans (Q_le_adjacent_h d.radical ht het)
  have hcomm : ⁅U d.radical a',Z d.radical a⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
    rw [commutator_comm]
    exact commutator_mono le_rfl (DistanceEight.U_le_Z d.radical a')
  have hRZa : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
    ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans (DistanceEight.U_le_Z d.radical a)
  let : IsElementaryAbelian 2 (X d.radical a) := omegaCenter_elementary _
  let : IsElementaryAbelian 2 (Z d.radical a) := IsElementaryAbelian.of_le
    ((replacementGeometry h d).omega_bound a p.start_color (by
      rw [(replacementGeometry h d).distance_constant a p.start_color]
      exact replacementDistance_pos h d))
  have hAA : ⁅U d.radical a',Z d.radical a⁆ ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (hcomm.trans hRZa).trans (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hAY : ⁅U d.radical a',Z d.radical a⁆ ≤ centralizer
      (V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) : Set (FreeAmalgam d.radical)) :=
    hcomm.trans (le_centralizer_iff.mp (critical_radius_intersection_centralizes (h := h) p hb))
  have hh := edge_commutator_control_at s hc u hR a' t p.end_color hct
    (Z d.radical a) _ hAt hYt hcard hAA hAY
  rw [commutator_comm (Z d.radical a') (Z d.radical a)] at hh
  rw [commutator_comm]
  exact hh.trans hRZa

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
