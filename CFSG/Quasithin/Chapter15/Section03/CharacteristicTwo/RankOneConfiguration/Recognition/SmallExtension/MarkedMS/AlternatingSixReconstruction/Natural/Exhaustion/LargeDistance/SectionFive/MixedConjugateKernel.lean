module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedRadius
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedLarge

/-!
# Generating conjugates and full mixed-plane kernel transfer

For a critical walk from a to a', write c = a' - 2. The completed radius
calculation gives |V_a : V_a intersect Q_c| = 2. Hence every backward
critical seed within radius two of a has the same commutator with Z_c.

Suppose two conjugate backward seeds both escape Q_c and their incident
edge kernels generate the stabilizer of a. Quadratic edge action places
the common line in both edge seeds, so the whole stabilizer of a fixes it.
Conjugating this equality and using full-cover kernel rigidity puts the
entire original seed kernel in the conjugated predecessor core. If the
conjugate seed is trapped in Q_c, the same containment follows directly.
Both central attachments are retained throughout this argument.

The checked six-letter mixed-plane generation calculation supplies the
required conjugating element at every actual edge. The final application
uses the original strict backward path, preserving its two transporters,
relative-normalizer generation, slice index and all shared walk vertices.
The internally imported MixedLarge certificate belongs to this same proof
family; its private declarations are not exposed in any public statement.

This closes the generating-conjugate kernel-transfer step. The trapped or
intermediate-central line alternatives still need the mixed-plane terminal
argument. Centrality at a does not contradict noncentrality at c. The larger
original-Sylow and distance-four branches, LargeDistanceInput, and the
unconditional replacement distance-two conclusion remain open.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), the two conjugate-seed cases in (5.11)(1), printed p.923, together
with the overlapping-path calculations of (5.10)--(5.11), pp.922--924.
The construction uses the original natural graph, minimum characteristic
replacement and inverse-conjugation action, with both moved covers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedConjugateKernel
local notation "S" => Equiv.Perm (Fin 6)
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

private theorem edge_coordinates {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    ∃ i : d.overgroup →* FreeAmalgam d.radical, Function.Injective i ∧
      i.range = stabilizer d.radical a ∧ d.radical.map i = Q d.radical t := by
  obtain ⟨g,hg|hg⟩ := (adjacent_iff_exists_common d.radical a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM d.radical)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective d.radical),?_,?_⟩
    · have he := stabilizer_act d.radical g (alpha d.radical)
      simpa only [i,alpha,act_mVertex,one_mul,stabilizer_m_base,Mbar,MonoidHom.range_comp] using he.symm
    · have he := Q_act d.radical g (beta d.radical)
      rw [Q_beta] at he
      simpa only [beta,act_hVertex,one_mul,map_map] using he.symm
  · rw [hg.1] at ha
    cases ha

/-- Every mixed-plane edge has a conjugate by the actual starting
stabilizer whose full kernel generates that stabilizer with the original
edge kernel. The replacement radical need not be a Sylow subgroup. -/
theorem mixed_generating_edge_conjugate_knownSimple
    (hb : 2 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ x ∈ stabilizer d.radical a,
      Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical a := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  obtain ⟨k,hk⟩ := MixedLarge.conjugate_generates u u
  obtain ⟨g,hg⟩ := s.surjective k
  have hm : (d.radical.map (MulAut.conj g).toMonoidHom).map s.projection =
      (d.radical.map s.projection).map (MulAut.conj k).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change s.projection (g*v*g⁻¹) = k*s.projection v*k⁻¹
    rw [map_mul,map_mul,map_inv,hg]
  have hgen : d.radical ⊔ d.radical.map (MulAut.conj g).toMonoidHom = ⊤ := by
    apply map_injective_of_ker_le s.projection
      ((s.projection_kernel.trans_le (replacement_core_le_radical h d)).trans le_sup_left) le_top
    rw [Subgroup.map_sup,hm,map_top_of_surjective s.projection s.surjective,
      SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him,sup_comm]
    exact hk
  obtain ⟨i,_,hir,hiR⟩ := edge_coordinates ha hat
  refine ⟨i g,hir ▸ (show i g ∈ i.range from ⟨g,rfl⟩),?_⟩
  have hmap : (d.radical.map (MulAut.conj g).toMonoidHom).map i =
      (d.radical.map i).map (MulAut.conj (i g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro v
    change i (g*v*g⁻¹) = i g*i v*(i g)⁻¹
    simp only [map_mul,map_inv]
  have hh := congrArg (Subgroup.map i) hgen
  rw [Subgroup.map_sup,hmap,hiR,←MonoidHom.range_eq_map,hir] at hh
  simpa only [Q_act,inv_inv] using hh

private theorem near_critical
    (hb : 4 < replacementDistance h d)
    {a a' z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hz : color d.radical z = false)
    (hnear : (cosetGraph d.radical).dist z a ≤ 2)
    (hout : ¬ Z d.radical z ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    Nonempty (CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2))) := by
  let c := p.walk.getVert (p.walk.length-2)
  have hpair : CriticalPair d.radical z c ((replacementGeometry h d).exists_critical z hz) := by
    refine ⟨?_,hout⟩
    apply le_antisymm _ (criticalDistance_le d.radical z _ hout)
    rw [(replacementGeometry h d).distance_constant z hz]
    have ht := (cosetGraph_connected d.radical).dist_triangle (u := z) (v := a) (w := c)
    have hac : (cosetGraph d.radical).dist a c = p.walk.length-2 :=
      p.dist_start (Nat.sub_le _ _)
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    change (cosetGraph d.radical).dist z c ≤ replacementDistance h d
    omega
  exact ⟨CriticalPath.ofPair (geometry := replacementGeometry h d) hz hpair⟩

omit [Finite G] in
private theorem edge_near {a z t : Vertex d.radical}
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t) :
    (cosetGraph d.radical).dist z a ≤ 2 := by
  have h1 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hzt)
  have h2 := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr
    (adjacent_symm d.radical hat))
  have ht := (cosetGraph_connected d.radical).dist_triangle (u := z) (v := t) (w := a)
  simpa only [h1,h2] using ht

/-- If both conjugate backward seeds escape the predecessor core, their
whole-radius line is fixed by the entire intermediate stabilizer. The
extra generation hypothesis concerns the two literal edge kernels. -/
theorem mixed_generating_conjugate_common_line_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hgen : Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical a)
    (hout : ¬ Z d.radical (act d.radical x⁻¹ z) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let c := p.walk.getVert (p.walk.length-2)
    ⁅Z d.radical z,Z d.radical c⁆ = ⁅Z d.radical (act d.radical x⁻¹ z),Z d.radical c⁆ ∧
      ⁅V d.radical a,Z d.radical c⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hnear := edge_near hat hzt
  have hfix : act d.radical x⁻¹ a = a := (stabilizer d.radical a).inv_mem hx
  have hnear' : (cosetGraph d.radical).dist (act d.radical x⁻¹ z) a ≤ 2 := by
    rw [←hfix,dist_act]
    exact hnear
  have hw : color d.radical (act d.radical x⁻¹ z) = false := by
    rw [action_preserves_color,q.start_color]
  obtain ⟨r⟩ := near_critical hb p hw hnear' hout
  have heq := (MixedRadius.mixed_near_seed_radius_commutator_knownSimple hb u him p q hnear).symm.trans
    (MixedRadius.mixed_near_seed_radius_commutator_knownSimple hb u him p r hnear')
  refine ⟨heq,?_⟩
  have hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom := by
    rw [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s,him]
    exact map_mono plus_le_D
  have hcQa : Z d.radical c ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt d.radical c ((replacementGeometry h d).exists_critical c q.end_color)
    rw [(replacementGeometry h d).distance_constant c q.end_color,SimpleGraph.dist_comm]
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    change (cosetGraph d.radical).dist a c < replacementDistance h d
    rw [p.dist_start (Nat.sub_le _ _)]
    omega
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.start_color] at hh
    cases he : color d.radical t <;> simp_all
  have hcQt : Z d.radical c ≤ Q d.radical t := hcQa.trans (Q_le_adjacent_h d.radical ht hat)
  have hQmap : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hcQt' : Z d.radical c ≤ Q d.radical (act d.radical x⁻¹ t) := by
    rw [Q_act,inv_inv]
    exact hcQa.trans (hQmap ▸ map_mono (Q_le_adjacent_h d.radical ht hat))
  have hline : ⁅Z d.radical z,Z d.radical c⁆ ≤ Z d.radical t :=
    (commutator_mono le_rfl hcQt).trans (cube_edge_seed_commutator_le s hc u hR q.start_color hzt)
  have hline' : ⁅Z d.radical z,Z d.radical c⁆ ≤ Z d.radical (act d.radical x⁻¹ t) := by
    rw [heq]
    exact (commutator_mono le_rfl hcQt').trans
      (cube_edge_seed_commutator_le s hc u hR hw ((adjacent_act_iff d.radical x⁻¹ _ _).mpr hzt))
  have hseed (v : Vertex d.radical) (hv : color d.radical v = true) :
      Z d.radical v ≤ centralizer (Q d.radical v : Set (FreeAmalgam d.radical)) := by
    intro y hy
    rw [Z,if_neg (by simp [hv])] at hy
    exact (mem_omegaCenter_iff.mp hy).2.2
  rw [MixedRadius.mixed_near_seed_radius_commutator_knownSimple hb u him p q hnear]
  apply le_centralizer_iff.mp
  rw [←hgen]
  exact sup_le (le_centralizer_iff.mp (hline.trans (hseed t ht)))
    (le_centralizer_iff.mp (hline'.trans (hseed _ (by rw [action_preserves_color,ht]))))

/-- The entire backward seed kernel lies in the conjugated predecessor
core. The escaping case uses the whole intermediate stabilizer's fixed
line; the trapped case follows directly, with all central attachments. -/
theorem mixed_generating_conjugate_kernel_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a a' z t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) z
      (p.walk.getVert (p.walk.length-2)))
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hgen : Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical a) :
    Z d.radical z ⊓ Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (act d.radical x (p.walk.getVert (p.walk.length-2))) := by
  let c := p.walk.getVert (p.walk.length-2)
  let w := act d.radical x⁻¹ z
  have hcancel : act d.radical x w = z := by
    dsimp only [w]
    rw [←act_mul,inv_mul_cancel,act_one]
  by_cases hout : Z d.radical w ≤ Q d.radical c
  · have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hout
    rw [←Z_act,←Q_act,hcancel] at hh
    exact inf_le_left.trans hh
  have hline := mixed_generating_conjugate_common_line_knownSimple hb u him p q hat hzt x hx hgen hout
  have hnear := edge_near hat hzt
  have hfix : act d.radical x⁻¹ a = a := (stabilizer d.radical a).inv_mem hx
  have hnear' : (cosetGraph d.radical).dist w a ≤ 2 := by
    rw [show w = act d.radical x⁻¹ z from rfl,←hfix,dist_act]
    exact hnear
  have hw : color d.radical w = false := (action_preserves_color d.radical _ _).trans q.start_color
  obtain ⟨r⟩ := near_critical hb p hw hnear' hout
  obtain ⟨r'⟩ : Nonempty (CriticalPath d.radical (replacementGeometry h d) z (act d.radical x c)) := by
    rw [←hcancel]
    exact ⟨r.act x⟩
  let H := ⁅Z d.radical z,Z d.radical c⁆
  have hHC : H ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    change ⁅Z d.radical z,Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤ _
    rw [←MixedRadius.mixed_near_seed_radius_commutator_knownSimple hb u him p q hnear]
    exact hline.2
  have hHmap : H.map (MulAut.conj x⁻¹).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer _ ((le_centralizer_iff.mp hHC)
        ((stabilizer d.radical a).inv_mem hx)))
  have heq : ⁅Z d.radical z,Z d.radical c⁆ = ⁅Z d.radical z,Z d.radical (act d.radical x c)⁆ := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hline.1
    change H.map (MulAut.conj x⁻¹).toMonoidHom = _ at hh
    rw [hHmap,map_commutator,←Z_act,←Z_act,hcancel] at hh
    exact hh
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hq : (Q d.radical c).relIndex (Z d.radical z) < 4 := by
    rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him q).1]
    decide
  have hr : (Q d.radical (act d.radical x c)).relIndex (Z d.radical z) < 4 := by
    rw [(MixedLarge.mixed_critical_indices_two_knownSimple hb u him r').1]
    decide
  exact (small_critical_equal_commutators_kernel s hc q r' hq hr heq).le.trans inf_le_right

/-- The original strict backward construction supplies the new conjugate
kernel containment with no generation or radius-index premise. Both
transporters, every shared walk vertex, and the strict slice survive. The
conjugate seed is trapped, or the intrinsic radius line is central at the
original start; it remains noncentral at the predecessor in either case. -/
theorem mixed_backward_conjugate_kernel_knownSimple
    (hb : 4 < replacementDistance h d) (u : S)
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a') :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      (normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
        stabilizer d.radical (alpha d.radical)) ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) ∧
      ∃ y ∈ stabilizer d.radical (alpha d.radical), act d.radical y (p.walk.getVert 1) = t ∧
      ∃ k ∈ stabilizer d.radical t,
      ∃ q : CriticalPath d.radical (replacementGeometry h d)
          (act d.radical k (act d.radical y (p.walk.getVert 2)))
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k (act d.radical y (p.walk.getVert 2)))) =
        (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (p.walk.getVert 2)) ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical k (act d.radical y (p.walk.getVert 2)))) ∧
        ∃ x ∈ stabilizer d.radical (alpha d.radical),
          Q d.radical t ⊔ Q d.radical (act d.radical x⁻¹ t) = stabilizer d.radical (alpha d.radical) ∧
          Z d.radical (act d.radical k (act d.radical y (p.walk.getVert 2))) ⊓
            Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
              Q d.radical (act d.radical x (p.walk.getVert (p.walk.length-2))) ∧
          (Z d.radical (act d.radical x⁻¹ (act d.radical k (act d.radical y (p.walk.getVert 2)))) ≤
              Q d.radical (p.walk.getVert (p.walk.length-2)) ∨
            ⁅V d.radical (alpha d.radical),Z d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
              centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) := by
  obtain ⟨t,hat,hgen,y,hy,hyt,k,hk,q,hq1,hover,hidx,hstrict⟩ :=
    MixedLarge.mixed_backward_path_of_four_lt_knownSimple hb u him p
  obtain ⟨x,hx,hpair⟩ := mixed_generating_edge_conjugate_knownSimple (by omega) u him rfl hat
  have hzt : Adjacent d.radical (act d.radical k (act d.radical y (p.walk.getVert 2))) t := by
    have hl : 0 < q.walk.length := q.length_eq_b ▸ replacementDistance_pos h d
    have hh := q.walk.adj_getVert_succ (i := 0) hl
    rw [SimpleGraph.Walk.getVert_zero,hq1] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  refine ⟨t,hat,hgen,y,hy,hyt,k,hk,q,hq1,hover,hidx,hstrict,x,hx,hpair,
    mixed_generating_conjugate_kernel_knownSimple hb u him p q hat hzt x hx hpair,?_⟩
  by_cases hout : Z d.radical (act d.radical x⁻¹ (act d.radical k (act d.radical y (p.walk.getVert 2)))) ≤
      Q d.radical (p.walk.getVert (p.walk.length-2))
  · exact Or.inl hout
  · exact Or.inr (mixed_generating_conjugate_common_line_knownSimple hb u him p q hat hzt x hx hpair hout).2

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.MixedConjugateKernel
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
