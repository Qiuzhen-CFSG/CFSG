module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.BackwardCentral

/-!
# The full backward core commutator

Under failure of radius escape, an eligible backward seed lies in the
predecessor core. Its nonzero reverse-kernel commutator has order two,
while the commutator with the entire predecessor core has order at most
two. Inclusion therefore identifies the two. The starting radius lies
between that backward seed and the predecessor core, so its commutator
is the same line as well. The resulting line is independent of the
eligible backward choice and is central at the original starting vertex.

In the small critical-image branch the full reverse kernel is invariant
under the actual last edge kernel. This kernel also normalizes the
predecessor core, hence normalizes their order-at-most-two commutator and
fixes it pointwise. The commutator is consequently in the last edge seed.
This argument does not require predecessor-slice placement and retains
both central covers, including the order-32 cover's central line.

The final theorem applies both identifications to the original full-point
characteristic replacement. It constructs the generating edge and eligible
backward vertex and retains the same critical path, the canonical quotient
projection, and the commutator in both edge seeds.

Source: Meierfrankenfeld--Stellmacher (1993), the backward line calculation
in (5.7)--(5.8), printed pp.919--920. Predecessor-slice containment, the
remaining radical-image cases, exact-four exclusion, intermediate R4/R6
noncentrality, and both terminal contradictions remain unproved here.
This does not establish LargeDistanceInput or unconditional distance two.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- Under failure of radius escape, the eligible backward line is the
whole reverse-kernel commutator with the predecessor core and the radius.
In particular it is independent of the choice of eligible backward seed. -/
theorem eligible_backward_core_line
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (hgen : Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical))
    (hel : ¬ U d.radical c ≤ B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _))
    (hbad : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
    let D := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
    D = ⁅K,Z d.radical c⁆ ∧ D = ⁅K,V d.radical (alpha d.radical)⁆ ∧
      Nat.card D = 2 ∧ D ≤ Z d.radical t ∧
      D ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ¬ D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
  let D := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hcV : Z d.radical c ≤ V d.radical (alpha d.radical) :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hcQ := hcV.trans hbad
  have hline := eligible_backward_failure_line s hc hb u hR p hat hct hgen hel hcQ
  have hs : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hbound := small_critical_kernel_predecessor_card s hc hb u hR p hs
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hZeG : Z d.radical a' ≤ stabilizer d.radical (p.walk.getVert (p.walk.length-2)) := by
    apply Z_le_stabilizer_of_dist_le a' ((replacementGeometry h d).exists_critical _ p.end_color)
    rw [(replacementGeometry h d).distance_constant _ p.end_color,SimpleGraph.dist_comm,p.dist_end]
    have hh := p.length_eq_b
    change p.walk.length-(p.walk.length-2) ≤ replacementDistance h d
    omega
  have hDQ : D ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    le_normalizer_iff_commutator_le_right.mp
      ((inf_le_left.trans hZeG).trans (Q_normalized d.radical _))
  let := finite_stabilizer d.radical (p.walk.getVert (p.walk.length-2))
  let : Finite D := Finite.of_injective
    (inclusion (hDQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have heq : D = ⁅K,Z d.radical c⁆ :=
    (eq_of_le_of_card_ge (commutator_mono le_rfl hcQ) (by
      change Nat.card D ≤ Nat.card (⁅K,Z d.radical c⁆ : Subgroup (FreeAmalgam d.radical))
      exact hbound.trans_eq hline.2.2.1.symm)).symm
  have hcentral := eligible_backward_line_central s hc hb u hR p hat hct hgen hel hcQ
  refine ⟨heq,?_,?_,?_,?_,?_⟩
  · exact le_antisymm (heq.le.trans (commutator_mono le_rfl hcV)) (commutator_mono le_rfl hbad)
  · exact (congrArg (fun H : Subgroup (FreeAmalgam d.radical) => Nat.card H) heq).trans hline.2.2.1
  · exact heq.le.trans hcentral.2.1
  · exact heq.le.trans hcentral.2.2
  · intro hh
    exact eligible_backward_kernel_not_central s hc hb p hs hat hct hgen hel hcQ (heq.ge.trans hh)

include s in
/-- The entire reverse-kernel commutator with the predecessor core lies in
the last edge seed. This uses the actual end-kernel invariance, without
predecessor-slice placement. -/
theorem small_critical_predecessor_commutator_le_last_seed
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hR : d.radical.map s.projection ≤ pointCore.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ⁅Z d.radical a' ⊓ Q d.radical a,Q d.radical (p.walk.getVert (p.walk.length-2))⁆ ≤
      Z d.radical (p.walk.getVert (p.walk.length-1)) := by
  let c := p.walk.getVert (p.walk.length-2)
  let t := p.walk.getVert (p.walk.length-1)
  let K := Z d.radical a' ⊓ Q d.radical a
  let D := ⁅K,Q d.radical c⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hct : Adjacent d.radical c t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have het : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical het
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  let := pointCore_elementary
  let : IsElementaryAbelian 2 (pointCore.map (MulAut.conj u).toMonoidHom) := IsElementaryAbelian.map _
  let helem : IsElementaryAbelian 2 (d.radical.map s.projection) := IsElementaryAbelian.of_le hR
  have hab : ⁅d.radical.map s.projection,d.radical.map s.projection⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr
      (le_centralizer_iff_isMulCommutative.mpr helem.toIsMulCommutative)
  have hKn : Q d.radical t ≤ normalizer (K : Set (FreeAmalgam d.radical)) :=
    (small_critical_end_kernels_normalized_of_abelian_image s hc hab p hsmall).2
  have hQn : Q d.radical t ≤ normalizer (Q d.radical c : Set (FreeAmalgam d.radical)) :=
    (show Q d.radical t ≤ stabilizer d.radical c from
      fun _ hx => hx.2 _ (adjacent_symm d.radical hct)).trans (Q_normalized d.radical c)
  have hDn : Q d.radical t ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅K,Q d.radical c⁆ : Subgroup (FreeAmalgam d.radical)).map (MulAut.conj g).toMonoidHom = _
    rw [map_commutator]
    exact congrArg₂ (fun A B : Subgroup (FreeAmalgam d.radical) => ⁅A,B⁆)
      (mem_normalizer_iff_map_conj_eq.mp (hKn hg))
      (mem_normalizer_iff_map_conj_eq.mp (hQn hg))
  have hDK : D ≤ K := le_normalizer_iff_commutator_le_left.mp
    ((Q_le_adjacent_h d.radical ht hct).trans hKn)
  let := finite_Z d.radical a'
  let : Finite D := Finite.of_injective (inclusion (hDK.trans inf_le_left)) (inclusion_injective _)
  have hcard : Nat.card D ≤ 2 := small_critical_kernel_predecessor_card s hc hb u hR p hsmall
  have hfix : D ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) := by
    by_cases he : D = ⊥
    · rw [he]; exact bot_le
    · have hh := (one_lt_card_iff_ne_bot D).mpr he
      exact le_centralizer_iff.mp (hDn.trans (normalizer_le_centralizer_of_card_two D (by omega)))
  have hZQ : Z d.radical a' ≤ Q d.radical a' := by
    apply Z_le_Q_of_dist_lt d.radical a' ((replacementGeometry h d).exists_critical _ p.end_color)
    rw [SimpleGraph.dist_self,(replacementGeometry h d).distance_constant _ p.end_color]
    exact replacementDistance_pos h d
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  intro x hx
  change x ∈ Z d.radical t
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨((hDK.trans inf_le_left).trans (hZQ.trans (Q_le_adjacent_h d.radical ht het))) hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hDK.trans inf_le_left) hx),hfix hx⟩

/-- The actual full-point replacement identifies its reverse-kernel core
commutator with the backward line and the entire starting-radius commutator.
The same line lies in the last edge seed, is central at the original start,
and is noncentral at the constructed backward vertex. No predecessor-slice
placement is assumed. -/
theorem radius_failure_backward_core_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    (u : Equiv.Perm (Fin 6))
    (hfull : d.radical.map (SourceReduction.projection h e hz hn d) =
      pointCore.map (MulAut.conj u).toMonoidHom)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hbad : V d.radical (alpha d.radical) ≤ Q d.radical (p.walk.getVert (p.walk.length-2))) :
    let K := Z d.radical a' ⊓ Q d.radical (alpha d.radical)
    let D := ⁅K,Q d.radical (p.walk.getVert (p.walk.length-2))⁆
    ∃ t c, Adjacent d.radical (alpha d.radical) t ∧ Adjacent d.radical c t ∧
      Q d.radical t ⊔ Z d.radical a' = stabilizer d.radical (alpha d.radical) ∧
      D = ⁅K,Z d.radical c⁆ ∧ D = ⁅K,V d.radical (alpha d.radical)⁆ ∧
      Nat.card D = 2 ∧
      D ≤ Z d.radical t ⊓ Z d.radical (p.walk.getVert (p.walk.length-1)) ∧
      D ≤ centralizer (stabilizer d.radical (alpha d.radical) : Set (FreeAmalgam d.radical)) ∧
      ¬ D ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hfull' : d.radical.map s.projection = pointCore.map (MulAut.conj u).toMonoidHom := by
    rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  obtain ⟨t,hat,hgen⟩ := full_point_generating_neighbor s hc u hfull' p
  obtain ⟨c,hct,hel⟩ := exists_eligible_neighbor_at_edge s hc hb rfl hat
  have hcore := eligible_backward_core_line s hc hb u hfull'.le p hat hct hgen hel hbad
  have hdist : (cosetGraph d.radical).dist c (alpha d.radical) ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t (alpha d.radical) = 1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle
      (u := c) (v := t) (w := alpha d.radical)
  have hcQ : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) :=
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)).trans hbad
  have hline := eligible_backward_failure_line s hc hb u hfull'.le p hat hct hgen hel hcQ
  have hs : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  exact ⟨t,c,hat,hct,hgen,hcore.1,hcore.2.1,hcore.2.2.1,
    le_inf hcore.2.2.2.1 (small_critical_predecessor_commutator_le_last_seed s hc hb u hfull'.le p hs),
    hcore.2.2.2.2.1,hcore.2.2.2.2.2⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
