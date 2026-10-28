module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.CubePairedKernel

/-!
# The trapped reverse-kernel line and its conjugate

In the three-pair branch, fix a small critical path from a to a', a backward
vertex c through the chosen edge t, and assume its backward shift is trapped.
If Z_{a'} fails to normalize Z_c Z_a, the whole trapped radius
W = V_a intersect Q_{a'-1} has commutator of order at most two with the full
reverse critical kernel F = Z_{a'} intersect Q_a. Indeed, the fixed-hyperplane
comparison on both moved covers would otherwise give [Z_{a'},W] <= Z_a:
the entire radius bound puts [W,F] in Z_a. Since Z_c lies in W, that would
normalize the forbidden product. The selected commutator is nonzero, so
[W,F] equals the actual selected line [Z_c,F].

For two trapped paths related by the original conjugator x, the second
backward seed transported by x lies in the first trapped radius. Thus the
second kernel commutator transports into the first line. The strict slice
index greater than two supplies its nontriviality, giving equality and order
two for both lines. The selected line consequently lies in both actual
backward seeds and centralizes both corresponding neighborhood kernels.
The separated-kernel theorem also proves that x does not normalize that line.
These conclusions use the literal right-coset action and its inverse
conjugation convention throughout.

The nonsylow consumer constructs the full three-pair image internally and
retains the same neighbor transporter, cubic, generating pair and both
complete overlapping critical walks. It has no new action or normalization
premise. Both central covers of orders sixteen and thirty-two, and their full
central attachments, are retained. Exclusion of this conjugate-line pair
still requires the source's common-fixer argument; no whole-stabilizer
centrality is inferred from order two. The remaining shifts, terminal
exclusions, original Sylow branches and distance-four arguments are open.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (3.3)(ii), (5.6)(b) and (5.7), printed pp.866--867,917--919.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped commutatorElement IsMulCommutative Pointwise
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)
local notation "S" => Equiv.Perm (Fin 6)

include s in
/-- The entire trapped part of the radius has at most line movement on the
reverse critical kernel, if the selected endpoint fails normalization. -/
theorem cube_trapped_radius_kernel_card_le_two
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical a' ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    Nat.card (⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-1)),
      Z d.radical a' ⊓ Q d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
  by_contra hcard
  have hlarge := Nat.lt_of_not_ge hcard
  let F := Z d.radical a' ⊓ Q d.radical a
  let v := p.walk.getVert (p.walk.length-1)
  let W := V d.radical a ⊓ Q d.radical v
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hev : Adjacent d.radical a' v := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hv : color d.radical v = true := by
    have hh := adjacent_color_ne d.radical hev
    rw [p.end_color] at hh
    cases he : color d.radical v <;> simp_all
  have hpre : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤ Q d.radical v := by
    apply Q_le_adjacent_h d.radical hv
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hAv : Z d.radical a ≤ Q d.radical v := by
    apply Z_le_Q_of_dist_lt d.radical _ ((replacementGeometry h d).exists_critical _ p.start_color)
    rw [(replacementGeometry h d).distance_constant _ p.start_color,p.dist_start (Nat.sub_le _ _)]
    have he : p.walk.length = replacementDistance h d := p.length_eq_b
    change p.walk.length-1 < replacementDistance h d
    omega
  have hfixed : F = Z d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color)))
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←C_eq_Q s hc a p.start_color]
      exact ⟨critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical hx.1,hx.2⟩
  let := finite_Z d.radical a'
  let : Finite (U d.radical a') := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a')) (inclusion_injective _)
  have hindex : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a') ≤ 2 := by
    have hQC : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a p.start_color))
    exact ((relIndex_le_of_le_left hQC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a') index_ne_zero_of_finite)).trans_eq
        (small_critical_indices s hc p hsmall).2
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle (u := c) (v := t) (w := a)
  have hCW : Z d.radical c ≤ W := le_inf
    ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)) (hbad.trans hpre)
  have hlarge' : 2 < Nat.card (⁅Z d.radical a' ⊓
      centralizer (Z d.radical a : Set (FreeAmalgam d.radical)),W⁆ : Subgroup (FreeAmalgam d.radical)) := by
    rw [←hfixed,commutator_comm]
    exact hlarge
  have hcmp := cube_edge_large_fixed_commutator s hc u hR p.end_color hev
    (Z d.radical a) W hAv inf_le_right p.critical.2 hindex hlarge'
  rw [←hfixed,commutator_comm F W] at hcmp
  have hH : ⁅W,F⁆ ≤ Z d.radical a :=
    (commutator_mono inf_le_left inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb u hR a p.start_color)
  have hcrit : ⁅Z d.radical a',Z d.radical a⁆ ≤ Z d.radical a :=
    le_normalizer_iff_commutator_le_right.mp
      ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical).trans (Z_normalized d.radical a))
  have hmove : ⁅Z d.radical a',Z d.radical c⁆ ≤ Z d.radical a :=
    (commutator_mono le_rfl hCW).trans (hcmp.trans (sup_le hH hcrit))
  have htotal := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
    (Z d.radical c) (Z d.radical a) (Z d.radical a') (Z d.radical a)
    (Z_normalized d.radical a)
    ((hCW.trans inf_le_left).trans ((replacementGeometry h d).V_local a p.start_color (by
      rw [(replacementGeometry h d).distance_constant _ p.start_color]; exact hb)))
    (Z_le_stabilizer d.radical a) (by rwa [commutator_comm]) (by rwa [commutator_comm])
  exact hnorm (le_normalizer_iff_commutator_le_left.mpr (htotal.trans le_sup_right))


include s in
/-- All trapped radius movement equals the selected nonzero line. This is
an equality for the literal intersection with the last edge kernel. -/
theorem cube_trapped_radius_kernel_eq_selected
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hnorm : ¬ Z d.radical a' ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical a⁆
    Nat.card H = 2 ∧
      ⁅V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-1)),
        Z d.radical a' ⊓ Q d.radical a⁆ = H := by
  let F := Z d.radical a' ⊓ Q d.radical a
  let H := ⁅Z d.radical c,F⁆
  let W := V d.radical a ⊓ Q d.radical (p.walk.getVert (p.walk.length-1))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
    have h1 : (cosetGraph d.radical).dist c t=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
    have h2 : (cosetGraph d.radical).dist t a=1 :=
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
    simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle (u := c) (v := t) (w := a)
  have hCV : Z d.radical c ≤ V d.radical a :=
    (Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist)
  have hVG := (replacementGeometry h d).V_local a p.start_color
    (by rw [(replacementGeometry h d).distance_constant _ p.start_color]; exact hb)
  have hv : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
    have hh := adjacent_color_ne d.radical
      ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)))
    rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length,p.end_color] at hh
    cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
  have hpre : Q d.radical (p.walk.getVert (p.walk.length-2)) ≤
      Q d.radical (p.walk.getVert (p.walk.length-1)) := by
    apply Q_le_adjacent_h d.radical hv
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hCW : Z d.radical c ≤ W := le_inf hCV (hbad.trans hpre)
  have hHle : H ≤ ⁅W,F⁆ := commutator_mono hCW le_rfl
  have hwhole : ⁅W,F⁆ ≤ Z d.radical a :=
    (commutator_mono inf_le_left inf_le_right).trans
      (cube_radius_core_commutator_le_seed s hc hb u hR a p.start_color)
  have hne : H ≠ ⊥ := by
    intro hzero
    have hmove := small_critical_predecessor_commutator s hc hb p hsmall
      (Z d.radical c) hbad (commutator_eq_bot_iff_le_centralizer.mp hzero)
    have hZmove : ⁅Z d.radical a,Z d.radical a'⁆ ≤ Z d.radical a :=
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
        (DistanceEight.U_le_Z d.radical _)
    have hh := commutator_sup_le_of_relative_normal (stabilizer d.radical a)
      (Z d.radical c) (Z d.radical a) (Z d.radical a') (Z d.radical a)
      (Z_normalized d.radical _) (hCV.trans hVG)
      (Z_le_stabilizer d.radical _) hmove hZmove
    exact hnorm (le_normalizer_iff_commutator_le_left.mpr (hh.trans le_sup_right))
  let := finite_Z d.radical a
  let : Finite (⁅W,F⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hwhole) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHle) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot _).mpr hne
  have hbound := cube_trapped_radius_kernel_card_le_two s hc hb u hR p hsmall hat hct hbad hnorm
  have hcard : Nat.card H = 2 := by
    have hh := card_le_of_le hHle
    change Nat.card (⁅W,F⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 at hbound
    omega
  refine ⟨hcard,(eq_of_le_of_card_ge hHle ?_).symm⟩
  rw [hcard]
  exact hbound

include s in
/-- For the same conjugator relating the two entire paths, the other
trapped kernel commutator transports into the selected obstruction line. -/
theorem cube_paired_kernel_conjugate_le_selected
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hR : d.radical.map s.projection ≤ (D 6).map (MulAut.conj u).toMonoidHom)
    {a a' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (q : CriticalPath d.radical (replacementGeometry h d) a (act d.radical x a'))
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hnorm : ¬ Z d.radical a' ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    (⁅Z d.radical c,Z d.radical (act d.radical x a') ⊓ Q d.radical a⁆).map
      (MulAut.conj x).toMonoidHom ≤ ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical a⁆ := by
  have hQ : (Q d.radical a).map (MulAut.conj x).toMonoidHom = Q d.radical a :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a hx)
  have hZ : (Z d.radical (act d.radical x a')).map (MulAut.conj x).toMonoidHom = Z d.radical a' := by
    have he := Z_act d.radical x⁻¹ (act d.radical x a')
    simpa only [inv_inv,←act_mul,mul_inv_cancel,act_one] using he.symm
  rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj x).injective,hQ,hZ]
  have heq := (cube_trapped_radius_kernel_eq_selected s hc hb u hR p hsmall hat hct hpbad hnorm).2
  rw [←heq]
  apply commutator_mono _ le_rfl
  apply le_inf
  · have hdist : (cosetGraph d.radical).dist c a ≤ 2 := by
      have h1 : (cosetGraph d.radical).dist c t=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hct)
      have h2 : (cosetGraph d.radical).dist t a=1 :=
        SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr (adjacent_symm d.radical hat))
      simpa only [h1,h2] using (cosetGraph_connected d.radical).dist_triangle (u := c) (v := t) (w := a)
    have hV := map_mono (f := (MulAut.conj x).toMonoidHom)
      ((Z_le_localZSpan d.radical _ _).trans (localZSpan_le_V d.radical hdist))
    have heV : (V d.radical a).map (MulAut.conj x).toMonoidHom = V d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized d.radical a hx)
    rwa [heV] at hV
  · have hlen : q.walk.length = p.walk.length := q.length_eq_b.trans p.length_eq_b.symm
    have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hqbad
    rw [hlen,hq] at hh
    have he := Q_act d.radical x⁻¹ (act d.radical x (p.walk.getVert (p.walk.length-2)))
    simp only [inv_inv,←act_mul,mul_inv_cancel,act_one] at he
    rw [←he] at hh
    apply hh.trans
    have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
    have hv : color d.radical (p.walk.getVert (p.walk.length-1)) = true := by
      have ha := adjacent_color_ne d.radical
        ((cosetGraph_adj d.radical _ _).mp (p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)))
      rw [show p.walk.length-1+1=p.walk.length by omega,p.walk.getVert_length,p.end_color] at ha
      cases he : color d.radical (p.walk.getVert (p.walk.length-1)) <;> simp_all
    apply Q_le_adjacent_h d.radical hv
    have ha := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1=p.walk.length-1 by omega] at ha
    exact (cosetGraph_adj d.radical _ _).mp ha



include s in
/-- The two trapped obstructions are distinct lines in the same conjugacy
orbit under the retained path transporter. Its normalization cannot be
inferred from either line's order or its edge centrality. -/
theorem cube_paired_trapped_kernel_orbit
    (hc : DistanceTwo.CentralLayer d) (hb : 2 < replacementDistance h d)
    (u : S) (hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom)
    {a' b' c t : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hps : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hat : Adjacent d.radical (alpha d.radical) t) (hct : Adjacent d.radical c t)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical (alpha d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) b')
    (hq : ∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i))
    (hqs : (Q d.radical b').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hgen : Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical b' =
      stabilizer d.radical (alpha d.radical))
    (hpbad : Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hqbad : Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical c))
    (hnorm : ¬ Z d.radical a' ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical (alpha d.radical) : Subgroup (FreeAmalgam d.radical)) :
        Set (FreeAmalgam d.radical))) :
    let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆
    let H' := ⁅Z d.radical c,Z d.radical b' ⊓ Q d.radical (alpha d.radical)⁆
    Nat.card H = 2 ∧ Nat.card H' = 2 ∧
      H'.map (MulAut.conj x).toMonoidHom = H ∧
      H ≤ Z d.radical c ⊓ Z d.radical (act d.radical x⁻¹ c) ∧
      H ≤ centralizer ((Q d.radical c ⊔ Q d.radical (act d.radical x⁻¹ c) :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
      H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
      ¬ H' ≤ H ∧ ¬ x ∈ normalizer (H : Set (FreeAmalgam d.radical)) := by
  have hb' : b' = act d.radical x a' := by
    have hh := hq p.walk.length
    have hlen : p.walk.length = q.walk.length := p.length_eq_b.trans q.length_eq_b.symm
    rw [p.walk.getVert_length,hlen,q.walk.getVert_length] at hh
    exact hh
  subst b'
  let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆
  let H' := ⁅Z d.radical c,Z d.radical (act d.radical x a') ⊓ Q d.radical (alpha d.radical)⁆
  obtain ⟨hcard,hcentral,hsep⟩ := cube_paired_trapped_kernels_separate s hc hb u hfull
    p q hps hqs hat hct hgen hpbad hqbad hindex hnorm
  have hcmp := cube_paired_kernel_conjugate_le_selected s hc hb u hfull.le
    p hps hat hct x hx q hq hpbad hqbad hnorm
  have hH' : H' ≤ Z d.radical (alpha d.radical) :=
    (cube_backward_kernel_le_edge_seeds s hc hb u hfull.le q hat hct hqbad).2.trans inf_le_left
  let := finite_Z d.radical (alpha d.radical)
  let : Finite H' := Finite.of_injective (inclusion hH') (inclusion_injective _)
  have hH : H ≤ Z d.radical (alpha d.radical) :=
    (cube_backward_kernel_le_edge_seeds s hc hb u hfull.le p hat hct hpbad).2.trans inf_le_left
  let : Finite H := Finite.of_injective (inclusion hH) (inclusion_injective _)
  have hne : H' ≠ ⊥ := fun hz => hsep (hz.trans_le bot_le)
  have hpos : 1 < Nat.card H' := (one_lt_card_iff_ne_bot _).mpr hne
  have hcard' : Nat.card H' = 2 := by
    have hh := card_le_of_le hcmp
    rw [card_map_of_injective (MulAut.conj x).injective,hcard] at hh
    change Nat.card H' ≤ 2 at hh
    omega
  have heq : H'.map (MulAut.conj x).toMonoidHom = H := eq_of_le_of_card_ge hcmp (by
    rw [card_map_of_injective (MulAut.conj x).injective,hcard,hcard'])
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    change false ≠ color d.radical t at hh
    cases he : color d.radical t <;> simp_all
  have hcol : color d.radical c = false := by
    have hh := adjacent_color_ne d.radical hct
    rw [ht] at hh
    cases he : color d.radical c <;> simp_all
  have hHc : H ≤ Z d.radical c :=
    ((cube_backward_kernel_le_edge_seeds s hc hb u hfull.le p hat hct hpbad).1.trans inf_le_left).trans
      (adjacent_Z_le d.radical hcol hct)
  have hH'c : H' ≤ Z d.radical c :=
    ((cube_backward_kernel_le_edge_seeds s hc hb u hfull.le q hat hct hqbad).1.trans inf_le_left).trans
      (adjacent_Z_le d.radical hcol hct)
  have hHxc : H ≤ Z d.radical (act d.radical x⁻¹ c) := by
    rw [Z_act,inv_inv,←heq]
    exact map_mono hH'c
  have hcc : H ≤ centralizer ((Q d.radical c ⊔ Q d.radical (act d.radical x⁻¹ c) :
      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mpr
    apply sup_le
    · exact le_centralizer_iff.mp (hHc.trans
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical c hcol)))
    · exact le_centralizer_iff.mp (hHxc.trans
        (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical _
          ((action_preserves_color d.radical x⁻¹ c).trans hcol))))
  refine ⟨hcard,hcard',heq,le_inf hHc hHxc,hcc,hcentral,hsep,?_⟩
  intro hxn
  have hfix : H.map (MulAut.conj x).toMonoidHom = H := mem_normalizer_iff_map_conj_eq.mp hxn
  have hh : H' = H := (Subgroup.map_injective (MulAut.conj x).injective)
    (heq.trans hfix.symm)
  exact hsep hh.le

include e hz hn in
/-- The original nonsylow strict-slice application retains the same cubic,
neighbor conjugator and overlapping walks. If neither backward shift is
critical, both obstructions are lines and the given cubic transports one
onto the other; it does not normalize the selected line. -/
theorem nonsylow_strict_small_backward_kernel_orbit_knownSimple
    (hb4 : 4 < replacementDistance h d)
    (hns : ¬ ∃ T : Sylow 2 (L ⊔ R : Subgroup G),
      (T : Subgroup (L ⊔ R : Subgroup G)) = R.subgroupOf (L ⊔ R))
    {a' delta : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4)
    (hdelta : Adjacent d.radical delta (p.walk.getVert 1))
    (hindex : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical delta)) :
    ∃ t, Adjacent d.radical (alpha d.radical) t ∧
      ∃ g ∈ stabilizer d.radical (alpha d.radical),
        act d.radical g (p.walk.getVert 1) = t ∧
        Adjacent d.radical (act d.radical g delta) t ∧
        2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
          (U d.radical (act d.radical g delta)) ∧
        ∃ x ∈ Ltilde d.radical (alpha d.radical),
          x ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧
          x^3 ∈ Q d.radical (alpha d.radical) ∧
          ∃ q : CriticalPath d.radical (replacementGeometry h d)
              (alpha d.radical) (act d.radical x a'),
            (∀ i, q.walk.getVert i = act d.radical x (p.walk.getVert i)) ∧
            (Q d.radical (act d.radical x a')).relIndex (Z d.radical (alpha d.radical)) < 4 ∧
            Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') =
              stabilizer d.radical (alpha d.radical) ∧
            let c := act d.radical g delta
            let P := Z d.radical c ⊔ Z d.radical (alpha d.radical)
            let H := ⁅Z d.radical c,Z d.radical a' ⊓ Q d.radical (alpha d.radical)⁆
            let H' := ⁅Z d.radical c,Z d.radical (act d.radical x a') ⊓ Q d.radical (alpha d.radical)⁆
            (¬ Z d.radical a' ≤ normalizer (P : Set (FreeAmalgam d.radical)) ∨
              ¬ Z d.radical (act d.radical x a') ≤ normalizer (P : Set (FreeAmalgam d.radical))) ∧
            ((∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (p.walk.getVert (p.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ p.walk.length-2, v.walk.getVert (i+2)=p.walk.getVert i) ∨
              (∃ v : CriticalPath d.radical (replacementGeometry h d) c
                (q.walk.getVert (q.walk.length-2)), v.walk.getVert 1=t ∧
                ∀ i ≤ q.walk.length-2, v.walk.getVert (i+2)=q.walk.getVert i) ∨
              (Z d.radical c ≤ Q d.radical (p.walk.getVert (p.walk.length-2)) ∧
                Z d.radical c ≤ Q d.radical (q.walk.getVert (q.walk.length-2)) ∧
                ((¬ Z d.radical a' ≤ normalizer (P : Set (FreeAmalgam d.radical)) ∧
                    Nat.card H=2 ∧ Nat.card H'=2 ∧
                    H'.map (MulAut.conj x).toMonoidHom = H ∧
                    H ≤ Z d.radical c ⊓ Z d.radical (act d.radical x⁻¹ c) ∧
                    H ≤ centralizer ((Q d.radical c ⊔ Q d.radical (act d.radical x⁻¹ c) :
                      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
                    H ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧ ¬ H' ≤ H ∧
                    ¬ x ∈ normalizer (H : Set (FreeAmalgam d.radical))) ∨
                  (¬ Z d.radical (act d.radical x a') ≤ normalizer (P : Set (FreeAmalgam d.radical)) ∧
                    Nat.card H'=2 ∧ Nat.card H=2 ∧
                    H.map (MulAut.conj x⁻¹).toMonoidHom = H' ∧
                    H' ≤ Z d.radical c ⊓ Z d.radical (act d.radical x c) ∧
                    H' ≤ centralizer ((Q d.radical c ⊔ Q d.radical (act d.radical x c) :
                      Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) ∧
                    H' ≤ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) ∧ ¬ H ≤ H' ∧
                    ¬ x⁻¹ ∈ normalizer (H' : Set (FreeAmalgam d.radical)))))) := by
  obtain ⟨t,hat,g,hg,hgt,hct,hstrict,x,hx,hxN,hx3,q,hq,hqs,hgen,hnorm,halt⟩ :=
    nonsylow_strict_small_backward_separated_obstruction_knownSimple (e := e) (hz := hz) (hn := hn)
      hb4 hns p hsmall hdelta hindex
  refine ⟨t,hat,g,hg,hgt,hct,hstrict,x,hx,hxN,hx3,q,hq,hqs,hgen,hnorm,?_⟩
  rcases halt with hp | hq' | ⟨hpbad,hqbad,hrest⟩
  · exact Or.inl hp
  · exact Or.inr (Or.inl hq')
  · refine Or.inr (Or.inr ⟨hpbad,hqbad,?_⟩)
    have hb : 2 < replacementDistance h d := by omega
    let s := fullSymmetricAction_knownSimple h e hz hn d hb
    have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
    obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
      (e := e) (hz := hz) (hn := hn) hb4 hns
    have hfull : d.radical.map s.projection = (D 6).map (MulAut.conj u).toMonoidHom := by
      rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
    rcases hrest with ⟨hnp,_⟩ | ⟨hnq,_⟩
    · exact Or.inl ⟨hnp,cube_paired_trapped_kernel_orbit s hc hb u hfull p hsmall hat hct
        x (Ltilde_le_stabilizer _ hx) q hq hqs hgen hpbad hqbad hstrict hnp⟩
    · have hgen' : Q d.radical t ⊔ Z d.radical (act d.radical x a') ⊔ Z d.radical a' =
          stabilizer d.radical (alpha d.radical) := by
        calc
          _ = Q d.radical t ⊔ Z d.radical a' ⊔ Z d.radical (act d.radical x a') := by ac_rfl
          _ = _ := hgen
      have hback := cube_paired_trapped_kernel_orbit s hc hb u hfull (b' := a') q hqs hat hct x⁻¹
        ((stabilizer d.radical (alpha d.radical)).inv_mem (Ltilde_le_stabilizer _ hx))
      have hqback (i : ℕ) : p.walk.getVert i = act d.radical x⁻¹ (q.walk.getVert i) := by
        rw [hq,←act_mul,mul_inv_cancel,act_one]
      refine Or.inr ⟨hnq,?_⟩
      simpa only [inv_inv] using hback p hqback hsmall hgen' hqbad hpbad hstrict hnq

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
