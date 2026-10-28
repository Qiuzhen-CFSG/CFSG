module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalFixedBudget
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootSpanNatural
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# Both root-span budgets on the same actual unequal selector

The original unequal edge supplies an actual residual selector and a second
critical path. Full source-kernel normalization excludes the trapped branch.
The unequal seed-budget theorem applies first to the given path pair, then
to the selected pair. Conjugation by that very selector transports the mover
inequality needed for the second application.

Thus both numerical premises of the root-span offender are produced on
one critical path whose endpoints lie in the orbit of its midpoint
stabilizer. The original backward path, individual generation, selector,
and every overlap are retained. No arbitrary endpoint orbit is assumed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem actual_mover_conjugate {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (a t : Vertex R) :
    Subgroup.SmallMover.join (U R (act R y a)) (Q R (act R y a))
        (Q R (act R y t)) q =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) q).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual unequal edge produces a second critical path with both
root-span budgets, the same midpoint orbit and all literal overlaps. -/
theorem Input.replacement_distance_four_unequal_root_span_data
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2)) :
    ∃ g ∈ Ltilde d.radical u,
      let v := act d.radical g⁻¹ a
      let s := act d.radical g⁻¹ (back.walk.getVert 1)
      Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
      Ltilde d.radical u ≤
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2) ∧
      ∃ next : CriticalPath d.radical geometry v a,
        next.walk.getVert 1=s ∧ next.walk.getVert 2=u ∧
        (∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i) ∧
        (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical u) ≤ Nat.card F ∧
        (B d.radical u (geometry.Z_normal u)).relIndex (U d.radical a) ≤ Nat.card F := by
  let e := path.walk.getVert 2
  let t := back.walk.getVert 1
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb2 : 2 < geometry.b d.radical := by omega
  have hbl : back.walk.length=4 := back.length_eq_b.trans hb
  have hut : Adjacent d.radical u t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0<back.walk.length))
  have hat : Adjacent d.radical a t := by
    rw [←hmid]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 1<back.walk.length)))
  have hpen : back.walk.getVert (back.walk.length-2)=a := by rw [hbl]; exact hmid
  have hroot := (h.replacement_distance_four_fixed_critical_indices d hb
    path.start_color hfixed back).2
  have hsmall : (Q d.radical u).relIndex (Z d.radical e)<Nat.card F^2 := by
    rw [hroot]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hnormal : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) back.start_color hut hat).trans
      (h.replacement_root_neighbor_seed_index_le_cube d back hb4 hut hat hsmall)
    have hq : 1<Nat.card F := Finite.one_lt_card
    have hYB := h.replacement_small_radius_le_B d geometry hb2 back.start_color
      (Z d.radical a ⊔ Z d.radical u) (neighbor_seed_join_le_radius hut hat)
      ((Ltilde_le_stabilizer u).trans hn)
      (hidx.trans_lt (Nat.pow_lt_pow_right hq (by decide : 3<4)))
    have hone := relIndex_eq_one.mpr (((U_le_Z a).trans le_sup_left).trans hYB)
    have hmove := h.replacement_path_moving_index_ge_field d back hb4
    rw [hmid,hone] at hmove
    exact hq.not_ge hmove
  obtain ⟨g,hg,hus,hvs,hindex,hJmap,hgen,hres,hfixedJ,hfixedJa,hquadJa,hquadEc,
    hEcindex,hQnot,hEcimage,hn,hcases⟩ :=
    h.replacement_unequal_individual_generation_root_at_neighbor d back hb4 hut rfl hat
      hnormal hsmall hne
  let v := act d.radical g⁻¹ a
  let s := act d.radical g⁻¹ t
  have hy : g⁻¹ ∈ stabilizer d.radical u :=
    (stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg)
  have hgu : act d.radical g⁻¹ u=u := hy
  have nextData : ∃ next : CriticalPath d.radical geometry v a,
      next.walk.getVert 1=s ∧
      ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i := by
    rcases hcases with ⟨next,hfirst,hover⟩ | ⟨htrap,_⟩
    · let next' : CriticalPath d.radical geometry v a := {
        start_color := next.start_color
        walk := next.walk.copy rfl hpen
        shortest := by simpa only [SimpleGraph.Walk.length_copy,hpen] using next.shortest
        critical := by simpa only [hpen] using next.critical }
      refine ⟨next',?_,?_⟩
      · simpa only [next',SimpleGraph.Walk.getVert_copy] using hfirst
      · simpa only [next',SimpleGraph.Walk.getVert_copy] using hover
    · have hnfull := h.replacement_distance_four_full_fixed_kernel_normalized d path hb back
        hmid hus hvs g⁻¹ hy rfl hfixed
      rw [hpen] at htrap
      rw [inf_eq_left.mpr htrap] at hnfull
      exact (hn hnfull).elim
  obtain ⟨next,hfirst,hover⟩ := nextData
  have hnextmid : next.walk.getVert 2=u := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hne' : Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical s) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) := by
    intro heq
    have heq' : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom =
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2)).map (MulAut.conj g).toMonoidHom := by
      have hmu := actual_mover_conjugate (Nat.card F^2) g⁻¹ u t
      have hma := actual_mover_conjugate (Nat.card F^2) g⁻¹ a t
      simp only [inv_inv,hgu] at hmu
      simp only [inv_inv] at hma
      exact hmu.symm.trans (heq.trans hma)
    exact hne (map_injective (MulAut.conj g).injective heq').symm
  let next' : CriticalPath d.radical geometry v (back.walk.getVert 2) := {
    start_color := next.start_color
    walk := next.walk.copy rfl hmid.symm
    shortest := by simpa only [SimpleGraph.Walk.length_copy,hmid] using next.shortest
    critical := by simpa only [hmid] using next.critical }
  have hmid' : next'.walk.getVert 2=u := by
    simpa only [next',SimpleGraph.Walk.getVert_copy] using hnextmid
  have hfirst' : next'.walk.getVert 1=s := by
    simpa only [next',SimpleGraph.Walk.getVert_copy] using hfirst
  have hfixed_u := radius_fixed_at d path.start_color back.start_color hfixed
  have hbudget := h.replacement_distance_four_unequal_fixed_seed_budget d back hb next'
    hmid' hfixed_u (by simpa only [hfirst'] using hne')
  exact ⟨g,hg,hus,hvs,hres,next,hfirst,hnextmid,hover,hbudget,
    h.replacement_distance_four_unequal_fixed_seed_budget d path hb back hmid hfixed hne⟩

/-- The unequal branch constructs the actual root-offender natural moved
section with both budgets and its midpoint orbit discharged internally. -/
theorem Input.replacement_distance_four_unequal_root_span_natural
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2)) :
    ∃ g ∈ Ltilde d.radical u,
      let v := act d.radical g⁻¹ a
      let s := act d.radical g⁻¹ (back.walk.getVert 1)
      Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
      Ltilde d.radical u ≤
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2) ∧
      ∃ next : CriticalPath d.radical geometry v a,
        next.walk.getVert 1=s ∧ next.walk.getVert 2=u ∧
        (∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i) ∧
        distanceFourRootSpanNatural geometry v u a n := by
  obtain ⟨g,hg,hus,hvs,hres,next,hfirst,hnextmid,hover,hbudget,hlast⟩ :=
    h.replacement_distance_four_unequal_root_span_data d path hb back hmid hfixed hne
  have hgv : act d.radical g (act d.radical g⁻¹ a)=a := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hfixed_v := radius_fixed_at d path.start_color next.start_color hfixed
  have hnat := h.replacement_distance_four_root_span_natural d next hb g
    (by rw [hnextmid]; exact Ltilde_le_stabilizer u hg) hgv hfixed_v
    (by simpa only [hnextmid] using hbudget) (by simpa only [hnextmid] using hlast)
  rw [hnextmid] at hnat
  exact ⟨g,hg,hus,hvs,hres,next,hfirst,hnextmid,hover,hnat⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
