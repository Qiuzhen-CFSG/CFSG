module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsOppositeAction

/-!
# A source transposition lift fixing a core generator

Choose two labels at distance four from a labelled vertex along distinct
branches beyond a different neighbour. Their product fixes the chosen
unlabelled neighbour and exchanges its remaining branches. The six-arc
commutator formula gives its square as the adjacent central label. A nearer
label commutes with both factors and supplies a fixed core generator.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), the
six-arc relations and the extension calculation in (6.12), pp.405–406.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Theory.GroupAction.CubicTree Subgroup.CosetGeometry
open scoped commutatorElement
variable {G : Type*} [Group G] {F : Bool → Subgroup G} {s : ℕ}

private theorem exists_forward (h : CubicTreeAction F) (v a : RankTwo.Vertex F) :
    ∃ u, (RankTwo.graph F).Adj v u ∧ u ≠ a := by
  by_contra! hh
  have hi : Subsingleton ((RankTwo.graph F).neighborSet v) := ⟨fun x y =>
    Subtype.ext ((hh x x.property).trans (hh y y.property).symm)⟩
  have hc : Nat.card ((RankTwo.graph F).neighborSet v) ≤ 1 := by
    let f : (RankTwo.graph F).neighborSet v → Unit := fun _ => ()
    simpa using Nat.card_le_card_of_injective f (fun x y _ => Subsingleton.elim _ _)
  rw [h.card_neighbor v] at hc
  omega

private theorem nb_dist (h : CubicTreeAction F) {n : ℕ} {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n v) (hp : p.Nonbacktracking) :
    (RankTwo.graph F).dist v p.endpoint = n :=
  geodesic_of_nonbacktracking_of_cycle_bound h.tree.connected
    (N := 2*n) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp le_rfl

private theorem nb_path (h : CubicTreeAction F) {n : ℕ} {v : RankTwo.Vertex F}
    (p : BasedWalk (RankTwo.graph F) n v) (hp : p.Nonbacktracking) :
    p.toWalk.IsPath :=
  isPath_of_nonbacktracking_of_cycle_bound
    (N := n) (fun _ _ hc => (h.tree.isAcyclic _ hc).elim) p hp le_rfl

private theorem same_perm_three : ∀ (p q : Equiv.Perm (Fin 3)) (i j : Fin 3),
    i ≠ j → p i = i → q i = i → p j ≠ j → q j ≠ j → p = q := by
  decide +kernel

private theorem neighbor_side (d : CanonicalLabelSetup F s)
    {v a : RankTwo.Vertex F} (hv : v.type ≠ d.side)
    (ha : (RankTwo.graph F).Adj v a) : a.type = d.side := by
  have hn := ha.1
  cases h0 : v.type <;> cases h1 : a.type <;> cases h2 : d.side <;> simp_all

/-- The source transposition lift in an adjacent radius-four stabilizer
has square equal to the central label at that adjacent vertex. -/
theorem LocalRelations.exists_oppositeGenerator_lift_with_fixedLabel
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {v a : RankTwo.Vertex F} (ha : a.type = d.side)
    (hva : (RankTwo.graph F).Adj v a) :
    ∃ T ∈ oppositeGenerator d v a, T ^ 2 = d.label a ∧
      (∃ b, (RankTwo.graph F).Adj v b ∧ T • b ≠ b) ∧
      ∃ w, w.type = d.side ∧ (RankTwo.graph F).dist v w = 3 ∧
        (RankTwo.graph F).dist a w = 2 ∧ Commute T (d.label w) := by
  classical
  let t := h.action.toCubicTreeAction
  obtain ⟨β, haβ, hβv⟩ := exists_forward t a v
  obtain ⟨b, hvb, hba⟩ := exists_forward t v a
  have hβside : β.type ≠ d.side := by
    intro he
    exact haβ.1 (ha.trans he.symm)
  have hvside : v.type ≠ d.side := by
    intro he
    exact hva.1 (he.trans ha.symm)
  have hbside : b.type = d.side := neighbor_side d hvside hvb
  obtain ⟨f⟩ := t.exists_branchFrame β
  obtain ⟨i, hi⟩ := f.e.surjective ⟨a, haβ.symm⟩
  have hi' : (f.e i).val = a := congrArg Subtype.val hi
  obtain ⟨j, hji, _⟩ := Fin.exists_ne_and_ne_of_two_lt i i (by decide : 2 < 3)
  obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 3)
  choose w hw hne using fun l : Fin 3 => exists_forward t (f.c l) (f.e l).val
  have hadj (l : Fin 3) : (RankTwo.graph F).Adj β (f.e l).val := (f.e l).property
  have hbase (l : Fin 3) : (f.e l).val.type = d.side :=
    neighbor_side d hβside (f.e l).property
  have hnear (l : Fin 3) : (RankTwo.graph F).dist (f.e l).val (w l) = 2 :=
    (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr
      ⟨(hne l).symm, f.c l, f.c_adj l, hw l⟩
  have hwside (l : Fin 3) : (w l).type = d.side := by
    exact ((RankTwo.even_dist_iff F t.generated _ _).mp
      (by rw [hnear]; decide)).symm.trans (hbase l)
  have habase (l : Fin 3) (hli : l ≠ i) : (f.e l).val ≠ a := by
    intro he
    exact hli (f.e.injective (Subtype.ext (he.trans hi'.symm)))
  let p3 (l : Fin 3) : BasedWalk (RankTwo.graph F) 3 β :=
    ⟨⟨(f.e l).val, (f.e l).property⟩,
      ⟨⟨f.c l, f.c_adj l⟩, ⟨⟨w l, hw l⟩, PUnit.unit⟩⟩⟩
  have hp3 (l : Fin 3) : (p3 l).Nonbacktracking :=
    ⟨f.c_ne_center l, hne l, trivial⟩
  have hd3 (l : Fin 3) : (RankTwo.graph F).dist β (w l) = 3 := nb_dist t (p3 l) (hp3 l)
  let p4 (l : Fin 3) : BasedWalk (RankTwo.graph F) 4 a := ⟨⟨β, haβ⟩, p3 l⟩
  have hp4 (l : Fin 3) (hli : l ≠ i) : (p4 l).Nonbacktracking :=
    ⟨habase l hli, hp3 l⟩
  have hd4 (l : Fin 3) (hli : l ≠ i) : (RankTwo.graph F).dist a (w l) = 4 :=
    nb_dist t (p4 l) (hp4 l hli)
  let p5 (l : Fin 3) : BasedWalk (RankTwo.graph F) 5 v := ⟨⟨a, hva⟩, p4 l⟩
  have hp5 (l : Fin 3) (hli : l ≠ i) : (p5 l).Nonbacktracking :=
    ⟨hβv, hp4 l hli⟩
  have hd5 (l : Fin 3) (hli : l ≠ i) : (RankTwo.graph F).dist v (w l) = 5 :=
    nb_dist t (p5 l) (hp5 l hli)
  let p6 (l : Fin 3) : BasedWalk (RankTwo.graph F) 6 (w l) :=
    ⟨⟨f.c l, (hw l).symm⟩, ⟨⟨(f.e l).val, (f.c_adj l).symm⟩,
      ⟨⟨β, (hadj l).symm⟩, ⟨⟨a, haβ.symm⟩,
        ⟨⟨v, hva.symm⟩, ⟨⟨b, hvb⟩, PUnit.unit⟩⟩⟩⟩⟩⟩
  have hp6 (l : Fin 3) (hli : l ≠ i) : (p6 l).Nonbacktracking :=
    ⟨(hne l).symm, (f.c_ne_center l).symm, (habase l hli).symm,
      hβv.symm, hba, trivial⟩
  have hwb (l : Fin 3) (hli : l ≠ i) :
      ⁅d.label (w l), d.label b⁆ = d.label (f.e l).val * d.label a :=
    r.six_arc (w l) b (p6 l).toWalk (hwside l) (nb_path t (p6 l) (hp6 l hli)) rfl
  let pjk : BasedWalk (RankTwo.graph F) 6 (w j) :=
    ⟨⟨f.c j, (hw j).symm⟩, ⟨⟨(f.e j).val, (f.c_adj j).symm⟩,
      ⟨⟨β, (hadj j).symm⟩, ⟨⟨(f.e k).val, (f.e k).property⟩,
        ⟨⟨f.c k, f.c_adj k⟩, ⟨⟨w k, hw k⟩, PUnit.unit⟩⟩⟩⟩⟩⟩
  have hkj' : (f.e k).val ≠ (f.e j).val :=
    fun he => hkj (f.e.injective (Subtype.ext he))
  have hpjk : pjk.Nonbacktracking :=
    ⟨(hne j).symm, (f.c_ne_center j).symm, hkj', f.c_ne_center k, hne k, trivial⟩
  have hjk : ⁅d.label (w j), d.label (w k)⁆ =
      d.label (f.e j).val * d.label (f.e k).val :=
    r.six_arc (w j) (w k) pjk.toWalk (hwside j) (nb_path t pjk hpjk) rfl
  have hprod : d.label (f.e j).val * d.label (f.e k).val = d.label a := by
    have hh := d.neighbor_product β (f.e j).val (f.e k).val a
      (f.e j).property (f.e k).property haβ.symm hkj'.symm
      (habase j hji) (habase k hki) (hbase j)
    simpa only [d.label_inv ha] using mul_eq_one_iff_eq_inv.mp hh
  let T := d.label (w j) * d.label (w k)
  have hTsq : T ^ 2 = d.label a := by
    rw [← hprod, ← hjk]
    simp only [T, pow_two, commutatorElement_def, d.label_inv (hwside j),
      d.label_inv (hwside k), mul_assoc]
  have hfixa (l : Fin 3) (hli : l ≠ i) : d.label (w l) • a = a :=
    d.fixes_ball _ (hwside l) a (by rw [dist_comm, hd4 l hli, hr])
      (by rw [dist_comm, hd4 l hli]; have := h.five_le; omega)
  have hfixβ (l : Fin 3) : d.label (w l) • β = β :=
    d.fixes_ball _ (hwside l) β (by rw [dist_comm, hd3, hr]; omega)
      (by rw [dist_comm, hd3]; have := h.five_le; omega)
  have hmovev (l : Fin 3) (hli : l ≠ i) : d.label (w l) • v ≠ v :=
    d.moves_sphere _ (hwside l) (by have := h.five_le; omega) v
      (by rw [dist_comm, hd5 l hli, hr])
  obtain ⟨e⟩ := t.exists_branchFrame a
  obtain ⟨m, hm⟩ := e.e.surjective ⟨β, haβ⟩
  obtain ⟨n, hn⟩ := e.e.surjective ⟨v, hva.symm⟩
  have hm' : (e.e m).val = β := congrArg Subtype.val hm
  have hn' : (e.e n).val = v := congrArg Subtype.val hn
  have hmn : m ≠ n := fun he => hβv (hm'.symm.trans ((congrArg (fun l => (e.e l).val) he).trans hn'))
  let kj : RankTwo.stabilizer F a := ⟨d.label (w j), hfixa j hji⟩
  let kk : RankTwo.stabilizer F a := ⟨d.label (w k), hfixa k hki⟩
  have hactfix (l : Fin 3) (hli : l ≠ i) :
      e.branchAction ⟨d.label (w l), hfixa l hli⟩ m = m := by
    apply e.e.injective
    apply Subtype.ext
    rw [e.branchAction_eval, hm']
    exact hfixβ l
  have hactmove (l : Fin 3) (hli : l ≠ i) :
      e.branchAction ⟨d.label (w l), hfixa l hli⟩ n ≠ n := by
    intro he
    have hh := e.branchAction_eval ⟨d.label (w l), hfixa l hli⟩ n
    rw [he, hn'] at hh
    exact hmovev l hli hh.symm
  have heq : e.branchAction kj = e.branchAction kk :=
    same_perm_three _ _ m n hmn (hactfix j hji) (hactfix k hki)
      (hactmove j hji) (hactmove k hki)
  have heqv : d.label (w j) • v = d.label (w k) • v := by
    rw [← hn', ← e.branchAction_eval kj n, ← e.branchAction_eval kk n, heq]
  have hTv : T • v = v := by
    dsimp only [T]
    rw [mul_smul, ← heqv, ← mul_smul, d.label_mul_self (hwside j), one_smul]
  have hTmem : T ∈ oppositeGenerator d v a := by
    exact ⟨mul_mem (d.label_mem_labelBall (hwside j) (le_of_eq (hd4 j hji)))
      (d.label_mem_labelBall (hwside k) (le_of_eq (hd4 k hki))), hTv⟩
  have hcomm (u l : Fin 3) : Commute (d.label (w u)) (d.label (f.e l).val) := by
    have hd : (RankTwo.graph F).dist (w u) (f.e l).val ≤ 4 := by
      have hh := t.tree.connected.dist_triangle (u := w u) (v := β) (w := (f.e l).val)
      have he : (RankTwo.graph F).dist β (f.e l).val = 1 :=
        dist_eq_one_iff_adj.mpr (hadj l)
      rw [(show (RankTwo.graph F).dist (w u) β = (RankTwo.graph F).dist β (w u) from SimpleGraph.dist_comm), hd3, he] at hh
      omega
    exact d.labels_commute_of_dist_le (hwside u) (hbase l) (by omega)
      (by have := h.five_le; omega)
  have hcommA : Commute (d.label (w j)) (d.label a) :=
    d.labels_commute_of_fixed ha (hfixa j hji)
  have hCA : Commute (d.label (f.e j).val) (d.label a) := by
    have hd : (RankTwo.graph F).dist (f.e j).val a ≤ 2 := by
      have hh := t.tree.connected.dist_triangle (u := (f.e j).val) (v := β) (w := a)
      rw [dist_eq_one_iff_adj.mpr (hadj j).symm,
        dist_eq_one_iff_adj.mpr haβ.symm] at hh
      exact hh
    exact d.labels_commute_of_dist_le (hbase j) ha (by omega)
      (by have := h.five_le; omega)
  have hTb : ⁅T, d.label b⁆ = d.label a := by
    change ⁅d.label (w j) * d.label (w k), d.label b⁆ = d.label a
    rw [commutatorElement_mul_left_eq_conj_mul, hwb k hki, hwb j hji]
    rw [((hcomm j k).mul_right hcommA).eq, mul_inv_cancel_right]
    calc
      d.label (f.e k).val * d.label a * (d.label (f.e j).val * d.label a) =
          d.label (f.e k).val * d.label (f.e j).val := by
        calc
          _ = d.label (f.e k).val * (d.label a * d.label (f.e j).val) * d.label a := by group
          _ = d.label (f.e k).val * (d.label (f.e j).val * d.label a) * d.label a := by
            rw [← hCA.eq]
          _ = _ := by simp only [mul_assoc, d.label_mul_self ha, mul_one]
      _ = d.label a := by
        have hh := congrArg Inv.inv hprod
        simpa only [mul_inv_rev, d.label_inv (hbase j), d.label_inv (hbase k),
          d.label_inv ha] using hh
  have hmoveb : T • b ≠ b := by
    intro hfixb
    have hc : Commute T (d.label b) := ((d.central b hbside).2 T hfixb).symm
    have he : d.label a = 1 := hTb.symm.trans (commutatorElement_eq_one_iff_commute.mpr hc)
    have ho := d.order_two a ha
    rw [he, orderOf_one] at ho
    omega
  refine ⟨T, hTmem, hTsq, ⟨b, hvb, hmoveb⟩, (f.e j).val, hbase j, ?_, ?_, ?_⟩
  · let p : BasedWalk (RankTwo.graph F) 3 v :=
      ⟨⟨a, hva⟩, ⟨⟨β, haβ⟩, ⟨⟨(f.e j).val, (f.e j).property⟩, PUnit.unit⟩⟩⟩
    exact nb_dist t p ⟨hβv, habase j hji, trivial⟩
  · exact (DistanceTwoGeometry.dist_eq_two_iff t.tree).mpr
      ⟨(habase j hji).symm, β, haβ, (f.e j).property⟩
  · exact (hcomm j j).mul_left (hcomm k j)

/-- Forgetting the fixed core generator retains the literal source lift. -/
theorem LocalRelations.exists_oppositeGenerator_lift
    {h : LargeTreeSource F s} {d : CanonicalLabelSetup F s}
    (r : LocalRelations h d) (hr : d.radius = 3)
    {v a : RankTwo.Vertex F} (ha : a.type = d.side)
    (hva : (RankTwo.graph F).Adj v a) :
    ∃ T ∈ oppositeGenerator d v a, T ^ 2 = d.label a ∧
      ∃ b, (RankTwo.graph F).Adj v b ∧ T • b ≠ b := by
  obtain ⟨T, hT, hs, hm, _⟩ := r.exists_oppositeGenerator_lift_with_fixedLabel hr ha hva
  exact ⟨T, hT, hs, hm⟩

end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
