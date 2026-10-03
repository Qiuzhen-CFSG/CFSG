module

public import Stellmacher.SectionFiveToSeven.Result7_3

/-!
# Stellmacher's Lemma 7.4

This module proves the critical-path containment and quadratic-action facts
used throughout the remainder of the coset-graph argument.  Minimality of the
critical distance puts every `Z_d` arising at a shorter distance inside the
corresponding `Q`; applying this observation to prefixes and suffixes of the
chosen path gives the two containment statements.

Lemma 7.3 at the first edge then gives `C_S(Z_a) = Q_a`: its other alternative
would put `Z_a` inside `Z_{a+1}` and contradict criticality.  At the final edge,
the same alternative is ruled out by a nontrivial endpoint commutator.  Sylow
conjugacy inside the endpoint stabilizer transports the resulting centralizer
equality from the edge Sylow subgroup to every Sylow subgroup.  Finally, each
`Z_d` is abelian and invariant under its vertex stabilizer; mutual containment
in the endpoint stabilizers therefore makes the two endpoint actions
quadratic.

Source: `refs/latex/stellmacher-n-group.tex`, Lemma (7.4), corresponding to
Journal of Algebra 190 (1997), p. 34.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven

open CosetGraphContext

universe u v

public structure LemmaSevenFourConclusion
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) : Prop where
  first_containment : z Gamma cp.a ≤ v Gamma cp.firstStep ∧
    v Gamma cp.firstStep ≤ stabilizer Gamma cp.a'
  reverse_containment : z Gamma cp.a' ≤ stabilizer Gamma cp.a ∧
    v Gamma cp.a' ≤ stabilizer Gamma cp.firstStep
  edge_centralizer :
    S ⊓ Subgroup.centralizer (z Gamma cp.a : Set G) = q Gamma cp.a
  commutator_case :
    ⁅z Gamma cp.a, z Gamma cp.a'⁆ ≠ ⊥ →
      (∀ T : Sylow 2 ↥(stabilizer Gamma cp.a'),
        sylowTwoAmbient (stabilizer Gamma cp.a') T ⊓
            Subgroup.centralizer (z Gamma cp.a' : Set G) = q Gamma cp.a') ∧
      IsCriticalPair Gamma cp.a' cp.a
  quadratic :
    IsQuadraticOn (z Gamma cp.a) (z Gamma cp.a') ∧
      IsQuadraticOn (z Gamma cp.a') (z Gamma cp.a)

variable {G : Type u} [Group G] [Finite G]
  {S P1 P2 : Subgroup G}

private theorem adjacent_irrefl
    (Gamma : CosetGraphContext G S P1 P2) (d : Gamma.Vertex) :
    ¬ Gamma.adjacent d d := by
  rcases Gamma.coset₁_surjective d with ⟨g, hg | hg⟩
  · rw [hg]
    exact Gamma.no_adj_coset₁_coset₁ g g
  · rw [hg]
    exact Gamma.no_adj_coset₂_coset₂ g g

private theorem adjacent_iff_distance_eq_one
    (Gamma : CosetGraphContext G S P1 P2) {d l : Gamma.Vertex} :
    Gamma.adjacent d l ↔ Gamma.distance d l = 1 := by
  constructor
  · intro hdl
    let f : Fin 2 → Gamma.Vertex := ![d, l]
    have hpath : ∀ i : Fin 1,
        Gamma.adjacent (f i.castSucc) (f i.succ) := by
      intro i
      fin_cases i
      exact hdl
    have hle : Gamma.distance d l ≤ 1 := by
      simpa [f] using Gamma.distance_le_of_path 1 f hpath
    have hne : Gamma.distance d l ≠ 0 := by
      intro hzero
      have hEq := (Gamma.distance_zero_iff d l).mp hzero
      exact adjacent_irrefl Gamma d (hEq ▸ hdl)
    omega
  · intro hdist
    rcases Gamma.distance_path d l with ⟨f, hstart, hend, hpath⟩
    have hpos : 0 < Gamma.distance d l := hdist ▸ Nat.zero_lt_one
    have hedge := hpath ⟨0, hpos⟩
    have hi : (⟨0, hpos⟩ : Fin (Gamma.distance d l)).succ =
        ⟨Gamma.distance d l, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp [hdist]
    rw [hi, hend] at hedge
    simpa [hstart] using hedge

private theorem mem_neighborhood_iff_adjacent
    (Gamma : CosetGraphContext G S P1 P2) {d l : Gamma.Vertex} :
    l ∈ neighborhood Gamma d ↔ Gamma.adjacent d l := by
  rw [neighborhood, Gamma.neighbors_def]
  change Gamma.distance l d = 1 ↔ Gamma.adjacent d l
  rw [Gamma.distance_symm]
  exact (adjacent_iff_distance_eq_one Gamma).symm

private theorem path_distance_le
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (i j : ℕ) (hi : i ≤ j) (hj : j ≤ cp.length) :
    Gamma.distance
        (cp.path ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩)
        (cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩) ≤ j - i := by
  let f : Fin (j - i + 1) → Gamma.Vertex := fun k ↦
    cp.path ⟨i + k, by omega⟩
  have hf0 : f 0 = cp.path
      ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩ := by
    rfl
  have hfend : f ⟨j - i, Nat.lt_succ_self _⟩ =
      cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩ := by
    apply congrArg cp.path
    apply Fin.ext
    dsimp [f]
    omega
  have hadj : ∀ k : Fin (j - i),
      Gamma.adjacent (f k.castSucc) (f k.succ) := by
    intro k
    convert cp.path_adj ⟨i + k, by omega⟩ using 1 <;> congr 1
  simpa [hf0, hfend] using Gamma.distance_le_of_path (j - i) f hadj

private theorem neighbor_path_distance_le
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (l : Gamma.Vertex) (i j : ℕ) (hi : i ≤ j) (hj : j ≤ cp.length)
    (hli : Gamma.adjacent l
      (cp.path ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩)) :
    Gamma.distance l
        (cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩) ≤ j - i + 1 := by
  let f : Fin ((j - i + 1) + 1) → Gamma.Vertex :=
    Fin.cases l (fun k ↦ cp.path ⟨i + k, by omega⟩)
  have hf0 : f 0 = l := by simp [f]
  have hfend : f ⟨j - i + 1, Nat.lt_succ_self _⟩ =
      cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩ := by
    apply congrArg cp.path
    apply Fin.ext
    simp
    omega
  have hadj : ∀ k : Fin (j - i + 1),
      Gamma.adjacent (f k.castSucc) (f k.succ) := by
    intro k
    refine Fin.cases ?_ (fun m ↦ ?_) k
    · convert hli using 1 <;> congr 1
    · convert cp.path_adj ⟨i + m, by omega⟩ using 1 <;> congr 1
  simpa [hf0, hfend] using
    Gamma.distance_le_of_path (j - i + 1) f hadj

private theorem neighbor_reverse_path_distance_le
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (l : Gamma.Vertex) (i j : ℕ) (hi : i ≤ j) (hj : j ≤ cp.length)
    (hlj : Gamma.adjacent l
      (cp.path ⟨j, hj.trans_lt (Nat.lt_succ_self _)⟩)) :
    Gamma.distance l
        (cp.path ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩) ≤
      j - i + 1 := by
  let f : Fin ((j - i + 1) + 1) → Gamma.Vertex :=
    Fin.cases l (fun k ↦ cp.path ⟨j - k, by omega⟩)
  have hf0 : f 0 = l := by simp [f]
  have hfend : f ⟨j - i + 1, Nat.lt_succ_self _⟩ =
      cp.path
        ⟨i, lt_of_le_of_lt hi (hj.trans_lt (Nat.lt_succ_self _))⟩ := by
    apply congrArg cp.path
    apply Fin.ext
    simp
    omega
  have hadj : ∀ k : Fin (j - i + 1),
      Gamma.adjacent (f k.castSucc) (f k.succ) := by
    intro k
    refine Fin.cases ?_ (fun m ↦ ?_) k
    · convert hlj using 1 <;> congr 1
    · dsimp [f]
      change Gamma.adjacent
        (cp.path ⟨j - m, by omega⟩)
        (cp.path ⟨j - (m + 1), by omega⟩)
      let k : Fin cp.length := ⟨j - (m + 1), by omega⟩
      have hkSucc : k.succ =
          ⟨j - m, by omega⟩ := by
        apply Fin.ext
        simp [k]
        omega
      have hp := cp.path_adj k
      rw [hkSucc] at hp
      exact Gamma.adjacent_symm hp
  simpa [hf0, hfend] using
    Gamma.distance_le_of_path (j - i + 1) f hadj

private theorem last_edge_adjacent
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    Gamma.adjacent
      (cp.path ⟨cp.length - 1, by omega⟩) cp.a' := by
  have hlenpos := cp.length_pos
  let k : Fin cp.length := ⟨cp.length - 1, by omega⟩
  have hkSucc : k.succ =
      ⟨cp.length, Nat.lt_succ_self _⟩ := by
    apply Fin.ext
    simp [k]
    omega
  have hp := cp.path_adj k
  rw [hkSucc, cp.path_end] at hp
  simpa [k] using hp

private theorem critical_minimality
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    {d l : Gamma.Vertex} (hdist : Gamma.distance d l < cp.length) :
    z Gamma d ≤ q Gamma l := by
  by_contra hnot
  have hmem : Gamma.distance d l ∈
      {n : ℕ | ∃ x y : Gamma.Vertex,
        Gamma.distance x y = n ∧ ¬ Gamma.zAt x ≤ Gamma.twoCoreAt y} :=
    ⟨d, l, rfl, by simpa [z, q] using hnot⟩
  have hle : cp.length ≤ Gamma.distance d l := by
    calc
      cp.length = sInf {n : ℕ | ∃ x y : Gamma.Vertex,
          Gamma.distance x y = n ∧ ¬ Gamma.zAt x ≤ Gamma.twoCoreAt y} := by
        rw [← cp.endpoint_distance]
        exact cp.critical.1
      _ ≤ Gamma.distance d l := Nat.sInf_le hmem
  omega

omit [Finite G] in
private theorem omegaOneCenter_le_self (A : Subgroup G) :
    omegaOneCenter A ≤ A := by
  unfold omegaOneCenter
  exact (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans
    (Subgroup.map_subtype_le _)

private theorem z_le_q_of_neighbor
    {Gamma : CosetGraphContext G S P1 P2}
    (h73 : LemmaSevenThreeConclusion Gamma)
    {d l : Gamma.Vertex} (hl : l ∈ neighborhood Gamma d) :
    z Gamma d ≤ q Gamma d :=
  (h73.center_core d l hl).trans (omegaOneCenter_le_self _)

private theorem q_le_stabilizer_of_neighbor
    {Gamma : CosetGraphContext G S P1 P2}
    (h73 : LemmaSevenThreeConclusion Gamma)
    {d l : Gamma.Vertex} (hl : l ∈ neighborhood Gamma d) :
    q Gamma d ≤ stabilizer Gamma l := by
  let T : Sylow 2 ↥(stabilizer Gamma d ⊓ stabilizer Gamma l) := default
  exact (h73.sylow_and_core d l hl T).2.2

private theorem v_le_own_stabilizer
    {Gamma : CosetGraphContext G S P1 P2}
    (h73 : LemmaSevenThreeConclusion Gamma) (d : Gamma.Vertex) :
    v Gamma d ≤ stabilizer Gamma d := by
  rw [v, Gamma.vAt_def]
  refine sSup_le fun Z hZ ↦ ?_
  rcases hZ with ⟨l, hl, rfl⟩
  have hdl : d ∈ neighborhood Gamma l :=
    (mem_neighborhood_iff_adjacent Gamma).2
      (Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).1 hl))
  exact (z_le_q_of_neighbor h73 hdl).trans
    (q_le_stabilizer_of_neighbor h73 hdl)

private theorem first_and_reverse_containment
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    (z Gamma cp.a ≤ v Gamma cp.firstStep ∧
      v Gamma cp.firstStep ≤ stabilizer Gamma cp.a') ∧
    (z Gamma cp.a' ≤ stabilizer Gamma cp.a ∧
      v Gamma cp.a' ≤ stabilizer Gamma cp.firstStep) := by
  let h73 := lemma_seven_three h Gamma
  have hafirst_mem : cp.a ∈ neighborhood Gamma cp.firstStep :=
    (mem_neighborhood_iff_adjacent Gamma).2
      (Gamma.adjacent_symm cp.firstStep_adj)
  have hfirsta_mem : cp.firstStep ∈ neighborhood Gamma cp.a :=
    (mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj
  have hza_v : z Gamma cp.a ≤ v Gamma cp.firstStep := by
    rw [v, Gamma.vAt_def]
    exact le_sSup ⟨cp.a, hafirst_mem, rfl⟩
  have hfirst_end_dist : Gamma.distance cp.firstStep cp.a' ≤
      cp.length - 1 := by
    have hp := path_distance_le Gamma cp 1 cp.length
      (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt cp.length_pos)) le_rfl
    simpa [cp.path_first, cp.path_end] using hp
  have hzend_qfirst : z Gamma cp.a' ≤ q Gamma cp.firstStep := by
    apply critical_minimality Gamma cp
    rw [Gamma.distance_symm]
    exact lt_of_le_of_lt hfirst_end_dist (Nat.sub_lt cp.length_pos Nat.zero_lt_one)
  have hzend_staba : z Gamma cp.a' ≤ stabilizer Gamma cp.a :=
    hzend_qfirst.trans (q_le_stabilizer_of_neighbor h73
      ((mem_neighborhood_iff_adjacent Gamma).2
        (Gamma.adjacent_symm cp.firstStep_adj)))
  by_cases hb : cp.length = 1
  · have hfirst_eq_end : cp.firstStep = cp.a' := by
      calc
        cp.firstStep = cp.path ⟨1, by omega⟩ := cp.path_first.symm
        _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
          congr 1
          apply Fin.ext
          simp [hb]
        _ = cp.a' := cp.path_end
    exact ⟨⟨hza_v, by simpa [hfirst_eq_end] using
        v_le_own_stabilizer h73 cp.firstStep⟩,
      ⟨hzend_staba, by simpa [hfirst_eq_end] using
        v_le_own_stabilizer h73 cp.firstStep⟩⟩
  · have hlenpos := cp.length_pos
    have hlenne := hb
    have hb2 : 2 ≤ cp.length := by omega
    let penult : Gamma.Vertex :=
      cp.path ⟨cp.length - 1, by omega⟩
    have hpenult_end_adj : Gamma.adjacent penult cp.a' := by
      simpa [penult] using last_edge_adjacent Gamma cp
    have hpenult_end_mem : cp.a' ∈ neighborhood Gamma penult :=
      (mem_neighborhood_iff_adjacent Gamma).2 hpenult_end_adj
    have hvfirst_end : v Gamma cp.firstStep ≤ stabilizer Gamma cp.a' := by
      rw [v, Gamma.vAt_def]
      refine sSup_le fun Z hZ ↦ ?_
      rcases hZ with ⟨l, hl, rfl⟩
      have hlfirst : Gamma.adjacent l cp.firstStep :=
        Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).1 hl)
      have hdist : Gamma.distance l penult ≤ cp.length - 1 := by
        have hp := neighbor_path_distance_le Gamma cp l 1
          (cp.length - 1) (by omega) (by omega) (by
            simpa [cp.path_first] using hlfirst)
        change Gamma.distance l penult ≤ cp.length - 1 - 1 + 1 at hp
        exact hp.trans (by omega)
      have hzlq : z Gamma l ≤ q Gamma penult := by
        apply critical_minimality Gamma cp
        exact lt_of_le_of_lt hdist (Nat.sub_lt cp.length_pos Nat.zero_lt_one)
      exact hzlq.trans (q_le_stabilizer_of_neighbor h73 hpenult_end_mem)
    let second : Gamma.Vertex := cp.path ⟨2, by omega⟩
    have hfirst_second_adj : Gamma.adjacent cp.firstStep second := by
      have hp := cp.path_adj ⟨1, by omega⟩
      simpa [second, cp.path_first] using hp
    have hsecond_first_mem : cp.firstStep ∈ neighborhood Gamma second :=
      (mem_neighborhood_iff_adjacent Gamma).2
        (Gamma.adjacent_symm hfirst_second_adj)
    have hvend_first : v Gamma cp.a' ≤ stabilizer Gamma cp.firstStep := by
      rw [v, Gamma.vAt_def]
      refine sSup_le fun Z hZ ↦ ?_
      rcases hZ with ⟨l, hl, rfl⟩
      have hlend : Gamma.adjacent l cp.a' :=
        Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).1 hl)
      have hdist : Gamma.distance l second ≤ cp.length - 1 := by
        have hp := neighbor_reverse_path_distance_le Gamma cp l 2 cp.length
          hb2 le_rfl (by simpa [cp.path_end] using hlend)
        change Gamma.distance l second ≤ cp.length - 2 + 1 at hp
        exact hp.trans (by omega)
      have hzlq : z Gamma l ≤ q Gamma second := by
        apply critical_minimality Gamma cp
        exact lt_of_le_of_lt hdist (Nat.sub_lt cp.length_pos Nat.zero_lt_one)
      exact hzlq.trans (q_le_stabilizer_of_neighbor h73 hsecond_first_mem)
    exact ⟨⟨hza_v, hvfirst_end⟩, ⟨hzend_staba, hvend_first⟩⟩

private theorem isSylowTwoIn_inf_right
    {S P K : Subgroup G}
    (hSP : IsSylowTwoIn S P) (hSK : S ≤ K) :
    IsSylowTwoIn S (P ⊓ K) := by
  classical
  obtain ⟨hSleP, T, hTmap⟩ := hSP
  let I : Subgroup G := P ⊓ K
  let J : Subgroup P := I.subgroupOf P
  have hTJ : (T : Subgroup P) ≤ J := by
    intro t ht
    have htS : (t : G) ∈ S := by
      rw [← hTmap]
      exact Subgroup.mem_map_of_mem P.subtype ht
    exact ⟨hSleP htS, hSK htS⟩
  let TJ : Sylow 2 J := T.subtype hTJ
  let eJI : J ≃* I :=
    { toFun := fun x ↦ ⟨(x : G), x.property⟩
      invFun := fun x ↦ ⟨⟨(x : G), x.property.1⟩, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  let TI : Sylow 2 I :=
    TJ.mapSurjective (f := eJI.toMonoidHom) eJI.surjective
  refine ⟨le_inf hSleP hSK, TI, ?_⟩
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, rfl⟩ := hx
    change i ∈ (TJ : Subgroup J).map eJI.toMonoidHom at hi
    obtain ⟨j, hj, hji⟩ := hi
    have hjT : (j : P) ∈ T := hj
    rw [← hTmap]
    have : (i : G) = (j : G) := congrArg Subtype.val hji.symm
    exact ⟨(j : P), hjT, this.symm⟩
  · intro hx
    rw [← hTmap] at hx
    obtain ⟨t, ht, htx⟩ := hx
    have htS : (t : G) ∈ S := by
      rw [← hTmap]
      exact Subgroup.mem_map_of_mem P.subtype ht
    let j : J := ⟨t, hTJ ht⟩
    let i : I := eJI j
    refine ⟨i, ?_, ?_⟩
    · change i ∈ (TJ : Subgroup J).map eJI.toMonoidHom
      exact Subgroup.mem_map_of_mem eJI.toMonoidHom ht
    · exact htx

private theorem edge_sylow_data
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    IsSylowTwoIn S (stabilizer Gamma cp.a) ∧
      IsSylowTwoIn S (stabilizer Gamma cp.firstStep) := by
  rcases cp.edge_stabilizers_are_P with hedge | hedge
  · rw [hedge.1, hedge.2]
    exact ⟨h.P1_mem.1.2.1, h.P2_mem.1.2.1⟩
  · rw [hedge.1, hedge.2]
    exact ⟨h.P2_mem.1.2.1, h.P1_mem.1.2.1⟩

private theorem omegaOneCenter_edge_le_z
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    omegaOneCenter S ≤ z Gamma cp.firstStep := by
  obtain ⟨_, T, hTmap⟩ := (edge_sylow_data h Gamma cp).2
  rw [z, Gamma.zAt_def]
  apply le_sSup
  change sylowTwoAmbient (stabilizer Gamma cp.firstStep) T = S at hTmap
  exact ⟨T, congrArg omegaOneCenter hTmap.symm⟩

private theorem edge_centralizer
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    S ⊓ Subgroup.centralizer (z Gamma cp.a : Set G) = q Gamma cp.a := by
  let h73 := lemma_seven_three h Gamma
  have hfirst_mem : cp.firstStep ∈ neighborhood Gamma cp.a :=
    (mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj
  have hSedge : IsSylowTwoIn S
      (stabilizer Gamma cp.a ⊓ stabilizer Gamma cp.firstStep) :=
    isSylowTwoIn_inf_right (edge_sylow_data h Gamma cp).1
      (cp.S_le_edge_stabilizers.trans inf_le_right)
  obtain ⟨_, T, hTmap⟩ := hSedge
  have halt := h73.centralizer_alternative cp.a cp.firstStep hfirst_mem T
  change sylowTwoAmbient
    (stabilizer Gamma cp.a ⊓ stabilizer Gamma cp.firstStep) T = S at hTmap
  rw [hTmap] at halt
  rcases halt with heq | heq
  · exact heq
  · exfalso
    have hza_zfirst : z Gamma cp.a ≤ z Gamma cp.firstStep := by
      rw [heq.2]
      exact omegaOneCenter_edge_le_z h Gamma cp
    have hdist : Gamma.distance cp.firstStep cp.a' < cp.length := by
      have hp := path_distance_le Gamma cp 1 cp.length
        (Nat.one_le_iff_ne_zero.2 (Nat.ne_of_gt cp.length_pos)) le_rfl
      have hp' : Gamma.distance cp.firstStep cp.a' ≤ cp.length - 1 := by
        simpa [cp.path_first, cp.path_end] using hp
      exact lt_of_le_of_lt hp' (Nat.sub_lt cp.length_pos Nat.zero_lt_one)
    exact cp.critical.2
      (hza_zfirst.trans (critical_minimality Gamma cp hdist))

private theorem omega₁_map_equiv
    {A B : Type u} [Group A] [Group B] (f : A ≃* B) :
    (omega₁ (G := A) (p := 2)).map f.toMonoidHom =
      omega₁ (G := B) (p := 2) := by
  let X : Set A := {x | x ^ (2 ^ 1) = 1}
  let Y : Set B := {y | y ^ (2 ^ 1) = 1}
  have hXY : f '' X = Y := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' : x ^ (2 ^ 1) = 1 := hx
      simpa [Y] using congrArg f.toMonoidHom hx'
    · intro hy
      refine ⟨f.symm y, ?_, by simp⟩
      have hy' : y ^ (2 ^ 1) = 1 := hy
      simpa [X] using congrArg f.symm.toMonoidHom hy'
  change (Subgroup.closure X).map f.toMonoidHom = Subgroup.closure Y
  rw [MonoidHom.map_closure]
  exact congrArg Subgroup.closure hXY

omit [Finite G] in
private theorem omegaOneCenter_map_equiv
    {G' : Type u} [Group G'] (f : G ≃* G') (A : Subgroup G) :
    omegaOneCenter (A.map f.toMonoidHom) =
      (omegaOneCenter A).map f.toMonoidHom := by
  let fA : A ≃* A.map f.toMonoidHom :=
    A.equivMapOfInjective f.toMonoidHom f.injective
  let fZ : Subgroup.center A ≃* Subgroup.center (A.map f.toMonoidHom) :=
    Subgroup.centerCongr fA
  have hOmega := omega₁_map_equiv fZ
  symm
  unfold omegaOneCenter
  rw [← hOmega]
  simp only [Subgroup.map_map]
  apply congrArg (fun g : Subgroup.center A →* G' ↦
    (omega₁ (G := Subgroup.center A) (p := 2)).map g)
  ext x
  rfl

private noncomputable def sylowOmegaJoin (P : Subgroup G) : Subgroup G :=
  sSup {Z : Subgroup G | ∃ T : Sylow 2 P,
    Z = omegaOneCenter ((T : Subgroup P).map P.subtype)}

omit [Finite G] in
private theorem sylowAmbient_smul (P : Subgroup G)
    (T : Sylow 2 P) (g : P) :
    (((g • T : Sylow 2 P) : Subgroup P).map P.subtype) =
      (((T : Subgroup P).map P.subtype).map
        (MulAut.conj (g : G)).toMonoidHom) := by
  change (((T : Subgroup P).map
      (MulAut.conj g).toMonoidHom).map P.subtype) = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
private theorem sylowOmegaJoin_map_conj (P : Subgroup G) (g : P) :
    (sylowOmegaJoin P).map (MulAut.conj (g : G)).toMonoidHom =
      sylowOmegaJoin P := by
  apply le_antisymm
  · unfold sylowOmegaJoin
    rw [sSup_eq_iSup, Subgroup.map_iSup]
    refine iSup_le fun W ↦ ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T, rfl⟩
    rw [← omegaOneCenter_map_equiv, ← sylowAmbient_smul]
    refine le_iSup_of_le
      (omegaOneCenter ((((g • T : Sylow 2 P) : Subgroup P).map P.subtype))) ?_
    exact le_iSup_of_le ⟨g • T, rfl⟩ le_rfl
  · unfold sylowOmegaJoin
    rw [sSup_eq_iSup]
    refine iSup_le fun W ↦ ?_
    refine iSup_le fun hW ↦ ?_
    rcases hW with ⟨T, rfl⟩
    have hgen :
        omegaOneCenter
            ((((g⁻¹ • T : Sylow 2 P) : Subgroup P).map P.subtype)) ≤
          sylowOmegaJoin P := le_sSup ⟨g⁻¹ • T, rfl⟩
    have hmap := Subgroup.map_mono
      (f := (MulAut.conj (g : G)).toMonoidHom) hgen
    rw [← omegaOneCenter_map_equiv, ← sylowAmbient_smul] at hmap
    simpa [sylowOmegaJoin, sSup_eq_iSup] using hmap

private theorem stabilizer_le_normalizer_z
    (Gamma : CosetGraphContext G S P1 P2) (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (z Gamma d : Set G) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  rw [z, Gamma.zAt_def]
  exact sylowOmegaJoin_map_conj (stabilizer Gamma d) ⟨g, hg⟩

public theorem stabilizer_le_normalizer_z_public
    (Gamma : CosetGraphContext G S P1 P2) (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (z Gamma d : Set G) :=
  stabilizer_le_normalizer_z Gamma d

private theorem stabilizer_le_normalizer_q
    (Gamma : CosetGraphContext G S P1 P2) (d : Gamma.Vertex) :
    stabilizer Gamma d ≤ Subgroup.normalizer (q Gamma d : Set G) := by
  rw [q, Gamma.twoCoreAt_def]
  apply (Subgroup.normal_subgroupOf_iff_le_normalizer
    (Subgroup.map_subtype_le (pCore 2 (stabilizer Gamma d)))).mp
  rw [← Subgroup.comap_subtype,
    Subgroup.comap_map_eq_self_of_injective
      (stabilizer Gamma d).subtype_injective]
  exact (inferInstance : (pCore 2 (stabilizer Gamma d)).Normal)

omit [Finite G] in
private theorem omegaOneCenter_le_centerAmbient (A : Subgroup G) :
    omegaOneCenter A ≤ (Subgroup.center A).map A.subtype := by
  unfold omegaOneCenter
  exact Subgroup.map_mono (Subgroup.map_subtype_le _)

omit [Finite G] in
private theorem centerAmbient_le_centralizer (A : Subgroup G) :
    (Subgroup.center A).map A.subtype ≤
      Subgroup.centralizer (A : Set G) := by
  intro x hx
  obtain ⟨xc, hxc, rfl⟩ := hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let ya : A := ⟨y, hy⟩
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hxc ya)

private theorem q_le_centralizer_z_of_neighbor
    {Gamma : CosetGraphContext G S P1 P2}
    (h73 : LemmaSevenThreeConclusion Gamma)
    {d l : Gamma.Vertex} (hl : l ∈ neighborhood Gamma d) :
    q Gamma d ≤ Subgroup.centralizer (z Gamma d : Set G) := by
  have hzcenter : z Gamma d ≤
      (Subgroup.center (q Gamma d)).map (q Gamma d).subtype :=
    (h73.center_core d l hl).trans (omegaOneCenter_le_centerAmbient _)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨yc, hyc, hycy⟩ := hzcenter hy
  let xq : q Gamma d := ⟨x, hx⟩
  have hcomm := Subgroup.mem_center_iff.mp hyc xq
  change y * x = x * y
  rw [← hycy]
  exact (congrArg Subtype.val hcomm).symm

omit [Finite G] in
private theorem twoCoreIn_le_sylow
    {W P : Subgroup G} (hWP : IsSylowTwoIn W P) :
    twoCoreIn P ≤ W := by
  obtain ⟨_, T, hTmap⟩ := hWP
  calc
    twoCoreIn P = (pCore 2 P).map P.subtype := rfl
    _ ≤ (T : Subgroup P).map P.subtype := Subgroup.map_mono
      ((pCore_isPGroup (p := 2) (G := P)).le_sylow_of_normal T)
    _ = W := hTmap

private theorem z_commutator_self_eq_bot_of_neighbor
    {Gamma : CosetGraphContext G S P1 P2}
    (h73 : LemmaSevenThreeConclusion Gamma)
    {d l : Gamma.Vertex} (hl : l ∈ neighborhood Gamma d) :
    ⁅z Gamma d, z Gamma d⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  have hzq := z_le_q_of_neighbor h73 hl
  have hzcenter : z Gamma d ≤
      (Subgroup.center (q Gamma d)).map (q Gamma d).subtype :=
    (h73.center_core d l hl).trans (omegaOneCenter_le_centerAmbient _)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨xc, hxc, hxcx⟩ := hzcenter hx
  let yq : q Gamma d := ⟨y, hzq hy⟩
  have hcomm := Subgroup.mem_center_iff.mp hxc yq
  change y * x = x * y
  rw [← hxcx]
  exact congrArg Subtype.val hcomm

private theorem quadratic
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    IsQuadraticOn (z Gamma cp.a) (z Gamma cp.a') ∧
      IsQuadraticOn (z Gamma cp.a') (z Gamma cp.a) := by
  let h73 := lemma_seven_three h Gamma
  have hcont := first_and_reverse_containment h Gamma cp
  have hlenpos := cp.length_pos
  have hfirst_mem : cp.firstStep ∈ neighborhood Gamma cp.a :=
    (mem_neighborhood_iff_adjacent Gamma).2 cp.firstStep_adj
  let penult : Gamma.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hpenult_end_adj : Gamma.adjacent penult cp.a' := by
    simpa [penult] using last_edge_adjacent Gamma cp
  have hpenult_mem : penult ∈ neighborhood Gamma cp.a' :=
    (mem_neighborhood_iff_adjacent Gamma).2
      (Gamma.adjacent_symm hpenult_end_adj)
  have hZa_ab : ⁅z Gamma cp.a, z Gamma cp.a⁆ = ⊥ :=
    z_commutator_self_eq_bot_of_neighbor h73 hfirst_mem
  have hZend_ab : ⁅z Gamma cp.a', z Gamma cp.a'⁆ = ⊥ :=
    z_commutator_self_eq_bot_of_neighbor h73 hpenult_mem
  have hZa_norm_Zend : z Gamma cp.a ≤
      Subgroup.normalizer (z Gamma cp.a' : Set G) :=
    hcont.1.1.trans (hcont.1.2.trans
      (stabilizer_le_normalizer_z Gamma cp.a'))
  have hZend_norm_Za : z Gamma cp.a' ≤
      Subgroup.normalizer (z Gamma cp.a : Set G) :=
    hcont.2.1.trans (stabilizer_le_normalizer_z Gamma cp.a)
  constructor
  · unfold IsQuadraticOn
    rw [eq_bot_iff]
    have hinner : ⁅z Gamma cp.a', z Gamma cp.a⁆ ≤ z Gamma cp.a := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hZend_norm_Za)
    exact (Subgroup.commutator_mono hinner le_rfl).trans
      (le_of_eq hZa_ab)
  · unfold IsQuadraticOn
    rw [eq_bot_iff]
    have hinner : ⁅z Gamma cp.a, z Gamma cp.a'⁆ ≤ z Gamma cp.a' := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hZa_norm_Zend)
    exact (Subgroup.commutator_mono hinner le_rfl).trans
      (le_of_eq hZend_ab)

private theorem commutator_case
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    ⁅z Gamma cp.a, z Gamma cp.a'⁆ ≠ ⊥ →
      (∀ T : Sylow 2 ↥(stabilizer Gamma cp.a'),
        sylowTwoAmbient (stabilizer Gamma cp.a') T ⊓
            Subgroup.centralizer (z Gamma cp.a' : Set G) = q Gamma cp.a') ∧
      IsCriticalPair Gamma cp.a' cp.a := by
  intro hcomm
  let h73 := lemma_seven_three h Gamma
  have hcont := first_and_reverse_containment h Gamma cp
  have hlenpos := cp.length_pos
  let penult : Gamma.Vertex := cp.path ⟨cp.length - 1, by omega⟩
  have hpenult_end_adj : Gamma.adjacent penult cp.a' := by
    simpa [penult] using last_edge_adjacent Gamma cp
  have hpenult_mem : penult ∈ neighborhood Gamma cp.a' :=
    (mem_neighborhood_iff_adjacent Gamma).2
      (Gamma.adjacent_symm hpenult_end_adj)
  let Te : Sylow 2 ↥(stabilizer Gamma cp.a' ⊓ stabilizer Gamma penult) :=
    default
  let W : Subgroup G :=
    sylowTwoAmbient (stabilizer Gamma cp.a' ⊓ stabilizer Gamma penult) Te
  have hedge := h73.sylow_and_core cp.a' penult hpenult_mem Te
  have hWcentral : W ⊓ Subgroup.centralizer (z Gamma cp.a' : Set G) =
      q Gamma cp.a' := by
    have halt := h73.centralizer_alternative cp.a' penult hpenult_mem Te
    rcases halt with halt | halt
    · exact halt
    · exfalso
      have hZendCentralizes : z Gamma cp.a' ≤
          Subgroup.centralizer (stabilizer Gamma cp.a' : Set G) := by
        rw [halt.1]
        exact (omegaOneCenter_le_centerAmbient _).trans
          (centerAmbient_le_centralizer _)
      have hZendZa : z Gamma cp.a' ≤
          Subgroup.centralizer (z Gamma cp.a : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyP := hcont.1.2 (hcont.1.1 hy)
        have hxC := Subgroup.mem_centralizer_iff.mp (hZendCentralizes hx) y hyP
        exact hxC
      apply hcomm
      rw [Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hZendZa
  constructor
  · intro T
    let R : Subgroup G := sylowTwoAmbient (stabilizer Gamma cp.a') T
    have hRP : IsSylowTwoIn R (stabilizer Gamma cp.a') :=
      ⟨Subgroup.map_subtype_le _, T, rfl⟩
    have hqR : q Gamma cp.a' ≤ R := by
      rw [q, Gamma.twoCoreAt_def]
      exact twoCoreIn_le_sylow hRP
    have hqC : q Gamma cp.a' ≤
        Subgroup.centralizer (z Gamma cp.a' : Set G) :=
      q_le_centralizer_z_of_neighbor h73 hpenult_mem
    apply le_antisymm
    · intro x hx
      obtain ⟨_, Tedge, hTedgeMap⟩ := hedge.1
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq
        (stabilizer Gamma cp.a') Tedge T
      have hRmap : R = W.map (MulAut.conj (g : G)).toMonoidHom := by
        have hs := sylowAmbient_smul (stabilizer Gamma cp.a') Tedge g
        change sylowTwoAmbient (stabilizer Gamma cp.a') Tedge = W at hTedgeMap
        rw [hg] at hs
        change R = (sylowTwoAmbient
          (stabilizer Gamma cp.a') Tedge).map
            (MulAut.conj (g : G)).toMonoidHom at hs
        rw [hTedgeMap] at hs
        exact hs
      have hgZ : (g : G) ∈
          Subgroup.normalizer (z Gamma cp.a' : Set G) :=
        stabilizer_le_normalizer_z Gamma cp.a' g.property
      have hnormC : Subgroup.normalizer (z Gamma cp.a' : Set G) ≤
          Subgroup.normalizer
            (Subgroup.centralizer (z Gamma cp.a' : Set G) : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          (Subgroup.centralizer_le_normalizer (z Gamma cp.a' : Set G))).mp
            inferInstance
      have hgC := hnormC hgZ
      have hgQ : (g : G) ∈
          Subgroup.normalizer (q Gamma cp.a' : Set G) :=
        stabilizer_le_normalizer_q Gamma cp.a' g.property
      have hxR : x ∈ R := hx.1
      rw [hRmap] at hxR
      obtain ⟨w, hwW, hwx⟩ := hxR
      have hwx' : (g : G) * (w : G) * (g : G)⁻¹ = x := by
        simpa using hwx
      have hwC : (w : G) ∈
          Subgroup.centralizer (z Gamma cp.a' : Set G) := by
        apply (Subgroup.mem_set_normalizer_iff.mp hgC (w : G)).2
        change (g : G) * (w : G) * (g : G)⁻¹ ∈
          Subgroup.centralizer (z Gamma cp.a' : Set G)
        rw [hwx']
        exact hx.2
      have hwQ : (w : G) ∈ q Gamma cp.a' := by
        rw [← hWcentral]
        exact ⟨hwW, hwC⟩
      have hxQ := (Subgroup.mem_set_normalizer_iff.mp hgQ (w : G)).1 hwQ
      change (g : G) * (w : G) * (g : G)⁻¹ ∈ q Gamma cp.a' at hxQ
      rwa [hwx'] at hxQ
    · exact le_inf hqR hqC
  · constructor
    · calc
        Gamma.distance cp.a' cp.a = Gamma.distance cp.a cp.a' :=
          Gamma.distance_symm _ _
        _ = sInf {n : ℕ | ∃ d d' : Gamma.Vertex,
            Gamma.distance d d' = n ∧
              ¬ Gamma.zAt d ≤ Gamma.twoCoreAt d'} := cp.critical.1
    · intro hZendQa
      change z Gamma cp.a' ≤ q Gamma cp.a at hZendQa
      apply hcomm
      rw [Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hZendQa.trans
        ((le_of_eq (edge_centralizer h Gamma cp).symm).trans inf_le_right)

/-- **Stellmacher (7.4).**  Containment, centralizer, critical-pair, and
quadratic-action properties for a critical path. -/
public theorem lemma_seven_four
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma) :
    LemmaSevenFourConclusion Gamma cp := by
  have hcont := first_and_reverse_containment h Gamma cp
  exact
    { first_containment := hcont.1
      reverse_containment := hcont.2
      edge_centralizer := edge_centralizer h Gamma cp
      commutator_case := commutator_case h Gamma cp
      quadratic := quadratic h Gamma cp }

end Stellmacher.SectionsFiveToSeven
