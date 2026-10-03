module

public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts

/-!
# Transport of neighboring core intersections

Along a critical path, local transitivity carries the first neighbor to any
other neighbor. Equivariance of stabilizers and their 2-cores therefore
identifies the conjugate core intersections. If the initial intersection is
normal, it equals each such neighbor intersection. A finite-cardinality
comparison also shows that containment in a generating neighbor core would
force this normality. Distance and critical-minimality facts support the
longer-path application of Stellmacher (7.6).
The ambient two-core covariance under a group automorphism is public so
later critical-pair arguments can transport residual cores by the same map.

Source: B. Stellmacher, Journal of Algebra 190 (1997), Lemma (7.6),
pp. 35–36; `refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise

namespace Stellmacher.SectionsFiveToSeven.SevenSix

open CosetGraphContext

universe u v

private theorem mem_stabilizer_iff
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {g : G} {d : Gamma.Vertex} :
    g ∈ stabilizer Gamma d ↔ Gamma.act g d = d := by
  have hdef : (stabilizer Gamma d : Set G) =
      {x | Gamma.act x d = d} := Gamma.stabilizer_def d
  exact Set.ext_iff.mp hdef g

private theorem stabilizer_act
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    stabilizer Gamma (Gamma.act g d) =
      conjugateBy (stabilizer Gamma d) g⁻¹ := by
  ext x
  rw [mem_stabilizer_iff, conjugateBy, Subgroup.mem_map_equiv,
    mem_stabilizer_iff]
  simp only [MulAut.conj_symm_apply, inv_inv]
  constructor
  · intro hx
    calc
      Gamma.act (g * x * g⁻¹) d =
          Gamma.act g⁻¹ (Gamma.act (g * x) d) := Gamma.act_mul _ _ _
      _ = Gamma.act g⁻¹ (Gamma.act x (Gamma.act g d)) := by
        rw [Gamma.act_mul]
      _ = Gamma.act g⁻¹ (Gamma.act g d) := by rw [hx]
      _ = Gamma.act (g * g⁻¹) d := (Gamma.act_mul _ _ _).symm
      _ = d := by simp [Gamma.act_one]
  · intro hx
    calc
      Gamma.act x (Gamma.act g d) = Gamma.act (g * x) d :=
        (Gamma.act_mul _ _ _).symm
      _ = Gamma.act g (Gamma.act (g * x * g⁻¹) d) := by
        rw [← Gamma.act_mul]
        simp [mul_assoc]
      _ = Gamma.act g d := by rw [hx]

/-- The ambient two-core commutes with transport by a group automorphism. -/
public theorem twoCoreIn_map_equiv
    {G : Type u} [Group G] (f : G ≃* G) (P : Subgroup G) :
    twoCoreIn (P.map f.toMonoidHom) =
      (twoCoreIn P).map f.toMonoidHom := by
  let fP : P ≃* P.map f.toMonoidHom :=
    P.equivMapOfInjective f.toMonoidHom f.injective
  have hcore : (pCore 2 P).map fP.toMonoidHom =
      pCore 2 (P.map f.toMonoidHom) := pCore_map_iso 2 fP
  unfold twoCoreIn
  rw [← hcore, Subgroup.map_map, Subgroup.map_map]
  congr 1

public theorem q_act
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    (g : G) (d : Gamma.Vertex) :
    q Gamma (Gamma.act g d) =
      (q Gamma d).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [q]
  rw [Gamma.twoCoreAt_def, Gamma.twoCoreAt_def]
  have hs := stabilizer_act Gamma g d
  simp only [stabilizer] at hs
  rw [hs, conjugateBy, twoCoreIn_map_equiv]

public theorem adjacent_iff_distance_eq_one
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} :
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
      have heq := (Gamma.distance_zero_iff d l).mp hzero
      subst l
      rcases Gamma.coset₁_surjective d with ⟨g, hg | hg⟩
      · exact Gamma.no_adj_coset₁_coset₁ g g (hg ▸ hdl)
      · exact Gamma.no_adj_coset₂_coset₂ g g (hg ▸ hdl)
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

public theorem mem_neighborhood_iff_adjacent
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G} (Gamma : CosetGraphContext G S P1 P2)
    {d l : Gamma.Vertex} :
    l ∈ neighborhood Gamma d ↔ Gamma.adjacent d l := by
  rw [neighborhood, Gamma.neighbors_def]
  change Gamma.distance l d = 1 ↔ Gamma.adjacent d l
  rw [Gamma.distance_symm]
  exact (adjacent_iff_distance_eq_one Gamma).symm

public theorem path_distance_le
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
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

public theorem critical_minimality
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
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

private theorem map_conj_eq_self_of_mem_normalizer
    {G : Type u} [Group G] (A : Subgroup G) (x : G)
    (hx : x ∈ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj x).toMonoidHom = A := by
  ext y
  rw [Subgroup.mem_map_equiv]
  change x⁻¹ * y * x ∈ A ↔ y ∈ A
  have hn := (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * y * x))
  simpa [mul_assoc] using hn

private theorem neighbor_core_intersection_conjugate
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (m : Gamma.Vertex) (hm : m ∈ neighborhood Gamma cp.firstStep) :
    ∃ g : stabilizer Gamma cp.firstStep,
      q Gamma m ⊓ q Gamma cp.firstStep =
        (q Gamma cp.a ⊓ q Gamma cp.firstStep).map
          (MulAut.conj ((g : G)⁻¹)).toMonoidHom := by
  have ha : cp.a ∈ neighborhood Gamma cp.firstStep :=
    (mem_neighborhood_iff_adjacent Gamma).2
      (Gamma.adjacent_symm cp.firstStep_adj)
  obtain ⟨g, hg⟩ := (lemma_seven_one h Gamma).local_transitivity
    cp.firstStep ha hm
  have hfix : Gamma.act (g : G) cp.firstStep = cp.firstStep :=
    (mem_stabilizer_iff Gamma).1 g.property
  refine ⟨g, ?_⟩
  calc
    q Gamma m ⊓ q Gamma cp.firstStep =
        q Gamma (Gamma.act (g : G) cp.a) ⊓
          q Gamma (Gamma.act (g : G) cp.firstStep) := by rw [hg, hfix]
    _ = (q Gamma cp.a).map
          (MulAut.conj ((g : G)⁻¹)).toMonoidHom ⊓
        (q Gamma cp.firstStep).map
          (MulAut.conj ((g : G)⁻¹)).toMonoidHom := by
      rw [q_act, q_act]
    _ = (q Gamma cp.a ⊓ q Gamma cp.firstStep).map
          (MulAut.conj ((g : G)⁻¹)).toMonoidHom :=
      (Subgroup.map_inf _ _ _ (MulAut.conj ((g : G)⁻¹)).injective).symm

public theorem core_intersection_eq_neighbor_intersection_of_normal
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (hnormal : IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep))
    (m : Gamma.Vertex) (hm : m ∈ neighborhood Gamma cp.firstStep) :
    q Gamma m ⊓ q Gamma cp.firstStep =
      q Gamma cp.a ⊓ q Gamma cp.firstStep := by
  obtain ⟨g, hg⟩ := neighbor_core_intersection_conjugate h Gamma cp m hm
  rw [hg]
  apply map_conj_eq_self_of_mem_normalizer
  have hnorm : stabilizer Gamma cp.firstStep ≤
      Subgroup.normalizer (q Gamma cp.a ⊓ q Gamma cp.firstStep : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hnormal.1).mp hnormal.2
  exact hnorm ((stabilizer Gamma cp.firstStep).inv_mem g.property)

public theorem core_intersection_normal_of_neighbor_containment
    {G : Type u} [Group G] [Finite G]
    {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Gamma : CosetGraphContext G S P1 P2) (cp : CriticalPath Gamma)
    (m : Gamma.Vertex) (hm : m ∈ neighborhood Gamma cp.firstStep)
    (hgen : q Gamma m ⊔
        (stabilizer Gamma cp.a ⊓ stabilizer Gamma cp.firstStep) =
      stabilizer Gamma cp.firstStep)
    (hle : q Gamma cp.a ⊓ q Gamma cp.firstStep ≤ q Gamma m) :
    IsNormalIn (q Gamma cp.a ⊓ q Gamma cp.firstStep)
      (stabilizer Gamma cp.firstStep) := by
  let N := q Gamma cp.a ⊓ q Gamma cp.firstStep
  let Nm := q Gamma m ⊓ q Gamma cp.firstStep
  let P := stabilizer Gamma cp.firstStep
  let I := stabilizer Gamma cp.a ⊓ P
  have hconj := neighbor_core_intersection_conjugate h Gamma cp m hm
  obtain ⟨g, hg⟩ := hconj
  have hNleNm : N ≤ Nm := le_inf hle inf_le_right
  have hcard : Nat.card Nm = Nat.card N := by
    dsimp [Nm, N]
    rw [hg, Subgroup.card_map_of_injective
      (MulAut.conj ((g : G)⁻¹)).injective]
  have hN_eq : N = Nm :=
    Subgroup.eq_of_le_of_card_ge hNleNm hcard.le
  have hqm_le_P : q Gamma m ≤ P := by
    let T : Sylow 2 ↥(stabilizer Gamma m ⊓ P) := default
    have hm' : cp.firstStep ∈ neighborhood Gamma m :=
      (mem_neighborhood_iff_adjacent Gamma).2
        (Gamma.adjacent_symm ((mem_neighborhood_iff_adjacent Gamma).1 hm))
    exact (lemma_seven_three h Gamma).sylow_and_core m cp.firstStep hm' T |>.2.2
  have hqm_norm_Nm : q Gamma m ≤ Subgroup.normalizer (Nm : Set G) := by
    exact (le_inf Subgroup.le_normalizer
      (hqm_le_P.trans (stabilizer_le_normalizer_q Gamma cp.firstStep))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hI_norm_N : I ≤ Subgroup.normalizer (N : Set G) := by
    exact (le_inf (inf_le_left.trans (stabilizer_le_normalizer_q Gamma cp.a))
      (inf_le_right.trans (stabilizer_le_normalizer_q Gamma cp.firstStep))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  have hqfirst_le_P : q Gamma cp.firstStep ≤ P := by
    rw [q, Gamma.twoCoreAt_def]
    exact twoCoreIn_le _
  have hNleP : N ≤ P := inf_le_right.trans hqfirst_le_P
  refine ⟨hNleP, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNleP]
  have hgen' : q Gamma m ⊔ I = P := by
    simpa [I, P] using hgen
  rw [← hgen']
  exact sup_le (by simpa [hN_eq] using hqm_norm_Nm) hI_norm_N

end Stellmacher.SectionsFiveToSeven.SevenSix
