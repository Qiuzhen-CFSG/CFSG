module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.BinaryRee.Reflections
/-!
# Coherent reflections through the marked binary Ree chamber

An involution reversing nine edges reverses every vertex of a sixteen-cycle:
the second half follows by applying the involution again. Reflections at two
adjacent vertices therefore have product acting by two steps around that
cycle. Its eighth power fixes an oriented edge and hence is the identity.

Edge transitivity places an apartment through the original two base vertices.
The resulting involutions belong to the actual endpoint images and are outside
the actual common Borel. All statements follow from the literal source smallness
witness; no reflection marking or braid relation is supplied as an input.

Source: Aschbacher--Smith F.4.15--16, printed pp.281--282.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
open SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (c : Completion G)

private theorem mirror_prefix_getVert {v : c.Vertex} (p : c.graph.Walk v v)
    (hl : p.length = 16) (g : G)
    (hm : (p.take 9).support.map (g • ·) = (p.reverse.take 9).support)
    (i : ℕ) (hi : i ≤ 9) : g • p.getVert i = p.getVert (16 - i) := by
  have h := congrArg (fun l : List c.Vertex => l[i]?) hm
  rw [List.getElem?_map, Walk.support_take, Walk.support_take,
    List.getElem?_take_of_lt (by omega : i < 9 + 1),
    List.getElem?_take_of_lt (by omega : i < 9 + 1),
    ← p.getVert_eq_support_getElem? (by omega),
    ← p.reverse.getVert_eq_support_getElem? (by rw [Walk.length_reverse]; omega)] at h
  simpa only [Option.map_some, Option.some.injEq, Walk.getVert_reverse, hl] using h

/-- Reflection of a nine-edge prefix determines the action on the entire apartment. -/
theorem mirror_getVert {v : c.Vertex} (p : c.graph.Walk v v)
    (hl : p.length = 16) (g : G) (hsq : g ^ 2 = 1)
    (hm : (p.take 9).support.map (g • ·) = (p.reverse.take 9).support)
    (i : ℕ) (hi : i ≤ 16) : g • p.getVert i = p.getVert (16 - i) := by
  by_cases h9 : i ≤ 9
  · exact mirror_prefix_getVert c p hl g hm i h9
  · have hj : 16 - i ≤ 9 := by omega
    have hh := mirror_prefix_getVert c p hl g hm (16 - i) hj
    have he : 16 - (16 - i) = i := by omega
    rw [he] at hh
    have hh' := congrArg (g • ·) hh
    rw [← mul_smul, ← pow_two, hsq, one_smul] at hh'
    exact hh'.symm

private theorem rotate_first_getVert [DecidableEq c.Vertex] {v : c.Vertex} (p : c.graph.Walk v v)
    (u : c.Vertex) (hu : u ∈ p.support) (heu : u = p.getVert 1)
    (hl : p.length = 16) (i : ℕ) (hi : i ≤ 15) :
    (p.rotate u hu).getVert i = p.getVert (i + 1) := by
  cases p with
  | nil => simp at hl
  | @cons v w v hadj q =>
    have hq : q.length = 15 := by simp only [Walk.length_cons] at hl; omega
    have he : u = w := heu.trans (Walk.getVert_zero q)
    clear heu
    subst u
    simp only [Walk.rotate]
    rw [Walk.dropUntil, dif_neg hadj.ne, Walk.takeUntil, dif_neg hadj.ne,
      Walk.dropUntil_first, Walk.takeUntil_first, Walk.getVert_append', hq, if_pos hi]
    rfl

/-- Adjacent apartment reflections satisfy the binary Ree braid relation. -/
theorem exists_cycle_reflection_pair (hsmall : c.Small)
    {v : c.Vertex} (p : c.graph.Walk v v) (hp : p.IsCycle) (hl : p.length = 16) :
    ∃ s t : G, s • v = v ∧ t • p.getVert 1 = p.getVert 1 ∧
      s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s ≠ 1 ∧ t ≠ 1 ∧
      s • p.getVert 1 = p.getVert 15 ∧ t • v = p.getVert 2 ∧
      (∀ w ∈ p.support, s • w ∈ p.support) ∧
      (∀ w ∈ p.support, t • w ∈ p.support) ∧ (s * t) ^ 8 = 1 := by
  classical
  obtain ⟨s, hsv, hs2, hsne, hs1, hsA, hsm⟩ := exists_cycle_reflection c hsmall p hp hl
  let q := p.rotate (p.getVert 1) (p.getVert_mem_support 1)
  have hq : q.IsCycle := hp.rotate _
  have hql : q.length = 16 := by simpa only [q, Walk.length_rotate] using hl
  obtain ⟨t, htv, ht2, htne, ht1, htA, htm⟩ := exists_cycle_reflection c hsmall q hq hql
  have hs (i : ℕ) (hi : i ≤ 16) := mirror_getVert c p hl s hs2 hsm i hi
  have ht (i : ℕ) (hi : i ≤ 16) := mirror_getVert c q hql t ht2 htm i hi
  have hqp (i : ℕ) (hi : i ≤ 15) : q.getVert i = p.getVert (i + 1) :=
    rotate_first_getVert c p _ _ rfl hl i hi
  have ht0 : t • v = p.getVert 2 := by
    have h := ht 15 (by decide)
    rw [hqp 15 (by decide), hqp 1 (by decide)] at h
    have he : p.getVert (15 + 1) = v := by change p.getVert 16 = v; rw [← hl, Walk.getVert_length]
    rwa [he] at h
  have htA' : ∀ w ∈ p.support, t • w ∈ p.support := by
    intro w hw
    exact (Walk.mem_support_rotate_iff ..).mp (htA w ((Walk.mem_support_rotate_iff ..).mpr hw))
  refine ⟨s, t, hsv, htv, hs2, ht2, hsne, htne, hs1, ht0, hsA, htA', ?_⟩
  have h16 : p.getVert 16 = v := by rw [← hl, Walk.getVert_length]
  have ht_ge (i : ℕ) (hi2 : 2 ≤ i) (hi16 : i ≤ 16) :
      t • p.getVert i = p.getVert (18 - i) := by
    have hh := ht (i - 1) (by omega)
    rw [hqp (i - 1) (by omega), hqp (16 - (i - 1)) (by omega)] at hh
    have he1 : i - 1 + 1 = i := by omega
    have he2 : 16 - (i - 1) + 1 = 18 - i := by omega
    rwa [he1, he2] at hh
  have hst (i : Fin 16) : (s * t) • p.getVert i = p.getVert ((i.val + 14) % 16) := by
    fin_cases i <;> norm_num only [Fin.val_mk, mul_smul, Nat.reduceAdd, Nat.reduceMod]
    · rw [Walk.getVert_zero, ht0, hs 2 (by decide)]
    · rw [htv, hs 1 (by decide)]
    all_goals rw [ht_ge _ (by decide) (by decide), hs _ (by decide)]
  apply cycle_edge_fixer_eq_one c (cycle_bound_of_small c hsmall) p hp hl ((s * t) ^ 8)
  · have hh : ∀ n : ℕ, (s * t) ^ n • p.getVert 0 = p.getVert ((14 * n) % 16) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', mul_smul, ih, hst ⟨_, Nat.mod_lt _ (by decide)⟩]
        congr 1
        change ((14 * n) % 16 + 14) % 16 = (14 * (n + 1)) % 16
        omega
    simpa only [Walk.getVert_zero, Nat.reduceMul, Nat.reduceMod] using hh 8
  · have hh : ∀ n : ℕ, (s * t) ^ n • p.getVert 1 = p.getVert ((1 + 14 * n) % 16) := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', mul_smul, ih, hst ⟨_, Nat.mod_lt _ (by decide)⟩]
        congr 1
        change ((1 + 14 * n) % 16 + 14) % 16 = (1 + 14 * (n + 1)) % 16
        omega
    simpa only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod] using hh 8
  · intro w hw
    have hh : ∀ n : ℕ, (s * t) ^ n • w ∈ p.support := by
      intro n
      induction n with
      | zero => simpa only [pow_zero, one_smul] using hw
      | succ n ih => simpa only [pow_succ', mul_smul] using hsA _ (htA' _ ih)
    exact hh 8
/-- A source apartment can be placed through the original marked chamber. -/
theorem exists_marked_cycle (hsmall : c.Small) :
    ∃ p : c.graph.Walk (base c.family false) (base c.family false),
      p.IsCycle ∧ p.length = 16 ∧ p.getVert 1 = base c.family true := by
  classical
  obtain ⟨v, p, hp, hl⟩ := exists_sixteen_cycle_of_small c hsmall
  have hex : ∃ v : c.Vertex, v.type = false ∧
      ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length = 16 := by
    by_cases hv : v.type = false
    · exact ⟨v, hv, p, hp, hl⟩
    · have ha : c.graph.Adj v (p.getVert 1) := by
        simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
      have hf : (p.getVert 1).type = false := by
        have ht := ha.1
        cases h₁ : v.type <;> cases h₂ : (p.getVert 1).type <;> simp_all
      exact ⟨p.getVert 1, hf, p.rotate _ (p.getVert_mem_support 1),
        hp.rotate _, by simpa only [Walk.length_rotate] using hl⟩
  obtain ⟨v, hv, p, hp, hl⟩ := hex
  have ha : c.graph.Adj v (p.getVert 1) := by
    simpa only [Walk.getVert_zero] using p.adj_getVert_succ (i := 0) (by omega)
  have ht : (p.getVert 1).type = true := by
    have hh := ha.1
    cases h₂ : (p.getVert 1).type <;> simp_all
  obtain ⟨g, hgv, hgw⟩ := incident_common_translate c.family ha.2
  rw [hv] at hgv
  rw [ht] at hgw
  have hv' : ((graphAction c).hom g⁻¹) v = base c.family false := by
    change g⁻¹ • v = base c.family false
    rw [← hgv, inv_smul_smul]
  let q := (p.map ((graphAction c).hom g⁻¹)).copy hv' hv'
  refine ⟨q, ?_, ?_, ?_⟩
  · exact (Walk.isCycle_copy _ _).mpr (hp.map (MulAction.injective g⁻¹))
  · simpa only [q, Walk.length_copy, Walk.length_map] using hl
  · change ((p.map ((graphAction c).hom g⁻¹)).copy hv' hv').getVert 1 = _
    rw [Walk.getVert_copy, Walk.getVert_map]
    change g⁻¹ • p.getVert 1 = _
    rw [← hgw, inv_smul_smul]

/-- The actual source endpoint groups contain coherent adjacent reflections,
with their eighth-power braid and literal marked apartment. -/
theorem exists_marked_reflection_pair (hsmall : c.Small) :
    ∃ p : c.graph.Walk (base c.family false) (base c.family false),
      p.IsCycle ∧ p.length = 16 ∧ p.getVert 1 = base c.family true ∧
      ∃ s ∈ c.left.range, ∃ t ∈ c.right.range,
        s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s ∉ c.middle.range ∧ t ∉ c.middle.range ∧
        (s * t) ^ 8 = 1 ∧ s • p.getVert 1 = p.getVert 15 ∧
        t • base c.family false = p.getVert 2 ∧
        (∀ w ∈ p.support, s • w ∈ p.support) ∧
        (∀ w ∈ p.support, t • w ∈ p.support) := by
  obtain ⟨p, hp, hl, hp1⟩ := exists_marked_cycle c hsmall
  obtain ⟨s, t, hsv, htv, hs2, ht2, _, _, hs1, ht0, hsA, htA, hst⟩ :=
    exists_cycle_reflection_pair c hsmall p hp hl
  have hsL : s ∈ c.left.range := by
    change s ∈ c.family false
    rw [← Subgroup.CosetGeometry.stabilizer_base c.family false]
    exact hsv
  have htR : t ∈ c.right.range := by
    change t ∈ c.family true
    rw [← Subgroup.CosetGeometry.stabilizer_base c.family true]
    rwa [hp1] at htv
  refine ⟨p, hp, hl, hp1, s, hsL, t, htR, hs2, ht2, ?_, ?_, hst, hs1, ht0, hsA, htA⟩
  · intro hsB
    have hsR := c.middle_le_right hsB
    change s ∈ c.family true at hsR
    rw [← Subgroup.CosetGeometry.stabilizer_base c.family true] at hsR
    have he : p.getVert 1 = p.getVert 15 := by
      rw [← hs1, hp1]
      exact hsR.symm
    have hi := hp.getVert_injOn' (by change 1 ≤ p.length - 1; omega)
      (by change 15 ≤ p.length - 1; omega) he
    omega
  · intro htB
    have htL := c.middle_le_left htB
    change t ∈ c.family false at htL
    rw [← Subgroup.CosetGeometry.stabilizer_base c.family false] at htL
    have he : p.getVert 0 = p.getVert 2 := by
      rw [Walk.getVert_zero, ← ht0]
      exact htL.symm
    have hi := hp.getVert_injOn' (by change 0 ≤ p.length - 1; omega)
      (by change 2 ≤ p.length - 1; omega) he
    omega

end CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee.Completion
