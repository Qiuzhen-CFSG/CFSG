module

public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure
public import Theory.Mathieu.M23.QuasithinGeometry.PairPlane
public import Theory.Combinatorics.PairGraphTriangleClosure.FourSubsetBase.SystemBridge

/-!
# The standard M23 uniqueness system

The concrete design automorphism group acts faithfully and transitively on
vertices and oriented edges of the pair graph. Its four-set stabilizer has the
induced pair graph on Λ as its local edge orbit. The three generation conditions
are proved, not imposed: connectedness gives global generation; four-transitivity
on the complement and two local swaps give generation of the pair stabilizer;
the symmetric four-set calculation gives generation of the local group.

The resulting system has its local graph as a base in the closed-walk sense.
The final subgroup identifications retain the original inclusions into M23,
so that the field-plane and heptad maps can be used in a similarity.

Source: Aschbacher--Smith, §5.2, printed pp.655--658, especially the standard
system on p.657; Aschbacher, *Sporadic Groups*, §37, pp.198--200.
-/

@[expose] public section

open scoped Pointwise
open Theory.Combinatorics.PairGraph
namespace Sporadic.Mathieu.M23Geometry

private def tripleEmbedding {α : Type*} (a b c : α)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : Fin 3 ↪ α where
  toFun := ![a, b, c]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

private theorem moveTriple (a b c d e f : Fin 23)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    ∃ g : M23, g • a = d ∧ g • b = e ∧ g • c = f := by
  let := m23_isFourPretransitive
  let := MulAction.isMultiplyPretransitive_of_le (G := M23) (α := Fin 23)
    (m := 3) (n := 4) (by decide) (by simp)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M23
    (tripleEmbedding a b c hab hac hbc) (tripleEmbedding d e f hde hdf hef)
  exact ⟨g, congrArg (fun z : Fin 3 ↪ Fin 23 => z 0) hg,
    congrArg (fun z : Fin 3 ↪ Fin 23 => z 1) hg,
    congrArg (fun z : Fin 3 ↪ Fin 23 => z 2) hg⟩

private theorem localMoveTriple (a b c d e f : lambda)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    ∃ g : fourStabilizer, (g : M23) • a.val = d.val ∧
      (g : M23) • b.val = e.val ∧ (g : M23) • c.val = f.val := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_smul_eq_embedding
    (tripleEmbedding a b c hab hac hbc) (tripleEmbedding d e f hde hdf hef)
  obtain ⟨g, hg⟩ := lambda_action_surjective σ
  have he (i : Fin 3) := congrArg (fun z : Fin 3 ↪ lambda => (z i).val) hσ
  refine ⟨g, ?_, ?_, ?_⟩
  all_goals simp only [← hg] at he
  · exact he 0
  · exact he 1
  · exact he 2

private theorem adjacentCoordinates {v w : Vertex (Fin 23)}
    (h : (graph (Fin 23)).Adj v w) :
    ∃ a b c : Fin 23, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      v.val = {a, b} ∧ w.val = {b, c} := by
  obtain ⟨b, hb⟩ := h.2
  obtain ⟨d, e, hde, hv⟩ := Finset.card_eq_two.mp v.property
  obtain ⟨f, k, hfk, hw⟩ := Finset.card_eq_two.mp w.property
  have hb' := Finset.mem_inter.mp hb
  rw [hv] at hb'
  rw [hw] at hb'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
  have hn : v.val ≠ w.val := fun hh => h.ne (Subtype.ext hh)
  rcases hb' with ⟨rfl | rfl, h | h⟩ <;> subst b
  · exact ⟨e, f, k, hde.symm, by intro hh; apply hn; simp_all [Finset.pair_comm],
      hfk, by simpa [Finset.pair_comm] using hv, hw⟩
  · exact ⟨e, k, f, hde.symm, by intro hh; apply hn; simp_all [Finset.pair_comm],
      hfk.symm, by simpa [Finset.pair_comm] using hv, by simpa [Finset.pair_comm] using hw⟩
  · exact ⟨d, f, k, hde, by intro hh; apply hn; simp_all [Finset.pair_comm], hfk, hv, hw⟩
  · exact ⟨d, k, f, hde, by intro hh; apply hn; simp_all [Finset.pair_comm],
      hfk.symm, hv, by simpa [Finset.pair_comm] using hw⟩

/-- Four-transitivity gives transitivity on oriented edges of the pair graph. -/
theorem pairGraph_edge_transitive (v w : Vertex (Fin 23))
    (h : (graph (Fin 23)).Adj v w) :
    ∃ g : M23, g • x = v ∧ g • y = w := by
  obtain ⟨a, b, c, hab, hac, hbc, hv, hw⟩ := adjacentCoordinates h
  obtain ⟨g, ha, hb, hc⟩ := moveTriple 17 11 5 a b c
    (by decide) (by decide) (by decide) hab hac hbc
  refine ⟨g, Subtype.ext ?_, Subtype.ext ?_⟩
  · change g • ({11, 17} : Finset (Fin 23)) = _
    simp [Finset.smul_finset_insert, Finset.smul_finset_singleton, ha, hb, hv, Finset.pair_comm]
  · change g • ({5, 11} : Finset (Fin 23)) = _
    simp [Finset.smul_finset_insert, Finset.smul_finset_singleton, hb, hc, hw, Finset.pair_comm]

/-- The local edge orbit is the full induced pair graph on the four-set. -/
theorem fourStabilizer_edge_transitive (v w : Vertex (Fin 23))
    (h : (graph (Fin 23)).Adj v w) (hv : v.val ⊆ lambda) (hw : w.val ⊆ lambda) :
    ∃ g : fourStabilizer, (g : M23) • x = v ∧ (g : M23) • y = w := by
  obtain ⟨a, b, c, hab, hac, hbc, hv', hw'⟩ := adjacentCoordinates h
  have ha : a ∈ lambda := hv (by simp [hv'])
  have hb : b ∈ lambda := hv (by simp [hv'])
  have hc : c ∈ lambda := hw (by simp [hw'])
  obtain ⟨g, hga, hgb, hgc⟩ := localMoveTriple
    ⟨17, by decide⟩ ⟨11, by decide⟩ ⟨5, by decide⟩ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    (by decide) (by decide) (by decide)
    (fun h => hab (congrArg Subtype.val h)) (fun h => hac (congrArg Subtype.val h))
    (fun h => hbc (congrArg Subtype.val h))
  refine ⟨g, Subtype.ext ?_, Subtype.ext ?_⟩
  · change (g : M23) • ({11, 17} : Finset (Fin 23)) = _
    simp [Finset.smul_finset_insert, Finset.smul_finset_singleton, hga, hgb, hv', Finset.pair_comm]
  · change (g : M23) • ({5, 11} : Finset (Fin 23)) = _
    simp [Finset.smul_finset_insert, Finset.smul_finset_singleton, hgb, hgc, hw', Finset.pair_comm]


/-- Stabilizers on pair vertices are the original stabilizers on their supports. -/
theorem pairGraph_stabilizer (v : Vertex (Fin 23)) :
    MulAction.stabilizer M23 v = MulAction.stabilizer M23 v.val := by
  ext g
  exact Subtype.ext_iff

/-- The local group contains an element reversing the distinguished edge. -/
theorem fourStabilizer_exists_swap :
    ∃ g : fourStabilizer, (g : M23) • x = y ∧ (g : M23) • y = x :=
  fourStabilizer_edge_transitive y x x_adj_y.symm y_subset_lambda x_subset_lambda

private theorem neighbor_in_generated_orbit (v : Vertex (Fin 23))
    (hv : (graph (Fin 23)).Adj x v) :
    ∃ g ∈ fourStabilizer ⊔ pairStabilizer, g • x = v := by
  obtain ⟨t, ht, _⟩ := fourStabilizer_exists_swap
  obtain ⟨g, hg, hgv⟩ := pairGraph_edge_transitive x v hv
  have hgp : g ∈ pairStabilizer := congrArg Subtype.val hg
  refine ⟨g * t, (fourStabilizer ⊔ pairStabilizer).mul_mem
    (Subgroup.mem_sup_right hgp) (Subgroup.mem_sup_left t.property), ?_⟩
  rw [mul_smul, ht, hgv]

/-- The pair stabilizer and four-set stabilizer generate the concrete M23. -/
theorem four_pair_generate : fourStabilizer ⊔ pairStabilizer = ⊤ := by
  have orbit (v : Vertex (Fin 23)) :
      ∃ g ∈ fourStabilizer ⊔ pairStabilizer, g • x = v := by
    rcases distance_le_two x v with hv | hv | ⟨w, hw, hwv⟩
    · exact ⟨1, (fourStabilizer ⊔ pairStabilizer).one_mem, by simpa using hv⟩
    · exact neighbor_in_generated_orbit v hv
    · obtain ⟨g, hg, hxg⟩ := neighbor_in_generated_orbit w hw
      have hv' : (graph (Fin 23)).Adj x (g⁻¹ • v) := by
        have hh := smul_adj g⁻¹ hwv
        rwa [← hxg, inv_smul_smul] at hh
      obtain ⟨k, hk, hxk⟩ := neighbor_in_generated_orbit _ hv'
      exact ⟨g * k, (fourStabilizer ⊔ pairStabilizer).mul_mem hg hk,
        by rw [mul_smul, hxk, smul_inv_smul]⟩
  apply top_unique
  intro g _
  obtain ⟨h, hh, hx⟩ := orbit (g • x)
  have hk : h⁻¹ * g ∈ pairStabilizer := by
    change (h⁻¹ * g) • x.val = x.val
    have he : (h⁻¹ * g) • x = x := by rw [mul_smul, ← hx, inv_smul_smul]
    exact congrArg Subtype.val he
  simpa only [mul_inv_cancel_left] using
    (fourStabilizer ⊔ pairStabilizer).mul_mem hh (Subgroup.mem_sup_right hk)

/-- The action on pair vertices is transitive. -/
theorem pairGraph_vertex_transitive (v : Vertex (Fin 23)) : ∃ g : M23, g • x = v := by
  obtain ⟨a, b, hab, hv⟩ := Finset.card_eq_two.mp v.property
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a, b}) (t := (Finset.univ : Finset (Fin 23))) (by simp [Finset.card_pair hab])
  have hac : a ≠ c := by intro h; exact hc (by simp [h])
  have hbc : b ≠ c := by intro h; exact hc (by simp [h])
  obtain ⟨g, ha, hb, _⟩ := moveTriple 11 17 5 a b c
    (by decide) (by decide) (by decide) hab hac hbc
  refine ⟨g, Subtype.ext ?_⟩
  change g • ({11, 17} : Finset (Fin 23)) = _
  simp [Finset.smul_finset_insert, Finset.smul_finset_singleton, ha, hb, hv]

/-- The induced action on unordered pairs is faithful. -/
theorem pairGraph_faithful (g : M23) (hg : ∀ v : Vertex (Fin 23), g • v = v) : g = 1 := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro a
  change g • a = a
  by_contra h
  obtain ⟨c, _, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {a, g • a}) (t := (Finset.univ : Finset (Fin 23)))
    (by simp [Finset.card_pair (Ne.symm h)])
  have hac : a ≠ c := by intro he; exact hc (by simp [he])
  have hgc : g • a ≠ c := by intro he; exact hc (by simp [he])
  have he := congrArg Subtype.val (hg (pair a c hac))
  have hm : g • a ∈ ({a, c} : Finset (Fin 23)) := by
    change g • ({a, c} : Finset (Fin 23)) = {a, c} at he
    rw [← he]
    exact Finset.smul_mem_smul_finset (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  exact hm.elim h hgc

private theorem localSwap (a b : lambda) :
    ∃ g : fourStabilizer, ∀ z : lambda,
      (g : M23) • z.val = (Equiv.swap a b z).val := by
  obtain ⟨g, hg⟩ := lambda_action_surjective (Equiv.swap a b)
  exact ⟨g, fun z => congrArg Subtype.val (Equiv.congr_fun hg z)⟩

private theorem moveFourth (c : Fin 23) (hc11 : c ≠ 11) (hc17 : c ≠ 17) (hc5 : c ≠ 5) :
    ∃ g : M23, g • (11 : Fin 23) = 11 ∧ g • (17 : Fin 23) = 17 ∧
      g • (5 : Fin 23) = 5 ∧ g • (4 : Fin 23) = c := by
  let a : Fin 4 ↪ Fin 23 := ⟨![11, 17, 5, 4], by decide⟩
  let b : Fin 4 ↪ Fin 23 := ⟨![11, 17, 5, c], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨g, hg⟩ := (MulAction.isMultiplyPretransitive_iff.mp m23_isFourPretransitive) a b
  exact ⟨g, congrArg (fun z : Fin 4 ↪ Fin 23 => z 0) hg,
    congrArg (fun z : Fin 4 ↪ Fin 23 => z 1) hg,
    congrArg (fun z : Fin 4 ↪ Fin 23 => z 2) hg,
    congrArg (fun z : Fin 4 ↪ Fin 23 => z 3) hg⟩

/-- Inside the pair stabilizer, the adjacent-pair stabilizer and Ix generate.
The adjacent-pair stabilizer is transitive on the twenty remaining points;
Ix supplies a move out of the fixed third point and exchanges the deleted pair. -/
theorem pairStabilizer_generated :
    (pairStabilizer ⊓ MulAction.stabilizer M23 y.val) ⊔ fourPairStabilizer = pairStabilizer := by
  let J := (pairStabilizer ⊓ MulAction.stabilizer M23 y.val) ⊔ fourPairStabilizer
  obtain ⟨t, ht⟩ := localSwap ⟨5, by decide⟩ ⟨4, by decide⟩
  have ht5 : (t : M23) • (5 : Fin 23) = 4 := ht ⟨5, by decide⟩
  have ht11 : (t : M23) • (11 : Fin 23) = 11 := ht ⟨11, by decide⟩
  have ht17 : (t : M23) • (17 : Fin 23) = 17 := ht ⟨17, by decide⟩
  have htJ : (t : M23) ∈ J := Subgroup.mem_sup_right ⟨t.property, by
    change (t : M23) • ({11, 17} : Finset (Fin 23)) = {11, 17}
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, ht11, ht17]⟩
  have moves (c : Fin 23) (hc11 : c ≠ 11) (hc17 : c ≠ 17) :
      ∃ g ∈ J, g • (11 : Fin 23) = 11 ∧ g • (17 : Fin 23) = 17 ∧ g • (5 : Fin 23) = c := by
    by_cases hc5 : c = 5
    · exact ⟨1, J.one_mem, by simp, by simp, by simp [hc5]⟩
    obtain ⟨k, hk11, hk17, hk5, hk4⟩ := moveFourth c hc11 hc17 hc5
    have hkJ : k ∈ J := Subgroup.mem_sup_left ⟨by
      change k • ({11, 17} : Finset (Fin 23)) = {11, 17}
      simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, hk11, hk17], by
      change k • ({5, 11} : Finset (Fin 23)) = {5, 11}
      simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, hk5, hk11]⟩
    exact ⟨k * t, J.mul_mem hkJ htJ,
      by rw [mul_smul, ht11, hk11], by rw [mul_smul, ht17, hk17],
      by rw [mul_smul, ht5, hk4]⟩
  obtain ⟨r, hr⟩ := localSwap ⟨11, by decide⟩ ⟨17, by decide⟩
  have hr11 : (r : M23) • (11 : Fin 23) = 17 := hr ⟨11, by decide⟩
  have hr17 : (r : M23) • (17 : Fin 23) = 11 := hr ⟨17, by decide⟩
  have hr5 : (r : M23) • (5 : Fin 23) = 5 := hr ⟨5, by decide⟩
  have hrJ : (r : M23) ∈ J := Subgroup.mem_sup_right ⟨r.property, by
    change (r : M23) • ({11, 17} : Finset (Fin 23)) = {11, 17}
    simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, hr11, hr17]
    exact Finset.pair_comm _ _⟩
  have hJ : J ≤ pairStabilizer := sup_le inf_le_left inf_le_right
  apply le_antisymm hJ
  intro g hg
  have hset : g • x.val = x.val := hg
  have hgc : g • (5 : Fin 23) ∉ x.val := by
    intro hm
    rw [← hset] at hm
    have : (5 : Fin 23) ∈ x.val := (Finset.smul_mem_smul_finset_iff g).mp hm
    exact (by decide : (5 : Fin 23) ∉ x.val) this
  have hc11 : g • (5 : Fin 23) ≠ 11 := fun h => hgc (by simp [h, x, label])
  have hc17 : g • (5 : Fin 23) ≠ 17 := fun h => hgc (by simp [h, x, label])
  obtain ⟨k, hk, hk11, hk17, hk5⟩ := moves (g • 5) hc11 hc17
  have h11 : g • (11 : Fin 23) = 11 ∨ g • (11 : Fin 23) = 17 := by
    have hm : g • (11 : Fin 23) ∈ x.val := by
      rw [← hset]
      exact Finset.smul_mem_smul_finset (by decide)
    change g • (11 : Fin 23) ∈ ({11, 17} : Finset (Fin 23)) at hm
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hex : ∃ k ∈ J, k • y.val = g • y.val := by
    rcases h11 with h11 | h11
    · exact ⟨k, hk, by
        change k • ({5, 11} : Finset (Fin 23)) = g • ({5, 11} : Finset (Fin 23))
        simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, hk5, hk11, h11]⟩
    · exact ⟨k * r, J.mul_mem hk hrJ, by
        change (k * r : M23) • ({5, 11} : Finset (Fin 23)) = g • ({5, 11} : Finset (Fin 23))
        simp only [Finset.smul_finset_insert, Finset.smul_finset_singleton, mul_smul,
          hr5, hr11, hk5, hk17, h11]⟩
  obtain ⟨k, hk, hky⟩ := hex
  have hkg : k⁻¹ * g ∈ pairStabilizer ⊓ MulAction.stabilizer M23 y.val :=
    ⟨pairStabilizer.mul_mem (pairStabilizer.inv_mem (hJ hk)) hg, by
      change (k⁻¹ * g) • y.val = y.val
      rw [mul_smul, ← hky, inv_smul_smul]⟩
  simpa only [mul_inv_cancel_left] using J.mul_mem hk (Subgroup.mem_sup_left hkg)


open Theory.GroupTheory.GraphUniquenessSystem

/-- The setwise edge stabilizer agrees with the finset convention used by the
heptad calculation; it allows the two vertices to be exchanged. -/
theorem pairGraph_edgeStabilizer : edgeStabilizer M23 x y =
    MulAction.stabilizer M23 ({x.val, y.val} : Finset (Finset (Fin 23))) := by
  ext g
  change ((g • x = x ∧ g • y = y) ∨ (g • x = y ∧ g • y = x)) ↔
    g • ({x.val, y.val} : Finset (Finset (Fin 23))) = {x.val, y.val}
  rw [Finset.smul_finset_insert, Finset.smul_finset_singleton]
  rw [← Finset.coe_inj]
  simp only [Finset.coe_pair, Set.pair_eq_pair_iff, Subtype.ext_iff, smul_vertex_val]

/-- The concrete M23 uniqueness system of Aschbacher--Smith §5.2.
All three source generation conditions are theorems about the actual groups. -/
noncomputable def standardSystem : System M23 (Vertex (Fin 23)) where
  graph := graph (Fin 23)
  H := fourStabilizer
  x := x
  y := y
  adjacent := x_adj_y
  preserves := smul_adj
  faithful := pairGraph_faithful
  vertex_transitive := pairGraph_vertex_transitive
  edge_transitive := by
    intro a b hab
    obtain ⟨g, hg⟩ := pairGraph_edge_transitive a b hab
    exact ⟨g, Or.inl hg⟩
  local_orbit := by
    obtain ⟨g, hg, _⟩ := fourStabilizer_exists_swap
    exact ⟨g, hg⟩
  generate := by rw [pairGraph_stabilizer]; exact four_pair_generate
  vertex_generate := by
    simp only [edgeFixer, pairGraph_stabilizer]
    exact pairStabilizer_generated
  local_generate := by
    rw [pairGraph_edgeStabilizer, pairGraph_stabilizer, sup_comm]
    exact fourStabilizer_generated

private theorem local_subset (g : fourStabilizer) {v : Vertex (Fin 23)}
    (hv : v.val ⊆ lambda) : ((g : M23) • v).val ⊆ lambda := by
  change (g : M23) • v.val ⊆ lambda
  rw [← show (g : M23) • lambda = lambda from g.property]
  exact Finset.smul_finset_subset_smul_finset_iff.mpr hv


/-- The local vertex orbit consists exactly of the six pairs from Λ. -/
theorem standardSystem_local_vertex_orbit (v : Vertex (Fin 23)) :
    (∃ g : fourStabilizer, (g : M23) • x = v) ↔ v.val ⊆ lambda := by
  constructor
  · rintro ⟨g, rfl⟩
    exact local_subset g x_subset_lambda
  · intro hv
    obtain ⟨a, b, hab, hv'⟩ := Finset.card_eq_two.mp v.property
    obtain ⟨c, hc, hcv⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := v.val) (t := lambda) (by rw [v.property, lambda_card]; decide)
    have hbc : b ≠ c := by intro h; exact hcv (by simp [hv', ← h])
    let w := pair b c hbc
    have hadj : (graph (Fin 23)).Adj v w := by
      refine ⟨?_, b, ?_⟩
      · intro h
        exact hcv (by rw [h]; simp [w, pair])
      · simp [hv', w, pair]
    have hw : w.val ⊆ lambda := by
      intro z hz
      have hb : b ∈ lambda := hv (by simp [hv'])
      simp only [w, pair, Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hb
      · exact hc
    obtain ⟨g, hg, _⟩ := fourStabilizer_edge_transitive v w hadj hv hw
    exact ⟨g, hg⟩

/-- The source's local edge orbit is precisely the induced pair graph on Λ. -/
theorem standardSystem_localEdge_iff (v w : Vertex (Fin 23)) :
    standardSystem.localEdge v w ↔ (graph (Fin 23)).Adj v w ∧
      v.val ⊆ lambda ∧ w.val ⊆ lambda := by
  constructor
  · rintro ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨smul_adj (g : M23) x_adj_y,
        local_subset g x_subset_lambda, local_subset g y_subset_lambda⟩
    · exact ⟨(smul_adj (g : M23) x_adj_y).symm,
        local_subset g y_subset_lambda, local_subset g x_subset_lambda⟩
  · rintro ⟨hvw, hv, hw⟩
    obtain ⟨g, hg⟩ := fourStabilizer_edge_transitive v w hvw hv hw
    exact ⟨g, Or.inl hg⟩

/-- The induced four-point graph is a base in the actual closed-walk sense. -/
theorem standardSystem_isBase : standardSystem.IsBase := by
  let := m23_isFourPretransitive
  exact standardSystem.isBase_of_pairGraph_fourSubset rfl lambda lambda_card
    standardSystem_localEdge_iff

/-- The vertex subgroup used by a similarity is the original pair stabilizer. -/
theorem standardSystem_vertexGroup : standardSystem.vertexGroup = pairStabilizer :=
  pairGraph_stabilizer x

/-- The edge subgroup used by a similarity is the adjacent-pair intersection. -/
theorem standardSystem_edgeGroup : standardSystem.edgeGroup =
    pairStabilizer ⊓ MulAction.stabilizer M23 y.val := by
  change MulAction.stabilizer M23 x ⊓ MulAction.stabilizer M23 y = _
  rw [pairGraph_stabilizer, pairGraph_stabilizer]

/-- The local vertex intersection is the subgroup Ix of the heptad calculation. -/
theorem standardSystem_local_vertex :
    standardSystem.H ⊓ standardSystem.vertexGroup = fourPairStabilizer := by
  rw [standardSystem_vertexGroup]
  rfl

/-- The local pointwise edge intersection is UB. -/
theorem standardSystem_local_edgeFixer : standardSystem.H ⊓ standardSystem.edgeGroup =
    heptadKernelAmbient ⊔ heptadThreeSubgroup := by
  rw [standardSystem_edgeGroup, ← fourTwoPairStabilizer_eq_binary_three]
  exact (inf_assoc _ _ _).symm

/-- The local setwise edge intersection is the source I({x,y}). -/
theorem standardSystem_local_edgeStabilizer :
    standardSystem.H ⊓ standardSystem.edgeSetGroup = fourEdgeStabilizer := by
  change fourStabilizer ⊓ edgeStabilizer M23 x y = _
  rw [pairGraph_edgeStabilizer]
  rfl

/-- Field-plane coordinates for the vertex group of the actual uniqueness system. -/
noncomputable def standardSystemVertexEquiv :
    standardSystem.vertexGroup ≃* Matrix.PSL3Four.FieldExtension :=
  (MulEquiv.subgroupCongr standardSystem_vertexGroup).trans PairPlane.pairEquiv

/-- The system's edge group is the point parabolic in the linear PSL subgroup. -/
noncomputable def standardSystemEdgeEquiv :
    standardSystem.edgeGroup ≃* PairPlane.pointParabolic :=
  (MulEquiv.subgroupCongr standardSystem_edgeGroup).trans PairPlane.adjacentEquiv

/-- The vertex coordinates preserve the original inclusion in M23. -/
theorem standardSystemVertexEquiv_coe (g : standardSystem.vertexGroup) :
    PairPlane.fieldExtensionToM23 (standardSystemVertexEquiv g) = g.val := by
  change (PairPlane.pairEquiv.symm (PairPlane.pairEquiv _)).val = g.val
  rw [PairPlane.pairEquiv.symm_apply_apply]
  exact MulEquiv.subgroupCongr_apply _ _

/-- The edge coordinates preserve the same ambient inclusion. -/
theorem standardSystemEdgeEquiv_coe (g : standardSystem.edgeGroup) :
    PairPlane.pslToM23 (standardSystemEdgeEquiv g).val = g.val :=
  PairPlane.adjacentEquiv_coe _

/-- Restriction of the vertex identification is precisely the edge identification
followed by the canonical inclusion of PSL in its field extension. -/
theorem standardSystemVertexEquiv_edge (g : standardSystem.edgeGroup) :
    standardSystemVertexEquiv ⟨g.val, g.property.1⟩ =
      Matrix.PSL3Four.linearInclusion (standardSystemEdgeEquiv g).val := by
  apply PairPlane.fieldExtensionToM23_injective
  rw [standardSystemVertexEquiv_coe, PairPlane.fieldExtensionToM23_linear,
    standardSystemEdgeEquiv_coe]

end Sporadic.Mathieu.M23Geometry
