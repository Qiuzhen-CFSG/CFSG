module

public import Theory.SpecificGroups.LeechRelated.HSRecognition.Uniqueness.Suborbits
public import Theory.GroupAction.MarkedOrbit
public import Theory.Combinatorics.GraphAutomorphismTransport
public import Theory.GroupAction.SwappedOrbital.Connected
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# The graph forced by the degree-100 rank-three action

Adjacency means that the suborbit has length 22. Paired suborbits have equal
cardinality, and the three different subdegrees therefore make both orbitals
self-paired. The resulting graph is invariant under the original faithful
action. Primitivity makes it connected, and rank three makes it strongly
regular.

The parameters are determined without identifying the local M₂₂ actions:
77μ = 22(21−λ), and cyclic rotation of ordered triangles shows that
3 divides 100·22·λ. Together with μ > 0 these give λ = 0 and μ = 6.

Source: Wales, "Uniqueness of the graph of a rank three group", Pacific
J. Math. 30 (1969), pp.271--274. The final graph reconstruction and comparison
with the specified HS carrier are separate from this geometric reduction.
-/

@[expose] public section
open MulAction
open scoped BigOperators
namespace Sporadic.LeechRelated.HS
attribute [local instance] Classical.propDecidable

private theorem paired_card {G X : Type*} [Group G] [MulAction G X]
    [Finite G] [Finite X] [IsPretransitive G X] (a b : X) :
    Nat.card (orbit (stabilizer G a) b) = Nat.card (orbit (stabilizer G b) a) := by
  let e : stabilizer (stabilizer G a) b ≃ stabilizer (stabilizer G b) a := {
    toFun := fun g => ⟨⟨g.val.val, g.property⟩, g.val.property⟩
    invFun := fun g => ⟨⟨g.val.val, g.property⟩, g.val.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hp := Nat.card_congr e
  have ha := Nat.card_congr (orbitProdStabilizerEquivGroup (stabilizer G a) b)
  have hb := Nat.card_congr (orbitProdStabilizerEquivGroup (stabilizer G b) a)
  rw [Nat.card_prod] at ha hb
  obtain ⟨g, hg⟩ := exists_smul_eq G a b
  have hs := Nat.card_congr (stabilizerEquivStabilizer hg.symm).toEquiv
  have hd : 0 < Nat.card (stabilizer (stabilizer G b) a) := Nat.card_pos
  rw [hp] at ha
  exact Nat.eq_of_mul_eq_mul_right hd (ha.trans (hs.trans hb.symm))

/-- Both nontrivial suborbits are self-paired. -/
theorem RankThreeData.exists_swap {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) (b : Fin 100) : ∃ t : P, t • (0 : Fin 100) = b ∧ t • b = 0 := by
  let := h.transitive
  obtain ⟨g, hg⟩ := exists_smul_eq P (0 : Fin 100) b
  have hc : Nat.card (orbit (stabilizer P (0 : Fin 100)) (g⁻¹ • (0 : Fin 100))) =
      Nat.card (orbit (stabilizer P (0 : Fin 100)) b) := by
    have hh := suborbit_card_smul g (0 : Fin 100) (g⁻¹ • (0 : Fin 100))
    rw [hg, smul_inv_smul] at hh
    exact hh.symm.trans (paired_card (G := P) b 0)
  have he := h.suborbit_eq_of_card_eq hc
  have hm : g⁻¹ • (0 : Fin 100) ∈ orbit (stabilizer P (0 : Fin 100)) b := by
    rw [← he]
    exact mem_orbit_self _
  obtain ⟨k, hk⟩ := hm
  refine ⟨g * k.val, ?_, ?_⟩
  · rw [mul_smul, k.property, hg]
  · rw [mul_smul, show k.val • b = g⁻¹ • (0 : Fin 100) from hk, smul_inv_smul]

/-- Adjacency on the original points is the suborbit of length 22. -/
noncomputable def RankThreeData.graph {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : SimpleGraph (Fin 100) where
  Adj x y := Nat.card (orbit (stabilizer P x) y) = 22
  symm := ⟨by
    let := h.transitive
    intro x y hxy
    exact (paired_card (G := P) y x).trans hxy⟩
  loopless := ⟨by
    intro x hx
    have ho : orbit (stabilizer P x) x = {x} := by
      ext y
      constructor
      · rintro ⟨g, rfl⟩
        exact g.property
      · rintro rfl
        exact mem_orbit_self _
    rw [ho] at hx
    simp at hx⟩

/-- The original permutation action preserves the canonical graph. -/
theorem RankThreeData.graph_invariant {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) (g : P) (x y : Fin 100) :
    h.graph.Adj (g • x) (g • y) ↔ h.graph.Adj x y := by
  exact (congrArg (fun n : ℕ => n = 22) (suborbit_card_smul g x y)).to_iff

private theorem RankThreeData.graph_eq_swapped {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) (b : Fin 100)
    (hb : Nat.card (orbit (stabilizer P (0 : Fin 100)) b) = 22)
    (h0b : (0 : Fin 100) ≠ b) (t : P) (ht0 : t • (0 : Fin 100) = b) (htb : t • b = 0) :
    h.graph = SwappedOrbital.graph 0 b h0b t ht0 htb := by
  let := h.transitive
  ext x y
  obtain ⟨g, rfl⟩ := exists_smul_eq P (0 : Fin 100) x
  have hy : y = g • (g⁻¹ • y) := (smul_inv_smul g y).symm
  rw [hy, h.graph_invariant, SwappedOrbital.adj_smul_iff, SwappedOrbital.adj_base]
  change Nat.card (orbit (stabilizer P (0 : Fin 100)) (g⁻¹ • y)) = 22 ↔
    g⁻¹ • y ∈ orbit (stabilizer P (0 : Fin 100)) b
  constructor
  · intro hc
    rw [← h.suborbit_eq_of_card_eq (hc.trans hb.symm)]
    exact mem_orbit_self _
  · intro hm
    rw [orbit_eq_iff.mpr hm]
    exact hb


/-- Primitivity forces the nontrivial orbital graph to be connected. -/
theorem RankThreeData.graph_connected {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : h.graph.Connected := by
  let := h.primitive
  obtain ⟨b, c, h0b, hb, _, _⟩ := h.suborbits
  have hne : (0 : Fin 100) ≠ b := by
    intro he
    subst b
    exact h0b (mem_orbit_self _)
  obtain ⟨t, ht0, htb⟩ := h.exists_swap b
  rw [h.graph_eq_swapped b hb hne t ht0 htb]
  exact SwappedOrbital.connected 0 b hne t ht0 htb

private theorem RankThreeData.graph_parameters_exist {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) :
    ∃ l m : ℕ, h.graph.IsSRGWith 100 22 l m ∧ 0 < m := by
  classical
  let := h.transitive
  obtain ⟨b, c, h0b, hb, _, hcover⟩ := h.suborbits
  have hne : (0 : Fin 100) ≠ b := by
    intro he
    subst b
    exact h0b (mem_orbit_self _)
  obtain ⟨t, ht0, htb⟩ := h.exists_swap b
  let Γ := SwappedOrbital.graph 0 b hne t ht0 htb
  have hΓ : h.graph = Γ := h.graph_eq_swapped b hb hne t ht0 htb
  have hs : Γ.IsSRGWith 100 22 (Nat.card (Γ.commonNeighbors 0 b))
      (Nat.card (Γ.commonNeighbors 0 c)) := by
    simpa only [Nat.card_fin, hb] using
      SwappedOrbital.stronglyRegular 0 b hne t ht0 htb c hcover
  have hc : c ≠ 0 ∧ c ∉ orbit (stabilizer P (0 : Fin 100)) b := by
    have hh := mem_orbit_self (M := stabilizer P (0 : Fin 100)) c
    rw [hcover] at hh
    exact not_or.mp hh
  have hna : ¬Γ.Adj 0 c := by
    rw [SwappedOrbital.adj_base]
    exact hc.2
  have hconn : Γ.Connected := hΓ ▸ h.graph_connected
  rw [hΓ]
  exact ⟨_, _, hs, hs.mu_pos_of_connected Γ hconn hc.1.symm hna⟩

/-- The literal permutation group acts by graph automorphisms. -/
noncomputable def RankThreeData.graphAction {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : P →* (h.graph ≃g h.graph) :=
  Theory.Combinatorics.graphActionHom P.subtype h.graph_invariant

/-- Passing to graph automorphisms preserves faithfulness. -/
theorem RankThreeData.graphAction_injective {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : Function.Injective h.graphAction :=
  Theory.Combinatorics.graphActionHom_injective P.subtype h.graph_invariant Subtype.val_injective

private theorem triangle_divisibility {V : Type*} [Fintype V]
    (Γ : SimpleGraph V) [DecidableRel Γ.Adj] {n k l m : ℕ}
    (h : Γ.IsSRGWith n k l m) : 3 ∣ n * k * l := by
  classical
  let T := (a : V) × (b : Γ.neighborSet a) × Γ.commonNeighbors a b
  let r : Equiv.Perm T := {
    toFun := fun t => ⟨t.2.1.val, ⟨⟨t.2.2.val, t.2.2.property.2⟩,
      ⟨t.1, ⟨t.2.1.property.symm, t.2.2.property.1.symm⟩⟩⟩⟩
    invFun := fun t => ⟨t.2.2.val, ⟨⟨t.1, t.2.2.property.1.symm⟩,
      ⟨t.2.1.val, ⟨t.2.2.property.2.symm, t.2.1.property⟩⟩⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have hr : r ^ 3 ^ 1 = 1 := by
    apply Equiv.ext
    intro t
    rfl
  have hcount : Fintype.card T = n * k * l := by
    change Fintype.card ((a : V) × (b : Γ.neighborSet a) × Γ.commonNeighbors a b) = _
    simp only [Fintype.card_sigma]
    have hlocal (a : V) (b : Γ.neighborSet a) :
        Fintype.card (Γ.commonNeighbors a b) = l := h.of_adj a b b.property
    simp_rw [hlocal, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      Γ.card_neighborSet_eq_degree]
    have hdegree (a : V) : Γ.degree a = k := h.regular a
    simp_rw [hdegree]
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [← h.card]
    exact (Nat.mul_assoc _ _ _).symm
  rw [← hcount]
  by_contra hd
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨t, ht⟩ := Equiv.Perm.exists_fixed_point_of_prime hd hr
  have he : t.2.1.val = t.1 := congrArg Sigma.fst ht
  exact t.2.1.property.ne he.symm

private theorem parameters_100_22 {Γ : SimpleGraph (Fin 100)} [DecidableRel Γ.Adj]
    {l m : ℕ} (h : Γ.IsSRGWith 100 22 l m) (hm : 0 < m) : l = 0 ∧ m = 6 := by
  have he := h.param_eq Γ (by decide)
  have ht := triangle_divisibility Γ h
  norm_num at he ht
  omega

/-- The rank-three data force the exact Higman--Sims graph parameters. -/
theorem RankThreeData.graph_stronglyRegular {P : Subgroup (Equiv.Perm (Fin 100))}
    (h : RankThreeData P) : h.graph.IsSRGWith 100 22 0 6 := by
  obtain ⟨l, m, hs, hm⟩ := h.graph_parameters_exist
  obtain ⟨rfl, rfl⟩ := parameters_100_22 hs hm
  exact hs

end Sporadic.LeechRelated.HS

