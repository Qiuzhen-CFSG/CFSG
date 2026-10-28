module
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Centralization from a coprime fixed layer

A finite solvable subgroup normalized by a finite coprime actor is the
product of its commutator subgroup and fixed subgroup, even when the ambient
group is infinite. The three-subgroup lemma then tests centralization on
these two factors: fixed displacements and commuting actor actions force
the commutator factor to centralize as well.

This is the coprime decomposition used in DGS, *Groups and Graphs* (1985),
Chapters 8–9, in the torus action on an adjacent Sylow omega quotient.
-/

namespace Subgroup
variable {G : Type*} [Group G]

public theorem eq_commutator_sup_centralizer_of_finite_solvable_coprime (V D : Subgroup G) [Finite V] [Finite D]
    (hn : D ≤ normalizer (V : Set G)) (hs : Group.IsSolvable V)
    (hc : Nat.Coprime (Nat.card D) (Nat.card V)) :
    V = ⁅V,D⁆ ⊔ (V ⊓ centralizer (D : Set G)) := by
  let _ : Normalizes D V := ⟨hn⟩
  have he := fixedPointSubgroup_sup_commutatorAction_eq_top_of_solvable_coprime
    (G := V) (A := D) hs hc
  have hm := congrArg (fun U : Subgroup V => U.map V.subtype) he
  rw [Subgroup.map_sup, commutatorAction_subgroup_conj_map_eq_commutator V D hn,
    fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn V D hn,
    map_subgroupOf_eq_of_le (show subgroupCentralizerIn V D ≤ V from inf_le_left),
    ← MonoidHom.range_eq_map, range_subtype, sup_comm] at hm
  exact hm.symm

public theorem le_centralizer_of_coprime_fixed_layer
    (V D X : Subgroup G) [Finite V] [Finite D]
    (hn : D ≤ normalizer (V : Set G)) (hs : Group.IsSolvable V)
    (hc : Nat.Coprime (Nat.card D) (Nat.card V))
    (hdisp : ⁅V,X⁆ ≤ centralizer (D : Set G))
    (hfix : V ⊓ centralizer (D : Set G) ≤ centralizer (X : Set G))
    (hcomm : ⁅X,D⁆ ≤ centralizer (V : Set G)) :
    V ≤ centralizer (X : Set G) := by
  have h1 : ⁅⁅V,X⁆,D⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hdisp
  have h2 : ⁅⁅X,D⁆,V⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr hcomm
  have h3 := commutator_commutator_eq_bot_of_rotate h1 h2
  rw [commutator_comm D V] at h3
  rw [eq_commutator_sup_centralizer_of_finite_solvable_coprime V D hn hs hc]
  exact sup_le (commutator_eq_bot_iff_le_centralizer.mp h3) hfix

end Subgroup
