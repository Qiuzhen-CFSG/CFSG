module

public import Theory.GroupTheory.ZStar.OddCentralizerIndex
public import Mathlib.GroupTheory.Sylow
public import Theory.GroupTheory.Involution.Basic

/-!
# From isolation to Sylow-local data

An isolated involution belongs to a Sylow 2-subgroup in which it is central
and weakly closed. The odd centralizer index theorem makes a Sylow 2-subgroup
of the centralizer a full Sylow subgroup of the ambient group. Choose that
subgroup to contain the given involution. Its centrality is then immediate,
and isolation forces every conjugate lying in it to equal the involution.

This ports `Submission/ZStar/LocalReduction.lean` at historical commit
`c3503435`, supplying the local input to the Z-star proof. The elementwise
weak-closure predicate and the small involution lemmas retain their historical
public names for later ported modules. The existing
`BenderSuzuki.PFAppendixIII.IsInvolution` definition is re-exported through its
own module rather than duplicated here. The two scalar involution hypotheses
in the reduction theorems express that same condition explicitly.
-/

namespace Glauberman.ZStar

/-- An element is weakly closed in a subgroup when it belongs to that subgroup
and no distinct conjugate of it belongs to the subgroup. -/
@[expose] public def IsWeaklyClosedInSylow {G : Type*} [Group G]
    (t : G) (S : Subgroup G) : Prop :=
  t ∈ S ∧ ∀ g : G, g * t * g⁻¹ ∈ S → g * t * g⁻¹ = t

/-- An element whose square is one is its own inverse. -/
public theorem inv_eq_self_of_sq_eq_one {G : Type*} [Group G] {t : G}
    (ht2 : t * t = 1) : t⁻¹ = t :=
  inv_eq_of_mul_eq_one_left ht2

/-- A nonidentity element whose square is one has order two. -/
public theorem orderOf_eq_two {G : Type*} [Group G] {t : G}
    (ht2 : t * t = 1) (ht1 : t ≠ 1) : orderOf t = 2 :=
  orderOf_eq_prime (by simpa [pow_two] using ht2) ht1

/-- An isolated involution lies in a Sylow 2-subgroup of its centralizer that
is also a Sylow 2-subgroup of the ambient group. -/
public theorem exists_sylow_le_centralizer
    {G : Type*} [Group G] [Finite G] (t : G) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ S : Sylow 2 G, t ∈ (S : Subgroup G) ∧
      (S : Subgroup G) ≤ Subgroup.centralizer {t} := by
  classical
  let C := Subgroup.centralizer ({t} : Set G)
  have htC : t ∈ C := by simp [C, Subgroup.mem_centralizer_singleton_iff]
  let tC : C := ⟨t, htC⟩
  have horder : orderOf tC = 2 := by
    rw [← Subgroup.orderOf_coe tC]
    exact orderOf_eq_two ht2 ht1
  have hcyclic : IsPGroup 2 (Subgroup.zpowers tC) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using horder
  obtain ⟨PC, hPC⟩ := hcyclic.exists_le_sylow
  let P := (PC : Subgroup C).map C.subtype
  have hP : IsPGroup 2 P := PC.isPGroup'.map C.subtype
  have hodd : Odd C.index := odd_index_of_centralizer ht2 ht1 hisolated
  have hCindex : ¬ 2 ∣ C.index := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hodd
  have hindex : ¬ 2 ∣ P.index := by
    change ¬ 2 ∣ ((PC : Subgroup C).map C.subtype).index
    rw [Subgroup.index_map_subtype]
    exact fun h => (Nat.prime_two.dvd_mul.mp h).elim PC.not_dvd_index hCindex
  let S := hP.toSylow hindex
  refine ⟨S, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨tC, hPC (Subgroup.mem_zpowers tC), rfl⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.property

/-- An isolated involution is central and weakly closed in a Sylow
2-subgroup containing it. -/
public theorem isolated_involution_local_data
    {G : Type*} [Group G] [Finite G] (t : G) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hisolated : ∀ g : G, (g * t * g⁻¹) * t = t * (g * t * g⁻¹) →
      g * t * g⁻¹ = t) :
    ∃ S : Sylow 2 G, t ∈ (S : Subgroup G) ∧
      (∀ s, s ∈ (S : Subgroup G) → s * t = t * s) ∧
      IsWeaklyClosedInSylow t (S : Subgroup G) := by
  obtain ⟨S, htS, hSC⟩ := exists_sylow_le_centralizer t ht2 ht1 hisolated
  have hcomm : ∀ s, s ∈ (S : Subgroup G) → s * t = t * s :=
    fun s hs => Subgroup.mem_centralizer_singleton_iff.mp (hSC hs)
  exact ⟨S, htS, hcomm, htS, fun g hg => hisolated g (hcomm _ hg)⟩

end Glauberman.ZStar
