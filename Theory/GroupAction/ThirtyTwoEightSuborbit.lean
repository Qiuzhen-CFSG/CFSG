module
public import Theory.GroupAction.BinaryCoatomOrbit
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Set.Card

/-!
# A nine-element orbit from eight- or sixteen-element suborbits

Let a finite group M act by automorphisms on a group V of order thirty-two,
and let U have order sixteen. Suppose z belongs to U, a subgroup A of M
fixes z, and every A-orbit in M·z outside U has eight or sixteen elements. If
the M-orbit of z meets U only in z and is nontrivial, it has nine elements.

The orbit lies in {z} together with the sixteen points outside U. If it
filled this set, the invariant complement U minus {z} would force every
actor to send z back into U, contradicting the intersection condition.
This rules out seventeen without an automorphism-order calculation. Any
sixteen-element A-suborbit, or two distinct eight-element A-suborbits,
would force seventeen. Exactly one eight-element suborbit remains.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
the first paragraph of p.676. This strengthens its exclusion of seventeen
by using the index-two subgroup and its invariant complement directly.
-/

open Subgroup MulAction

/-- Eight- or sixteen-element suborbits and a half-sized subgroup force an orbit of length nine. -/
public theorem card_orbit_nine_of_card_thirtyTwo_and_eight_or_sixteen_suborbits
    {V M : Type*} [Group V] [Finite V] [Group M] [Finite M]
    [MulDistribMulAction M V]
    (hV : Nat.card V = 32) (U : Subgroup V) (hU : Nat.card U = 16)
    (z : V) (hz : z ∈ U) (A : Subgroup M)
    (hAz : ∀ a : A, a • z = z)
    (hsuborbit : ∀ v : V, v ∈ orbit M z → v ∉ U →
      Nat.card (orbit A v) = 8 ∨ Nat.card (orbit A v) = 16)
    (hinter : ∀ v : V, v ∈ orbit M z → v ∈ U → v = z)
    (hmove : ∃ m : M, m • z ≠ z) : Nat.card (orbit M z) = 9 := by
  classical
  let O := orbit M z
  let Q : Set V := insert z (U : Set V)ᶜ
  have hUncard : (U : Set V).ncard = 16 := hU
  have hQcard : Q.ncard = 17 := by
    rw [Set.ncard_insert_of_notMem (by simpa using hz), Set.ncard_compl, hUncard, hV]
  have hOQ : O ⊆ Q := by
    intro v hv
    by_cases hvU : v ∈ U
    · exact Or.inl (hinter v hv hvU)
    · exact Or.inr hvU
  have hupper : O.ncard ≤ 17 := (Set.ncard_le_ncard hOQ).trans_eq hQcard
  obtain ⟨m, hm⟩ := hmove
  have hz1 : z ≠ 1 := by
    intro hz1
    apply hm
    rw [hz1, smul_one]
  have hnot17 : O.ncard ≠ 17 := by
    intro h17
    have hOeq : O = Q := Set.eq_of_subset_of_ncard_le hOQ (by omega)
    have hout (v : V) (hv : v ∉ O) : v ∈ U := by
      by_contra hvU
      exact hv (hOeq ▸ Or.inr hvU)
    have hsmul (v : V) (hv : v ∉ O) : m • v ∉ O := by
      intro hmv
      have hh := mapsTo_smul_orbit m⁻¹ z hmv
      exact hv (by simpa only [inv_smul_smul] using hh)
    have hex : ∃ a : V, a ∈ U ∧ a ≠ 1 ∧ a ≠ z := by
      by_contra hnone
      have hsub : (U : Set V) ⊆ {1, z} := by
        intro a ha
        by_contra han
        exact hnone ⟨a, ha, (by simpa using han)⟩
      have hh := Set.ncard_le_ncard hsub
      rw [hUncard, Set.ncard_pair hz1.symm] at hh
      omega
    obtain ⟨a, ha, ha1, haz⟩ := hex
    have haO : a ∉ O := fun h => haz (hinter a h ha)
    have hbU : a⁻¹ * z ∈ U := U.mul_mem (U.inv_mem ha) hz
    have hbz : a⁻¹ * z ≠ z := by
      intro heq
      have hh : a⁻¹ = 1 := mul_right_cancel (heq.trans (one_mul z).symm)
      exact ha1 (inv_eq_one.mp hh)
    have hbO : a⁻¹ * z ∉ O := fun h => hbz (hinter _ h hbU)
    have hmz : m • z ∈ U := by
      have hh := U.mul_mem (hout _ (hsmul a haO)) (hout _ (hsmul _ hbO))
      simpa only [← smul_mul', mul_inv_cancel_left] using hh
    exact hm (hinter _ (mem_orbit z m) hmz)
  have hznot {v : V} (hv : v ≠ z) : z ∉ orbit A v := by
    rintro ⟨a, ha⟩
    change a • v = z at ha
    apply hv
    calc
      v = a⁻¹ • (a • v) := (inv_smul_smul a v).symm
      _ = a⁻¹ • z := by rw [ha]
      _ = z := hAz a⁻¹
  have height (v : V) (hvO : v ∈ O) (hvU : v ∉ U) : Nat.card (orbit A v) = 8 := by
    rcases hsuborbit v hvO hvU with h8 | h16
    · exact h8
    have hvz : v ≠ z := fun hv => hvU (hv ▸ hz)
    have hAvO : orbit A v ⊆ O :=
      (orbit_subgroup_subset A v).trans (orbit_eq_iff.mpr hvO).subset
    have hsub : insert z (orbit A v) ⊆ O := by
      intro w hw
      rcases hw with rfl | hw
      · exact mem_orbit_self _
      · exact hAvO hw
    have hlarge := Set.ncard_le_ncard hsub
    rw [Set.ncard_insert_of_notMem (hznot hvz)] at hlarge
    change Nat.card (orbit A v) + 1 ≤ O.ncard at hlarge
    rw [h16] at hlarge
    exact (hnot17 (by omega)).elim
  let x := m • z
  have hxO : x ∈ O := mem_orbit z m
  have hxU : x ∉ U := fun hx => hm (hinter x hxO hx)
  have hAxO : orbit A x ⊆ O := by
    exact (orbit_subgroup_subset A x).trans (orbit_eq_iff.mpr hxO).subset
  let B := insert z (orbit A x)
  have hBcard : B.ncard = 9 := by
    rw [Set.ncard_insert_of_notMem (hznot hm)]
    change Nat.card (orbit A x) + 1 = 9
    rw [height x hxO hxU]
  have hBO : B ⊆ O := by
    intro v hv
    rcases hv with hv | hv
    · simpa only [hv] using mem_orbit_self (M := M) z
    · exact hAxO hv
  change O.ncard = 9
  by_cases hOB : O = B
  · exact hOB ▸ hBcard
  have hnsub : ¬ O ⊆ B := fun h => hOB (Set.Subset.antisymm h hBO)
  obtain ⟨y, hyO, hyB⟩ := Set.not_subset.mp hnsub
  have hyz : y ≠ z := fun hy => hyB (Or.inl hy)
  have hyU : y ∉ U := fun hy => hyz (hinter y hyO hy)
  have hAyO : orbit A y ⊆ O := by
    exact (orbit_subgroup_subset A y).trans (orbit_eq_iff.mpr hyO).subset
  have hdisj : Disjoint B (orbit A y) := by
    apply Set.disjoint_left.mpr
    rintro v (rfl | hvx) hvy
    · exact hznot hyz hvy
    · have heq : orbit A y = orbit A x :=
        (orbit_eq_iff.mpr hvy).symm.trans (orbit_eq_iff.mpr hvx)
      exact hyB (Or.inr (heq ▸ mem_orbit_self y))
  have hlarge : 17 ≤ O.ncard := by
    have hh := Set.ncard_le_ncard (Set.union_subset hBO hAyO)
    rw [Set.ncard_union_eq hdisj, hBcard] at hh
    change 9 + Nat.card (orbit A y) ≤ O.ncard at hh
    simpa only [height y hyO hyU] using hh
  exact (hnot17 (by omega)).elim

/-- In binary rank five, weak closure in a half-sized subgroup and these suborbits
force every actor to fix the distinguished point. -/
public theorem smul_eq_of_binary_thirtyTwo_and_eight_or_sixteen_suborbits
    {V M : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    [Group M] [Finite M] [MulDistribMulAction M V]
    (hV : Nat.card V = 32) (U : Subgroup V) (hU : Nat.card U = 16)
    (z : V) (hz : z ∈ U) (A : Subgroup M)
    (hAz : ∀ a : A, a • z = z)
    (hsuborbit : ∀ v : V, v ∈ orbit M z → v ∉ U →
      Nat.card (orbit A v) = 8 ∨ Nat.card (orbit A v) = 16)
    (hinter : ∀ v : V, v ∈ orbit M z → v ∈ U → v = z) :
    ∀ m : M, m • z = z := by
  intro m
  by_contra hm
  have hcard := card_orbit_nine_of_card_thirtyTwo_and_eight_or_sixteen_suborbits
    hV U hU z hz A hAz hsuborbit hinter ⟨m, hm⟩
  exact not_card_orbit_nine_of_binary_thirtyTwo_and_half_subgroup hV U hU z hz hinter hcard
