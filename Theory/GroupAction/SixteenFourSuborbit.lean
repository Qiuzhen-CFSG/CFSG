module
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Set.Card

/-!
# A five-element orbit from four-element suborbits

Let a finite group M act by automorphisms on a group V of order sixteen,
and let U have order eight. Suppose z lies in U, a subgroup A of M fixes z,
and every A-orbit outside U has four elements. If the M-orbit of z meets U
only at z and contains a point different from z, then it has five elements.
No elementary abelian or involution hypothesis is needed.

The orbit lies in {z} together with the eight points outside U. A point
moved from z contributes a four-element A-orbit disjoint from z. Any
further point contributes another disjoint four-element orbit, forcing
nine points in total. In that case the complement is U minus {z}, and is
M-invariant. Choose a in U different from both 1 and z. Both a and a⁻¹z
lie in that complement, so every m sends their product z into U. The
intersection hypothesis then forces m to fix z, a contradiction.

This is the elementary orbit argument in David Parrott, *A characterization
of the Tits' simple group* (1972), Lemma 3, p.675. Its recognition consumer
must establish all displayed hypotheses for the actual normalizer action.
-/

open Subgroup MulAction

/-- Four-element suborbits and the order-eight intersection force an orbit of length five. -/
public theorem card_orbit_five_of_card_sixteen_and_four_suborbits
    {V M : Type*} [Group V] [Finite V] [Group M] [Finite M]
    [MulDistribMulAction M V]
    (hV : Nat.card V = 16) (U : Subgroup V) (hU : Nat.card U = 8)
    (z : V) (hz : z ∈ U) (A : Subgroup M)
    (hAz : ∀ a : A, a • z = z)
    (hfour : ∀ v : V, v ∉ U → Nat.card (orbit A v) = 4)
    (hinter : ∀ v : V, v ∈ orbit M z → v ∈ U → v = z)
    (hmove : ∃ m : M, m • z ≠ z) : Nat.card (orbit M z) = 5 := by
  classical
  let O := orbit M z
  let Q : Set V := insert z (U : Set V)ᶜ
  have hUncard : (U : Set V).ncard = 8 := hU
  have hQcard : Q.ncard = 9 := by
    rw [Set.ncard_insert_of_notMem (by simpa using hz), Set.ncard_compl, hUncard, hV]
  have hOQ : O ⊆ Q := by
    intro v hv
    by_cases hvU : v ∈ U
    · exact Or.inl (hinter v hv hvU)
    · exact Or.inr hvU
  have hupper : O.ncard ≤ 9 := (Set.ncard_le_ncard hOQ).trans_eq hQcard
  obtain ⟨m, hm⟩ := hmove
  have hz1 : z ≠ 1 := by
    intro hz1
    apply hm
    rw [hz1, smul_one]
  have hnot9 : O.ncard ≠ 9 := by
    intro h9
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
  let x := m • z
  have hxO : x ∈ O := mem_orbit z m
  have hxU : x ∉ U := fun hx => hm (hinter x hxO hx)
  have hAxO : orbit A x ⊆ O := by
    exact (orbit_subgroup_subset A x).trans (orbit_eq_iff.mpr hxO).subset
  let B := insert z (orbit A x)
  have hBcard : B.ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (hznot hm)]
    change Nat.card (orbit A x) + 1 = 5
    rw [hfour x hxU]
  have hBO : B ⊆ O := by
    intro v hv
    rcases hv with hv | hv
    · simpa only [hv] using mem_orbit_self (M := M) z
    · exact hAxO hv
  change O.ncard = 5
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
  have hlarge : 9 ≤ O.ncard := by
    have hh := Set.ncard_le_ncard (Set.union_subset hBO hAyO)
    rw [Set.ncard_union_eq hdisj, hBcard] at hh
    change 5 + Nat.card (orbit A y) ≤ O.ncard at hh
    simpa only [hfour y hyU] using hh
  exact (hnot9 (by omega)).elim
