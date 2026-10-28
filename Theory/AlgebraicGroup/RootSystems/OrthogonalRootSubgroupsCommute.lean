module

public import Theory.AlgebraicGroup.RootData.ChevalleyCommutator
public import Theory.AlgebraicGroup.RootSystems.Weyl

universe u

/-!
Commutation for root groups belonging to different orthogonal components.

Orthogonality of two individual roots is not sufficient in a general
irreducible root system: for example, the two short roots in `B₂` can have a
nonzero commutator term.  In an orthogonal decomposition, however, every root
in one part is orthogonal to every root in another part.  Pairing a proposed
positive integral cross-combination with the appropriate coroot (and using
the diagonal value `2`) rules out such a root and at the same time proves the
two input roots are linearly independent.  The Chevalley commutator API then
turns the empty term set into pointwise commutation.

This is the root-system input used by the root-block component construction;
the decomposition is the source's decomposition into irreducible orthogonal
components, while the commutator reduction follows the Chevalley relation of
GLS3, Theorem 1.12.1.
-/

namespace Theory.AlgebraicGroup

/-! A positive integral combination of roots from distinct orthogonal parts is
not itself a root. -/
public theorem root_not_positive_integral_combination_of_distinct_orthogonal_parts
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (d : P.OrthogonalDecomposition)
    {s t : Set ι} (hs : s ∈ d.parts) (ht : t ∈ d.parts) (hst : s ≠ t)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ t) :
    ∀ γ : ι, ∀ m n : ℕ, 0 < m → 0 < n →
      P.root γ ≠ (m : ℝ) • P.root i + (n : ℝ) • P.root j := by
  intro γ m n hm hn hroot
  obtain ⟨u, hu, hγ⟩ : ∃ u ∈ d.parts, γ ∈ u := by
    have hcover : γ ∈ ⋃₀ d.parts := by
      rw [d.cover]
      trivial
    exact Set.mem_sUnion.mp hcover
  by_cases hus : u = s
  · have hγs : γ ∈ s := hus ▸ hγ
    have hγj : P.IsOrthogonal γ j :=
      d.orthogonal s hs t ht hst γ hγs j hj
    have hij : P.IsOrthogonal i j :=
      d.orthogonal s hs t ht hst i hi j hj
    have hleft : P.pairing γ j = 0 := hγj.1
    have hij0 : P.pairing i j = 0 := hij.1
    have hpair : P.pairing j j = 2 := by
      rw [← P.root_coroot_eq_pairing]
      exact P.root_coroot_two j
    have heval := congrArg (fun x : M => P.toLinearMap x (P.coroot j)) hroot
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
      P.root_coroot_eq_pairing, smul_eq_mul] at heval
    rw [hleft, hij0, hpair] at heval
    have hmn : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  · by_cases hut : u = t
    · have hγt : γ ∈ t := hut ▸ hγ
      have hγi : P.IsOrthogonal γ i :=
        d.orthogonal t ht s hs (Ne.symm hst) γ hγt i hi
      have hji : P.IsOrthogonal j i :=
        d.orthogonal t ht s hs (Ne.symm hst) j hj i hi
      have hleft : P.pairing γ i = 0 := hγi.1
      have hji0 : P.pairing j i = 0 := hji.1
      have hpair : P.pairing i i = 2 := by
        rw [← P.root_coroot_eq_pairing]
        exact P.root_coroot_two i
      have heval := congrArg (fun x : M => P.toLinearMap x (P.coroot i)) hroot
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        P.root_coroot_eq_pairing, smul_eq_mul] at heval
      rw [hleft, hji0, hpair] at heval
      have hmm : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      linarith
    · have hγu : P.IsOrthogonal i γ :=
        d.orthogonal s hs u hu (by
          intro h
          exact hus h.symm) i hi γ hγ
      have hju : P.IsOrthogonal j γ :=
        d.orthogonal t ht u hu (by
          intro h
          exact hut h.symm) j hj γ hγ
      have hiγ : P.pairing i γ = 0 := hγu.1
      have hjγ : P.pairing j γ = 0 := hju.1
      have hpair : P.pairing γ γ = 2 := by
        rw [← P.root_coroot_eq_pairing]
        exact P.root_coroot_two γ
      have heval := congrArg (fun x : M => P.toLinearMap x (P.coroot γ)) hroot
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
        P.root_coroot_eq_pairing, smul_eq_mul] at heval
      rw [hpair, hiγ, hjγ] at heval
      norm_num at heval

/-! Roots in distinct orthogonal parts are linearly independent. -/
public theorem roots_linearIndependent_of_distinct_orthogonal_parts
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (d : P.OrthogonalDecomposition)
    {s t : Set ι} (hs : s ∈ d.parts) (ht : t ∈ d.parts) (hst : s ≠ t)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ t) :
    LinearIndependent ℝ ![P.root i, P.root j] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have heval_i := congrArg (fun x : M => P.toLinearMap x (P.coroot i)) hab
  have heval_j := congrArg (fun x : M => P.toLinearMap x (P.coroot j)) hab
  have hij : P.IsOrthogonal i j :=
    d.orthogonal s hs t ht hst i hi j hj
  have hji : P.IsOrthogonal j i :=
    d.orthogonal t ht s hs (Ne.symm hst) j hj i hi
  have hself_i : P.pairing i i = 2 := by
    rw [← P.root_coroot_eq_pairing]
    exact P.root_coroot_two i
  have hself_j : P.pairing j j = 2 := by
    rw [← P.root_coroot_eq_pairing]
    exact P.root_coroot_two j
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    P.root_coroot_eq_pairing, smul_eq_mul] at heval_i heval_j
  rw [hself_i, hji.1] at heval_i
  rw [hij.1, hself_j] at heval_j
  norm_num at heval_i heval_j
  exact ⟨heval_i, heval_j⟩

/-! Chevalley pointwise commutation for roots in distinct parts. -/
public theorem rootSubgroups_commute_of_distinct_orthogonal_parts
    {k : Type u} [Field k]
    {K : Variety k} [AlgebraicGroup K] {T : ClosedSubgroup K}
    (D : RootGroupData K T) (C : ChevalleyData K D)
    {ι M N : Type*} [Fintype ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced]
    (e : D.Root ≃ ι) (base : P.Base)
    (hC : IsChevalleySystem D C P e base)
    (d : P.OrthogonalDecomposition)
    (_hd : d.IsIrreducible)
    {s t : Set ι} (hs : s ∈ d.parts) (ht : t ∈ d.parts) (hst : s ≠ t)
    {α β : D.Root} (hα : e α ∈ s) (hβ : e β ∈ t) :
    ∀ x, x ∈ D.rootSubgroup α → ∀ y, y ∈ D.rootSubgroup β → Commute x y := by
  have hLI : AreLinearlyIndependentRoots D P e α β := by
    have hlin := roots_linearIndependent_of_distinct_orthogonal_parts
      P d hs ht hst hα hβ
    simpa [AreLinearlyIndependentRoots] using (LinearIndependent.pair_iff.mp hlin)
  have hEmpty : ChevalleyCommutatorRoots D P e α β = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro γ hγ
    obtain ⟨m, n, hm, hn, hroot⟩ :=
      (mem_chevalleyCommutatorRoots_iff D P e α β γ).mp hγ
    exact (root_not_positive_integral_combination_of_distinct_orthogonal_parts
      P d hs ht hst hα hβ (e γ) m n hm hn) hroot
  exact rootSubgroups_commute_of_chevalleyCommutatorRoots_eq_empty
    D C P e base hC hLI hEmpty

end Theory.AlgebraicGroup
