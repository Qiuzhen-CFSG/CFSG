module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.Invariant
public import Theory.GroupAction.Lemmas
public import Theory.GroupTheory.Commutator.ActionTriviality

/-!
# The `P × Q` lemma

This module proves the standard coprime `P × Q` action lemma in the form
needed by Stellmacher (1.6).  Let the finite elementary abelian `p`-group `V`
be acted on by an ambient finite group, and let commuting subgroups `P` and
`Q` have `P` a `p`-group and `p` coprime to `|Q|`.  If `Q` fixes `C_V(P)`
pointwise, then it fixes all of `V` pointwise.

The proof uses coprime action to split
`V = C_V(Q) × [V,Q]`.  Commutation makes `[V,Q]` invariant under `P`.  If
this commutator subgroup were nontrivial, orbit counting for the `p`-group
`P` would give a nonidentity `P`-fixed element in it.  The hypothesis makes
that element `Q`-fixed too, contradicting the direct complement.

Source: the standard `P × Q` lemma cited in the proof of Stellmacher (1.6),
`refs/latex/stellmacher-n-group.tex`, lines 446–447.
-/

open scoped Pointwise

universe u

private theorem commutatorAction_isInvariant_of_commuting_subgroups
    {G V : Type u} [Group G] [Group V] [MulDistribMulAction G V]
    (P Q : Subgroup G) (hPQ : ⁅P, Q⁆ = ⊥) :
    IsInvariant P V (commutatorAction Q V) := by
  have hcomm : P ≤ Subgroup.centralizer (Q : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hPQ
  have hpq (a : P) (q : Q) : (a : G) * (q : G) = (q : G) * (a : G) := by
    exact (Subgroup.mem_centralizer_iff.mp (hcomm a.property)
      (q : G) q.property).symm
  have hsmul (a : P) (q : Q) (v : V) : a • (q • v) = q • (a • v) := by
    change (a : G) • ((q : G) • v) = (q : G) • ((a : G) • v)
    rw [← mul_smul, ← mul_smul, hpq]
  have hforward : ∀ a : P, ∀ v : V,
      v ∈ commutatorAction Q V → a • v ∈ commutatorAction Q V := by
    intro a v hv
    rw [commutatorAction_eq_closure] at hv ⊢
    refine Subgroup.closure_induction
      (p := fun x _ => a • x ∈ Subgroup.closure
        {d : V | ∃ q : Q, ∃ v : V, d = v⁻¹ * q • v})
      (x := v) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨q, w, rfl⟩
      refine Subgroup.subset_closure ⟨q, a • w, ?_⟩
      simp only [smul_mul', smul_inv', hsmul]
    · simp
    · intro x y _ _ hx hy
      simpa [smul_mul'] using (Subgroup.closure
        {d : V | ∃ q : Q, ∃ v : V, d = v⁻¹ * q • v}).mul_mem hx hy
    · intro x _ hx
      simpa [smul_inv'] using (Subgroup.closure
        {d : V | ∃ q : Q, ∃ v : V, d = v⁻¹ * q • v}).inv_mem hx
  constructor
  intro a v
  constructor
  · exact hforward a v
  · intro hav
    have := hforward a⁻¹ (a • v) hav
    simpa [inv_smul_smul] using this

/-- **The `P × Q` lemma.**

Suppose commuting subgroups `P,Q ≤ G` act on a finite elementary abelian
`p`-group `V`, with `P` a `p`-group and `p` coprime to `|Q|`.  If `Q`
fixes every `P`-fixed vector, then `Q` fixes every vector. -/
public theorem p_times_q_lemma
    {p : ℕ} [Fact p.Prime]
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian p V] [MulDistribMulAction G V]
    (P Q : Subgroup G)
    (hP : IsPGroup p P) (hQ : Nat.Coprime p (Nat.card Q))
    (hPQ : ⁅P, Q⁆ = ⊥)
    (hfix : Q ≤ fixingSubgroup G (FixedPoints.subgroup P V : Set V)) :
    Q ≤ fixingSubgroup G (Set.univ : Set V) := by
  let C : Subgroup V := commutatorAction Q V
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup p V).exists_card_eq
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card V) := by
    rw [hn]
    exact hQ.symm.pow_right n
  have hcompl : IsCompl (FixedPoints.subgroup Q V) C := by
    exact isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := Q)
        (Group.isSolvable_of_comm (fun a b => IsMulCommutative.is_comm.comm a b))
        hcop (by infer_instance)
  have hCinv : IsInvariant P V C := by
    simpa [C] using commutatorAction_isInvariant_of_commuting_subgroups P Q hPQ
  let _ : IsInvariant P V C := hCinv
  have hCbot : C = ⊥ := by
    by_contra hCne
    have hCp : IsPGroup p C :=
      (IsElementaryAbelian.isPGroup p V).to_subgroup C
    have hCcard_ne_one : Nat.card C ≠ 1 := by
      intro hcard
      exact hCne ((Subgroup.card_eq_one (H := C)).1 hcard)
    have hpC : p ∣ Nat.card C :=
      hCp.card_eq_or_dvd.resolve_left hCcard_ne_one
    have hone : (1 : C) ∈ MulAction.fixedPoints P C := by
      simp [MulAction.mem_fixedPoints]
    obtain ⟨c, hcP, hcne⟩ :=
      hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (α := C) hpC hone
    have hcP' : (c : V) ∈ FixedPoints.subgroup P V := by
      rw [FixedPoints.mem_subgroup]
      intro a
      exact congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hcP) a)
    have hcQ : (c : V) ∈ FixedPoints.subgroup Q V := by
      rw [FixedPoints.mem_subgroup]
      intro q
      have hqfix : (q : G) ∈
          fixingSubgroup G (FixedPoints.subgroup P V : Set V) :=
        hfix q.property
      rw [mem_fixingSubgroup_iff] at hqfix
      have := hqfix (c : V) hcP'
      simpa only [Subgroup.smul_def] using this
    have hcinf : (c : V) ∈ FixedPoints.subgroup Q V ⊓ C :=
      ⟨hcQ, c.property⟩
    rw [hcompl.inf_eq_bot] at hcinf
    have hc_one : c = 1 := by
      apply Subtype.ext
      simpa using hcinf
    exact hcne hc_one.symm
  have htriv : ActsTrivially (A := Q) (G := V) :=
    actsTrivially_of_commutatorAction_eq_bot (by simpa [C] using hCbot)
  intro q hq
  rw [mem_fixingSubgroup_iff]
  intro v _hv
  simpa only [Subgroup.smul_def] using htriv ⟨q, hq⟩ v
