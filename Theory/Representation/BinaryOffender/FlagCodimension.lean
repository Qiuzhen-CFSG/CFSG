module

public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.BinaryOffender.IrreducibleExistence

/-!
# Fixed codimension along an invariant flag

The sum of the fixed codimensions on successive literal quotients of an
invariant flag is bounded by the fixed codimension on the whole module.
The proof iterates the submodule–quotient inequality; it does not split any
extension. In particular, two factors each costing three cannot occur when
the whole fixed codimension is at most five.
For a perfect actor, a flag with trivial factors has trivial total action.

This is the multiplicity argument used in Aschbacher–Smith, *The Classification
of Quasithin Groups*, 13.8.25, printed p.960 (1 March 2004 manuscript).
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- The denominator in a contained section contributes its actual codimension. -/
theorem fixedCodim_section_add_lower_le (L N : Subrepresentation ρ)
    (hLN : L ≤ N) (A : Subgroup G) :
    fixedCodim (sectionRepresentation ρ L N) A + fixedCodim L.toRepresentation A ≤
      fixedCodim N.toRepresentation A := by
  have he : fixedCodim (sectionLower ρ L N).toRepresentation A =
      fixedCodim L.toRepresentation A := by
    simpa only [Subgroup.map_id] using fixedCodim_map_equivariant
      (sectionLower ρ L N).toRepresentation L.toRepresentation (MonoidHom.id G)
      (sectionLowerEquiv ρ hLN) (fun _ _ => rfl) A
  have h := fixedCodim_quotient_add_subrepresentation_le N.toRepresentation
    (sectionLower ρ L N) A
  change fixedCodim (sectionRepresentation ρ L N) A + _ ≤ _ at h
  rwa [he] at h

/-- Telescoping along a flag, without a semisimplicity assumption. -/
theorem sum_fixedCodim_flag_le (c : ℕ → Subrepresentation ρ) (hc : Monotone c)
    (n : ℕ) (A : Subgroup G) :
    ∑ i ∈ Finset.range n, fixedCodim (sectionRepresentation ρ (c i) (c (i + 1))) A ≤
      fixedCodim ρ A := by
  have h (m : ℕ) :
      ∑ i ∈ Finset.range m, fixedCodim (sectionRepresentation ρ (c i) (c (i + 1))) A ≤
        fixedCodim (c m).toRepresentation A := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have := fixedCodim_section_add_lower_le ρ (c m) (c (m + 1))
        (hc (Nat.le_succ m)) A
      omega
  exact (h n).trans (fixedCodim_subrepresentation_le ρ (c n) A)

/-- Two distinct factors of a flag cannot both exceed half the total budget. -/
theorem eq_of_flag_fixedCodim_bounds (c : ℕ → Subrepresentation ρ) (hc : Monotone c)
    (n d : ℕ) (A : Subgroup G) (hbudget : fixedCodim ρ A < 2 * d)
    {i j : ℕ} (hi : i < n) (hj : j < n)
    (hdi : d ≤ fixedCodim (sectionRepresentation ρ (c i) (c (i + 1))) A)
    (hdj : d ≤ fixedCodim (sectionRepresentation ρ (c j) (c (j + 1))) A) : i = j := by
  classical
  by_contra hij
  have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range n := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_range.mpr hi
    · exact Finset.mem_range.mpr hj
  have hpair := Finset.sum_le_sum_of_subset
    (f := fun k => fixedCodim (sectionRepresentation ρ (c k) (c (k + 1))) A) hsub
  rw [Finset.sum_pair hij] at hpair
  have := sum_fixedCodim_flag_le ρ c hc n A
  omega

omit [FiniteDimensional (ZMod 2) V] in
/-- Perfectness collapses any finite flag of central factors. In particular,
a nontrivial perfect action must survive on at least one factor of every
exhaustive invariant flag. -/
theorem le_fixedSpace_of_central_flag (K : Subgroup G) [Group.IsPerfect K]
    (c : ℕ → Subrepresentation ρ) (hzero : c 0 = ⊥) (n : ℕ)
    (hc : ∀ i < n, ∀ k ∈ K, ∀ v,
      sectionRepresentation ρ (c i) (c (i + 1)) k v = v) :
    (c n).toSubmodule ≤ fixedSpace ρ K := by
  induction n with
  | zero =>
    rw [hzero]
    exact bot_le
  | succ n ih =>
    have hn := ih (fun i hi => hc i (Nat.lt_succ_of_lt hi))
    apply le_fixedSpace_of_commutator_le_fixedSpace ρ K (c (n + 1)).toSubmodule
      (le_subspaceStabilizer ρ _ (fun k _ v hv => (c (n + 1)).apply_mem_toSubmodule k hv))
    apply le_trans _ hn
    apply Submodule.span_le.mpr
    rintro _ ⟨k, hk, v, hv, rfl⟩
    exact (sectionRepresentation_trivial_iff ρ (c n) (c (n + 1)) k).mp
      (hc n (Nat.lt_succ_self n) k hk) v hv

end Representation.BinaryOffender
