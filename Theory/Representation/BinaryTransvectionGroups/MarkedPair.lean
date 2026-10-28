module

public import Theory.Representation.BinaryTransvectionGroups.ReducedCommutation

/-!
# The displacement plane of two marked binary transvections

Two linear maps with displacement in the lines through z and r generate a
group with displacement in their plane. If the first moves r by z and the
second moves z by r, both lines occur, so the displacement space is exactly
that plane. In a group with trivial two-core, this discharges the displacement
hypothesis of the reduced-commutation theorem.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
proof of Lemma 16.4.7, printed p.1187. Constructing the two marked elements
inside the prescribed relative normalizers is a separate group-theoretic step.
-/

@[expose] public section

namespace BinaryTransvectionGroups
open BinaryLinear Subgroup
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The displacement span is the smallest subspace on whose quotient the
group acts trivially. -/
theorem displacementSpan_le_iff (X : Subgroup (GL V)) (W : Submodule (ZMod 2) V) :
    displacementSpan X ≤ W ↔ X ≤ quotientFixer W := by
  rw [displacementSpan, Submodule.span_le]
  constructor
  · intro h x hx v
    exact h ⟨⟨x, hx⟩, v, rfl⟩
  · rintro h w ⟨x, v, rfl⟩
    exact h x.property v

/-- Both nonzero cross-displacements are retained; no representation
recognition or assumption about the generated group's order is needed. -/
theorem pair_displacementSpan (t u : GL V) (r z : V)
    (ht : t ∈ quotientFixer (centerLine z))
    (hu : u ∈ quotientFixer (centerLine r))
    (htr : t r - r = z) (huz : u z - z = r) :
    displacementSpan (zpowers t ⊔ zpowers u) = centerLine r ⊔ centerLine z := by
  apply le_antisymm
  · apply (displacementSpan_le_iff _ _).mpr
    exact sup_le (zpowers_le.mpr (fun v => Submodule.mem_sup_right (ht v)))
      (zpowers_le.mpr (fun v => Submodule.mem_sup_left (hu v)))
  · apply sup_le <;> apply Submodule.span_le.mpr
    · rintro v (rfl : v = r)
      exact Submodule.subset_span
        ⟨⟨u, mem_sup_right (mem_zpowers u)⟩, z, huz⟩
    · rintro v (rfl : v = z)
      exact Submodule.subset_span
        ⟨⟨t, mem_sup_left (mem_zpowers t)⟩, r, htr⟩

/-- Fixation of Q passes from the two marked generators to X. -/
theorem pair_le_pointwiseFixer (t u : GL V) (Q : Submodule (ZMod 2) V)
    (ht : t ∈ pointwiseFixer Q) (hu : u ∈ pointwiseFixer Q) :
    zpowers t ⊔ zpowers u ≤ pointwiseFixer Q :=
  sup_le (zpowers_le.mpr ht) (zpowers_le.mpr hu)

/-- The reduced group fixes both marked centers under every element acting
trivially modulo Q. In the shadow application such an element must move r. -/
theorem fixes_marked_pair_of_reduced (H : Subgroup (GL V))
    (Q : Submodule (ZMod 2) V) (hH : H ≤ parabolic Q)
    (hcore : pCore 2 H = ⊥) (t u : H) (r z : V)
    (ht : t.val ∈ quotientFixer (centerLine z))
    (hu : u.val ∈ quotientFixer (centerLine r))
    (htr : t.val r - r = z) (huz : u.val z - z = r)
    (htQ : t.val ∈ pointwiseFixer Q) (huQ : u.val ∈ pointwiseFixer Q)
    (hdis : Disjoint Q (centerLine r ⊔ centerLine z))
    (n : H) (hn : n.val ∈ quotientFixer Q) : n.val r = r ∧ n.val z = z := by
  have hXH : zpowers t.val ⊔ zpowers u.val ≤ H :=
    sup_le (zpowers_le.mpr t.property) (zpowers_le.mpr u.property)
  have hspan := pair_displacementSpan t.val u.val r z ht hu htr huz
  have hXQ := pair_le_pointwiseFixer t.val u.val Q htQ huQ
  have hd : Disjoint Q (displacementSpan (zpowers t.val ⊔ zpowers u.val)) := by
    rw [hspan]
    exact hdis
  have hfix (v : V) (hv : v ∈ displacementSpan (zpowers t.val ⊔ zpowers u.val)) :=
    fixes_displacementSpan_of_reduced H Q hH hcore
      (zpowers t.val ⊔ zpowers u.val) hXH hXQ hd n hn hv
  constructor
  · apply hfix
    rw [hspan]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self r)
  · apply hfix
    rw [hspan]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)

end BinaryTransvectionGroups
