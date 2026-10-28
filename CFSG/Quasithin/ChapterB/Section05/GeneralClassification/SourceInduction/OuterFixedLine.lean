module

public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# The fixed line in the rank-five branch of B.5.7

The five-dimensional augmentation core of the binary six-point permutation
module has exactly one nonzero A₆-fixed vector, the all-one vector. If a
normal subgroup L of G acts on a G-invariant subspace W as this core, then
normality makes its fixed line G-invariant. Over F₂ every invertible action
on a line is trivial. Consequently W meets C_V(G) nontrivially.

The final theorem uses the actual equality W = [V,L] and rules out
`V = C_V(G) ⊕ ([V,L] ⊕ X)` for every subspace X. This obstructs the printed
rank-five deduction at the end of B.5.7: its rank-five core cannot have the
disjointness asserted in B.5.6(4). The literal PDF has the direct-sum sign.

This is a local obstruction, not a counterexample satisfying all of B.5.3.
In particular, the existence of this branch under a genuine SQTK quotient
is not asserted here. To complete the requested literal classification one
must exclude this branch from B.5.3 by an additional argument, or resolve
the source statement. No corrected classification is asserted.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, B.5.6(4), printed p.105 (PDF p.116), and the
rank-five paragraph of the proof of B.5.7, printed p.106 (PDF p.117).
-/

@[expose] public section

open BinaryPermutation Representation

namespace CFSG.Quasithin.ChapterB.SourceInduction.OuterFixedLine

/-- The literal augmentation kernel of the six-point binary permutation module. -/
abbrev SixCore := core (Fin 6)
/-- The action of the actual alternating group on that kernel. -/
abbrev sixAction := alternatingCoreRepresentation (Fin 6)

/-- The all-one vector lies in the augmentation kernel because six is even. -/
def fixedVector : SixCore := ⟨allOne (Fin 6), by
  rw [mem_core]
  decide⟩

/-- The fixed line is nonzero. -/
theorem fixedVector_ne_zero : fixedVector ≠ 0 := by
  intro h
  exact allOne_ne_zero (Fin 6) (congrArg Subtype.val h)

/-- Every even coordinate permutation fixes the all-one vector. -/
theorem fixedVector_fixed (g : alternatingGroup (Fin 6)) :
    sixAction g fixedVector = fixedVector := by
  apply Subtype.ext
  exact permute_allOne (Fin 6) g.val

/-- Transitivity on the six coordinates leaves exactly two fixed vectors. -/
theorem fixed_eq_zero_or (v : SixCore) (hv : ∀ g, sixAction g v = v) :
    v = 0 ∨ v = fixedVector := by
  let := alternatingGroup.isPretransitive_of_three_le_card (Fin 6) (by simp)
  have hc (i : Fin 6) : v.val i = v.val 0 := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 6)) (0 : Fin 6) i
    have he := congrArg (fun w : SixCore => w.val i) (hv g)
    change v.val (g.val.symm i) = v.val i at he
    have hgi : g.val 0 = i := hg
    rw [show g.val.symm i = 0 from g.val.symm_apply_eq.mpr hgi.symm] at he
    exact he.symm
  have hz : v.val 0 = 0 ∨ v.val 0 = 1 := by
    have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    exact h _
  rcases hz with hz | hz
  · left
    apply Subtype.ext
    funext i
    exact (hc i).trans hz
  · right
    apply Subtype.ext
    funext i
    exact (hc i).trans hz

/-- This is the rank-five core occurring in the printed proof. -/
theorem sixCore_finrank : Module.finrank (ZMod 2) SixCore = 5 := by
  simpa using finrank_core (Fin 6)

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Any ambient extension of the core action of a normal A₆ fixes its
nonzero fixed vector. Both group and module identifications are actual
isomorphisms, and the module identification intertwines the given action. -/
theorem normal_sixCore_fixed (L : Subgroup G) [L.Normal]
    (W : Subrepresentation ρ) (eL : L ≃* alternatingGroup (Fin 6))
    (eW : W.toSubmodule ≃ₗ[ZMod 2] SixCore)
    (he : ∀ l : L, ∀ w : W.toSubmodule,
      eW (W.toRepresentation l.val w) = sixAction (eL l) (eW w)) :
    ∃ v : V, v ≠ 0 ∧ v ∈ W ∧ v ∈ ρ.invariants := by
  let w : W.toSubmodule := eW.symm fixedVector
  have hw0 : w ≠ 0 := by
    intro h
    apply fixedVector_ne_zero
    have hh := congrArg eW h
    simpa [w] using hh
  have hw (l : L) : W.toRepresentation l.val w = w := by
    apply eW.injective
    rw [he]
    simp only [w, LinearEquiv.apply_symm_apply]
    exact fixedVector_fixed _
  have hwG (g : G) : W.toRepresentation g w = w := by
    have hfixed (l : L) :
        W.toRepresentation l.val (W.toRepresentation g w) = W.toRepresentation g w := by
      let l' : L := ⟨g⁻¹ * l.val * g,
        by simpa only [inv_inv] using (inferInstance : L.Normal).conj_mem l.val l.property g⁻¹⟩
      calc
        _ = W.toRepresentation g (W.toRepresentation l'.val w) := by
          simp only [l', map_mul, Module.End.mul_apply]
          simp
        _ = W.toRepresentation g w := congrArg (W.toRepresentation g) (hw l')
    have hf (a : alternatingGroup (Fin 6)) :
        sixAction a (eW (W.toRepresentation g w)) = eW (W.toRepresentation g w) := by
      obtain ⟨l, rfl⟩ := eL.surjective a
      rw [← he, hfixed]
    rcases fixed_eq_zero_or _ hf with hz | hz
    · have hzero : W.toRepresentation g w = 0 := eW.map_eq_zero_iff.mp hz
      have hh := congrArg (W.toRepresentation g⁻¹) hzero
      simp only [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
        map_one, Module.End.one_apply] at hh
      exact (hw0 hh).elim
    · apply eW.injective
      simpa only [w, LinearEquiv.apply_symm_apply] using hz
  refine ⟨w.val, ?_, w.property, ?_⟩
  · intro h
    exact hw0 (Subtype.ext h)
  · intro g
    exact congrArg Subtype.val (hwG g)

/-- A subspace carrying the normal A₆ core cannot occur as a summand
disjoint from the whole ambient fixed space. -/
theorem no_outer_split (L : Subgroup G) [L.Normal]
    (W : Subrepresentation ρ) (eL : L ≃* alternatingGroup (Fin 6))
    (eW : W.toSubmodule ≃ₗ[ZMod 2] SixCore)
    (he : ∀ l : L, ∀ w : W.toSubmodule,
      eW (W.toRepresentation l.val w) = sixAction (eL l) (eW w))
    (X : Submodule (ZMod 2) V) :
    ¬ IsCompl ρ.invariants (W.toSubmodule ⊔ X) := by
  intro h
  obtain ⟨v, hv0, hvW, hvG⟩ := normal_sixCore_fixed ρ L W eL eW he
  exact hv0 (Submodule.disjoint_def.mp h.disjoint v hvG (Submodule.mem_sup_left hvW))

open Representation.BinaryOffender

/-- The obstruction on the literal commutator space in B.5.7: in the
rank-five core branch, the direct sum demanded by B.5.6(4) is impossible. -/
theorem no_moved_outer_split (L : Subgroup G) [L.Normal]
    (W : Subrepresentation ρ) (hW : W.toSubmodule = subspaceCommutator ρ ⊤ L)
    (eL : L ≃* alternatingGroup (Fin 6))
    (eW : W.toSubmodule ≃ₗ[ZMod 2] SixCore)
    (he : ∀ l : L, ∀ w : W.toSubmodule,
      eW (W.toRepresentation l.val w) = sixAction (eL l) (eW w))
    (X : Submodule (ZMod 2) V) :
    ¬ IsCompl ρ.invariants (subspaceCommutator ρ ⊤ L ⊔ X) := by
  rw [← hW]
  exact no_outer_split ρ L W eL eW he X

end CFSG.Quasithin.ChapterB.SourceInduction.OuterFixedLine
