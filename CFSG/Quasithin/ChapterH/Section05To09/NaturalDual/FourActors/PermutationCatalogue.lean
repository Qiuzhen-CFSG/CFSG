module

public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.FourActors.PermutationCatalogue.ElementaryThompson

/-!
# The permutation clauses H.9.3(1,3)

The two outer-involution classes are disjoint and exhaustive, and their inner
centralizers are S₆ and C₂ × S₄. The imported constructions supply actual
multiplicative equivalences, including equivalences for the fixed subgroups
of the original natural linear group.

The three specified elementary subgroups of order sixteen exhaust the
conjugacy classes, with unique class indices and actual conjugators. Their
orbit partitions are 4², 2⁴ and 2²·4. The first is the elementary Thompson
subgroup of the chosen Sylow intersection; the other two are not inner.
The imported Thompson adapter also transports this identification to any
Sylow choice. These conclusions have no additional classification premises.

The proofs assemble the permutation centralizer calculations, the exhaustion
inside the binary-tree Sylow, and the uniqueness of its largest even elementary
subgroup. The natural-dual module clauses H.9.3(2,4–6) have separate owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(1,3),
printed pp.391–392, PDF pp.402–403.
-/

public section

namespace CFSG.Quasithin.ChapterH.NaturalDual.FourActors
open BinaryNaturalDual.FourActors BinaryNaturalDual.FourActors.PermutationCatalogue

theorem marked_representative_elementary_order (i : Fin 3) :
    IsElementaryAbelian 2 (actor i) ∧ Nat.card (actor i) = 16 :=
  ⟨actor_elementary i, actor_card i⟩

theorem marked_representatives_distinct (i j : Fin 3) :
    (∃ a : M, (actor i).map (MulAut.conj a).toMonoidHom = actor j) ↔ i = j :=
  actor_conjugate_iff i j

/-- H.9.3(1): precisely two outer-involution classes, with their full relative
centralizers. The equivalences are the constructed maps in the theory module. -/
theorem outer_involution_catalogue :
    (orderOf transposition = 2 ∧ transposition ∉ BinaryNaturalDual.FourActors.inner) ∧
    (orderOf tripleTransposition = 2 ∧ tripleTransposition ∉ BinaryNaturalDual.FourActors.inner) ∧
    (∀ a : M, orderOf a = 2 → a ∉ BinaryNaturalDual.FourActors.inner →
      IsConj a transposition ∨ IsConj a tripleTransposition) ∧
    ¬ IsConj transposition tripleTransposition ∧
    Nonempty (innerCentralizer transposition ≃* Equiv.Perm (Fin 6)) ∧
    Nonempty (innerCentralizer tripleTransposition ≃*
      (Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :=
  ⟨⟨transposition_order, transposition_outer⟩,
    ⟨tripleTransposition_order, tripleTransposition_outer⟩,
    outer_involution_conjugacy, not_isConj_representatives,
    ⟨transpositionCentralizerEquiv⟩, ⟨tripleTranspositionCentralizerEquiv⟩⟩

/-- H.9.3(3): the three actual conjugacy classes, their orbits, and the elementary
Thompson marking. `blockLabel` describes precisely the partitions 4², 2⁴, 2²·4;
the imported `A0_orbit_partition`, `A1_orbit_partition`, and `A2_orbit_partition`
also give these orbit sets explicitly on the eight letters. -/
theorem elementary_sixteen_catalogue :
    (∀ i : Fin 3, IsElementaryAbelian 2 (actor i) ∧ Nat.card (actor i) = 16 ∧
      ∀ x : Fin 8, actorOrbit (actor i) x = {y | blockLabel i y = blockLabel i x}) ∧
    (∀ E : Subgroup M, IsElementaryAbelian 2 E → Nat.card E = 16 →
      ∃! i : Fin 3, ∃ a : M, E.map (MulAut.conj a).toMonoidHom = actor i) ∧
    (∀ i j : Fin 3,
      (∃ a : M, (actor i).map (MulAut.conj a).toMonoidHom = actor j) ↔ i = j) ∧
    Stellmacher.elementaryAbelianMaxJ
      ((T0 : Subgroup M) ⊓ BinaryNaturalDual.FourActors.inner) = A0 ∧
    A0 ≤ BinaryNaturalDual.FourActors.inner ∧
    ¬ A1 ≤ BinaryNaturalDual.FourActors.inner ∧ ¬ A2 ≤ BinaryNaturalDual.FourActors.inner := by
  refine ⟨fun i => ⟨actor_elementary i, actor_card i, actor_orbit i⟩,
    ?_, actor_conjugate_iff, elementaryThompson_T0_inner,
    A0_le_inner, A1_not_le_inner, A2_not_le_inner⟩
  intro E hE hcard
  let := hE
  exact existsUnique_actor_conjugate E hcard

end CFSG.Quasithin.ChapterH.NaturalDual.FourActors
