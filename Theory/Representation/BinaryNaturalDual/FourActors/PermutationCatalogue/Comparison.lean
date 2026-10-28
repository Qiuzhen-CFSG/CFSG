module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model

/-!
# Relative centralizers under the eight-point comparison

The actual automorphism/permutation equivalence takes the inner subgroup to
A₈ and preserves commutation. Restricting it therefore gives a multiplicative
equivalence from each inner centralizer to the corresponding relative
centralizer in A₈. Composing with the fixed-group comparison gives the same
identification for the original linear group. Subgroup conjugation is also
transported through this one specified equivalence.

This is a transport interface, not a claim about either centralizer's structure.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(1),
printed p.391, PDF p.402.
-/

@[expose] public section

open Equiv Subgroup
namespace BinaryNaturalDual.FourActors.PermutationCatalogue

theorem innerCentralizer_map (a : M) :
    (innerCentralizer a).map permutationEquiv.toMonoidHom =
      alternatingGroup (Fin 8) ⊓ centralizer ({permutationEquiv a} : Set S) := by
  ext q
  constructor
  · rintro ⟨b, hb, rfl⟩
    refine ⟨(permutationEquiv_mem_alternating b).mpr hb.1, ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    simpa using congrArg permutationEquiv (mem_centralizer_singleton_iff.mp hb.2)
  · intro hq
    refine ⟨permutationEquiv.symm q, ?_, permutationEquiv.apply_symm_apply q⟩
    constructor
    · exact (permutationEquiv_mem_alternating _).mp (by simpa using hq.1)
    · apply mem_centralizer_singleton_iff.mpr
      apply permutationEquiv.injective
      simpa using mem_centralizer_singleton_iff.mp hq.2

noncomputable def innerCentralizerPermutationEquiv (a : M) :
    innerCentralizer a ≃*
      (alternatingGroup (Fin 8) ⊓ centralizer ({permutationEquiv a} : Set S) : Subgroup S) :=
  (permutationEquiv.subgroupMap (innerCentralizer a)).trans
    (MulEquiv.subgroupCongr (innerCentralizer_map a))

noncomputable def fixedPermutationEquiv (a : M) :
    a.fixedSubgroup ≃*
      (alternatingGroup (Fin 8) ⊓ centralizer ({permutationEquiv a} : Set S) : Subgroup S) :=
  (fixedInnerEquiv a).trans (innerCentralizerPermutationEquiv a)

theorem permutation_map_conj (A : Subgroup M) (a : M) :
    (A.map (MulAut.conj a).toMonoidHom).map permutationEquiv.toMonoidHom =
      (A.map permutationEquiv.toMonoidHom).map
        (MulAut.conj (permutationEquiv a)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext b
  simp

end BinaryNaturalDual.FourActors.PermutationCatalogue
