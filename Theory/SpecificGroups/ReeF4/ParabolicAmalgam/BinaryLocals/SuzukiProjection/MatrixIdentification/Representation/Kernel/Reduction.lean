module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.BinaryLocals.SuzukiProjection.MatrixIdentification.Representation.Kernel.FourComparison

/-!
# Reduction of the full ambient kernel to finite word identities

Assume the five explicit ambient words satisfy the A₅ Coxeter relations and
the four recovery identities. The type-A presentation then supplies an S₆
homomorphism onto the entire split Levi. Its action on the four half-root
lines agrees with the faithful S₆ map constructed in `FourComparison`.
Consequently every Levi element fixing the four-space is the identity.

Both premises concern concrete words in the actual 52-dimensional root
matrices. They remain explicit proof obligations; the conditional reduction
does not establish them or the unconditional kernel theorem.

Source context: the split B₂ Levi used in Aschbacher–Smith F.1.12(I)(5),
printed pp.263–264 (PDF pp.274–275) of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open GLS3.Chapter5.SchurPresentation

namespace ReeF4.Parabolics.BinarySuzuki.MatrixIdentification
namespace KernelProof

/-- The ambient S₆ homomorphism once the five explicit words satisfy the
Coxeter relations. -/
def ambientHom (hrel : (CoxeterMatrix.A 5).IsLiftable ambientChain) :
    Equiv.Perm (Fin 6) →* splitLevi :=
  ((CoxeterMatrix.A 5).toCoxeterSystem.lift ⟨ambientChain, hrel⟩).comp
    sixCoxeterEquiv.symm.toMonoidHom

theorem ambientHom_adjacent (hrel : (CoxeterMatrix.A 5).IsLiftable ambientChain)
    (i : Fin 5) : ambientHom hrel (adjacentSwap 1 i) = ambientChain i := by
  rw [← sixCoxeterEquiv_simple i]
  change ((CoxeterMatrix.A 5).toCoxeterSystem.lift ⟨ambientChain, hrel⟩)
    (sixCoxeterEquiv.symm (sixCoxeterEquiv ((CoxeterMatrix.A 5).simple i))) = _
  rw [MulEquiv.symm_apply_apply]
  exact (CoxeterMatrix.A 5).toCoxeterSystem.lift_apply_simple hrel i

/-- Recovering the four root generators proves that the ambient S₆ map
covers the whole generated Levi. -/
theorem ambientHom_surjective (hrel : (CoxeterMatrix.A 5).IsLiftable ambientChain)
    (hrec : ∀ i, ((recoveryWord i).map ambientChain).prod = splitGenerator i) :
    Function.Surjective (ambientHom hrel) := by
  apply MonoidHom.range_eq_top.mp
  apply top_le_iff.mp
  rw [← splitGenerator_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  rw [← hrec i]
  refine ⟨((recoveryWord i).map (adjacentSwap 1)).prod, ?_⟩
  simp only [map_list_prod, List.map_map, Function.comp_def, ambientHom_adjacent]

/-- The two S₆ maps intertwine on the entire group, by induction in the
Coxeter generators. -/
theorem ambientHom_intertwines (hrel : (CoxeterMatrix.A 5).IsLiftable ambientChain)
    (s : Equiv.Perm (Fin 6)) :
    (ambientLeviHom (ambientHom hrel s)).val * fourEmbedding =
      fourEmbedding * (fourHom s).val := by
  have h : ∀ w : (CoxeterMatrix.A 5).Group,
      (ambientLeviHom (ambientHom hrel (sixCoxeterEquiv w))).val * fourEmbedding =
        fourEmbedding * (fourHom (sixCoxeterEquiv w)).val := by
    intro w
    apply (CoxeterMatrix.A 5).toCoxeterSystem.simple_induction_right w
    · simp
    · intro w i ih
      change (ambientLeviHom (ambientHom hrel
        (sixCoxeterEquiv (w * (CoxeterMatrix.A 5).simple i)))).val * fourEmbedding =
          fourEmbedding * (fourHom
            (sixCoxeterEquiv (w * (CoxeterMatrix.A 5).simple i))).val
      simp only [map_mul, sixCoxeterEquiv_simple, ambientHom_adjacent, fourHom_adjacent,
        Units.val_mul]
      rw [Matrix.mul_assoc, ambientChain_intertwines, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc]
  simpa only [MulEquiv.apply_symm_apply] using h (sixCoxeterEquiv.symm s)

end KernelProof

/-- A finite-presentation reduction of the full-Levi kernel question. Its only
premises are explicit Coxeter and generator-recovery identities in the actual
ambient root elements; these premises must still be discharged. -/
theorem fourSpace_faithful_of_chain_relations
    (hrel : (CoxeterMatrix.A 5).IsLiftable KernelProof.ambientChain)
    (hrec : ∀ i, ((KernelProof.recoveryWord i).map KernelProof.ambientChain).prod =
      splitGenerator i)
    (x : splitLevi) (hx : (ambientLeviHom x).val * fourEmbedding = fourEmbedding) :
    x = 1 := by
  obtain ⟨s, rfl⟩ := KernelProof.ambientHom_surjective hrel hrec x
  have hs : KernelProof.fourHom s = 1 := by
    apply Units.ext
    apply fourEmbedding_mul_injective
    change fourEmbedding * (KernelProof.fourHom s).val = fourEmbedding * 1
    rw [← KernelProof.ambientHom_intertwines hrel s, hx]
    simp
  have hs' : s = 1 := KernelProof.fourHom_injective (by simpa using hs)
  rw [hs', map_one]

end ReeF4.Parabolics.BinarySuzuki.MatrixIdentification
