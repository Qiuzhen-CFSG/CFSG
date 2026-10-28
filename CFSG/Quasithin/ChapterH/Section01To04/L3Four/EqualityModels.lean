module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.Source
public import Theory.Representation.HermitianTensorThree
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# Concrete equality predicates for H.4.7

The module alternative is an actual equivalence of the pulled-back source
representation with the nine-dimensional Hermitian tensor or its dual. The
actor alternative compares literal conjugation with an automorphism conjugate
to square Frobenius in Aut(PSL₃(4)). Full automorphism conjugacy permits the
diagonal re-markings present in the source; it is stronger than merely asking
for a nontrivial field component in the outer automorphism group.

These predicates fix the equality conclusion of Aschbacher–Smith H.4.7,
printed pp.382–383 of refs/quasithin.pdf. They are specifications, not assumed
classification or displacement theorems. The final equivalence remains an
assembly obligation.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
open Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
variable {M V : Type*} [Group M] [AddCommGroup V] [Module (ZMod 2) V]

/-- The equality case specifies an actual equivalence to the descended tensor or its dual. -/
def IsTensorModule (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V) : Prop :=
  Nonempty ((coverRep e ρ).Equiv (HermitianTensorThree.binaryAction 1)) ∨
    Nonempty ((coverRep e ρ).Equiv (HermitianTensorThree.binaryAction 1).dual)

/-- The literal conjugation action is conjugate in Aut(PSL₃(4)) to square Frobenius.
Allowing the full automorphism group retains the diagonal re-markings. -/
def InducesFieldAutomorphism (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (t : M) : Prop :=
  ∃ a : MulAut Matrix.PSL3Four.PSL, IsConj Matrix.PSL3Four.pslFrobenius a ∧
    ∀ x, t * (e x : M) * t⁻¹ = (e (a x) : M)

/-- Actual tensor equivalences, rather than a family tag, force binary dimension nine. -/
theorem IsTensorModule.finrank (e : Matrix.PSL3Four.PSL ≃* generalizedFitting M)
    (ρ : Representation (ZMod 2) M V) (h : IsTensorModule e ρ) :
    Module.finrank (ZMod 2) V = 9 := by
  unfold IsTensorModule at h
  rcases h with hh | hh
  · obtain ⟨φ⟩ := hh
    rw [φ.toLinearEquiv.finrank_eq]
    simpa using HermitianTensorThree.finrank_binary 1
  · obtain ⟨φ⟩ := hh
    rw [φ.toLinearEquiv.finrank_eq, Subspace.dual_finrank_eq]
    simpa using HermitianTensorThree.finrank_binary 1

end CFSG.Quasithin.ChapterH.Section01To04.L3Four
