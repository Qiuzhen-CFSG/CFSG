module

public import Theory.SpecificGroups.LieType.ParabolicModelVersions
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.SU3.BinaryG2Comparison
public import Theory.SpecificGroups.ReeG2.TernaryDerivedEquiv
public import Theory.SpecificGroups.ReeF4.DerivedTits

/-!
# The four small derived endpoints

The finite parabolic construction uses the full fixed model.  In the four
small cases GLS3 Chapter 3, §3.3 passes to the derived endpoint and records
the index of its intersection with the root radical.  This module exposes the
actual comparison theorems separately, so later parabolic proofs can provide
the root witness and the covering/index fields of `DerivedParabolicVersion`.

The ternary Ree comparison remains conditional on the two concrete maps from
the nine-point permutation model: the projective identification and a
nontrivial homomorphism into the literal Ree matrix model.  Keeping those
premises explicit is essential; no classification-defined carrier is used.
-/

@[expose] public section

namespace Theory.SpecificGroups.LieType.ParabolicModelVersions.SmallDerived

open Theory.SpecificGroups.SymplecticFour

/-- The binary symplectic endpoint is the actual derived subgroup of the
central quotient `PSp₄(2)`, identified with `A₆`. -/
noncomputable def b2DerivedEquivAlternatingSix :
    commutator (Sp (ZMod 2) ⧸ Subgroup.center (Sp (ZMod 2))) ≃*
      alternatingGroup (Fin 6) :=
  Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix

theorem b2Derived_nonempty :
    Nonempty (commutator (Sp (ZMod 2) ⧸ Subgroup.center (Sp (ZMod 2))) ≃*
      alternatingGroup (Fin 6)) :=
  ⟨b2DerivedEquivAlternatingSix⟩

/-- Fong's concrete comparison for `G₂(2)'`. -/
theorem g2Derived_nonempty :
    Nonempty (commutator (Atlas.G2.Model (ZMod 2)) ≃*
      ABG.PSU3 3 1 (by decide)) :=
  Atlas.G2.nonempty_commutator_binary_equiv_psu3

open scoped MatrixGroups
open Atlas.ReeG2 Atlas.ReeG2.TernaryDerived

/-- The two independent concrete maps needed for `²G₂(3)'`. -/
structure TernaryReeComparison where
  permutationEquiv : PermutationModel ≃* PSL(2, GaloisField 2 3)
  modelHom : PermutationModel →* Model (ZMod 3) 0
  modelHom_ne_one : modelHom ≠ 1

/-- Assembly of the ternary Ree derived equivalence from the actual maps. -/
noncomputable def reeG2TernaryDerivedEquiv (h : TernaryReeComparison) :
    commutator (Model (ZMod 3) 0) ≃* PSL(2, GaloisField 2 3) :=
  equivOfPermutationModel h.permutationEquiv h.modelHom h.modelHom_ne_one

theorem reeG2TernaryDerived_nonempty (h : TernaryReeComparison) :
    Nonempty (commutator (Model (ZMod 3) 0) ≃* PSL(2, GaloisField 2 3)) :=
  ⟨reeG2TernaryDerivedEquiv h⟩

/-- The concrete Parrott comparison for the derived binary Ree group. -/
theorem reeF4BinaryDerived_nonempty :
    Nonempty (commutator (ReeF4.Model 0) ≃* Tits.ParrottGroup) :=
  ReeF4.DerivedTits.nonempty_derived_equiv

end Theory.SpecificGroups.LieType.ParabolicModelVersions.SmallDerived

end
