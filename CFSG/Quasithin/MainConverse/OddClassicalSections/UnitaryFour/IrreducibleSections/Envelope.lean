module

public import CFSG.Quasithin.MainConverse.SolvableSections
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.SectionReduction

/-!
# Concrete quotient models for the irreducible PSU₄(3) branch

The three targets below are actual permutation and matrix groups. A kernel
model is a homomorphism with solvable kernel; it need not be surjective.
We also allow such a model on a normal subgroup with solvable outer quotient.
This is needed for almost simple overgroups such as A₆.2₃. The first
isomorphism theorem and closure of K-groups under extensions remove both
solvable layers when calculating the nonsolvable simple sections.

This interface separates the intrinsic subgroup-coverage calculation from
the smaller-model section calculations. In particular, its definition is not
a theorem that every maximal irreducible subgroup has such a witness.
The final coverage and section premises must all be discharged by the owner
of `IrreducibleSections.lean`.

Source obligation: Aschbacher–Smith, Theorem 0.1.2(4) and condition K,
printed pp.4 and 482 of `refs/quasithin.pdf`. Unitary conventions are those
of GLS3, §2.7, as implemented in `UnitaryFourThree.Model`.
The A₆.2₃ motivation can be checked in the
[GAP Character Table Library entry](https://www.math.rwth-aachen.de/~Thomas.Breuer/ctbllib/ctbltoc/data/U4(3).html).
That table is not used as a proof of coverage.
-/

namespace CFSG.Quasithin.MainConverse.UnitaryFourIrreducible

open CFSG.KnownSimple

/-- The degree-seven permutation group, including its alternating subgroup. -/
public abbrev PermutationTarget := Equiv.Perm (Fin 7)

/-- The usual central quotient of SL₃ over the field with four elements. -/
public abbrev LinearTarget :=
  Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2)

/-- The standard four-dimensional projective symplectic group over F₃. -/
public abbrev SymplecticTarget := ClassicalGroup.PSp 2 (ZMod 3)

/-- Each alternative is linked to the domain by an actual homomorphism.
The kernel is normal in the domain; no ambient normality is imposed. -/
@[expose] public def HasSolvableKernelModel (G : Type) [Group G] : Prop :=
  (∃ f : G →* PermutationTarget, Group.IsSolvable f.ker) ∨
  (∃ f : G →* LinearTarget, Group.IsSolvable f.ker) ∨
  (∃ f : G →* SymplecticTarget, Group.IsSolvable f.ker)

/-- Solvable groups are included by their trivial permutation representation. -/
public theorem HasSolvableKernelModel.of_solvable (G : Type) [Group G]
    [Group.IsSolvable G] : HasSolvableKernelModel G :=
  Or.inl ⟨1, inferInstance⟩

private theorem isKGroup_of_solvable_kernel {G H : Type} [Group G] [Group H]
    (hH : IsKGroup IsConstructedCarrier H) (f : G →* H)
    [Group.IsSolvable f.ker] : IsKGroup IsConstructedCarrier G := by
  have hQ : IsKGroup IsConstructedCarrier (G ⧸ f.ker) :=
    (IsKGroup.equiv (QuotientGroup.quotientKerEquivRange f)).mpr (hH.subgroup f.range)
  exact IsKGroup.of_normal_quotient f.ker (solvable_isKGroup_constructed _) hQ

/-- The section calculation uses the actual image in the selected model. -/
public theorem HasSolvableKernelModel.isKGroup {G : Type} [Group G]
    (h : HasSolvableKernelModel G)
    (hperm : IsKGroup IsConstructedCarrier PermutationTarget)
    (hlinear : IsKGroup IsConstructedCarrier LinearTarget)
    (hsymp : IsKGroup IsConstructedCarrier SymplecticTarget) :
    IsKGroup IsConstructedCarrier G := by
  rcases h with ⟨f, hf⟩ | ⟨f, hf⟩ | ⟨f, hf⟩
  · let := hf
    exact isKGroup_of_solvable_kernel hperm f
  · let := hf
    exact isKGroup_of_solvable_kernel hlinear f
  · let := hf
    exact isKGroup_of_solvable_kernel hsymp f

/-- The normal alternative retains a possibly nontrivial solvable outer
quotient. Both its subgroup and the kernel-model homomorphism are actual data. -/
public inductive HasSolvableLayersModel (G : Type) [Group G] : Prop
  | direct (model : HasSolvableKernelModel G)
  | normal (L : Subgroup G) [L.Normal]
      (outer : Group.IsSolvable (G ⧸ L)) (model : HasSolvableKernelModel L)

/-- Removing a solvable outer quotient preserves the section calculation. -/
public theorem HasSolvableLayersModel.isKGroup {G : Type} [Group G]
    (h : HasSolvableLayersModel G)
    (hperm : IsKGroup IsConstructedCarrier PermutationTarget)
    (hlinear : IsKGroup IsConstructedCarrier LinearTarget)
    (hsymp : IsKGroup IsConstructedCarrier SymplecticTarget) :
    IsKGroup IsConstructedCarrier G := by
  cases h with
  | direct model => exact model.isKGroup hperm hlinear hsymp
  | normal L outer model =>
    let := outer
    exact IsKGroup.of_normal_quotient L (model.isKGroup hperm hlinear hsymp)
      (solvable_isKGroup_constructed _)

end CFSG.Quasithin.MainConverse.UnitaryFourIrreducible
