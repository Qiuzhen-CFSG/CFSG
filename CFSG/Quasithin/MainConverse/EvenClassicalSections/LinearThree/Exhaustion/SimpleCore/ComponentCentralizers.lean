module

public import CFSG.Quasithin.MainConverse.EvenClassicalSections.LinearThree.Exhaustion.SimpleCore.Reduction
public import Theory.Representation.PerfectDegreeThree
public import Theory.Representation.GeneralLinearNatural
public import Theory.SpecificGroups.PSL3.ProjectionKernel

/-!
# Solvable centralizers of simple components in projective degree three

The natural action of `SL₃(F)` is faithful and its projection onto `PSL₃(F)`
has central kernel. The perfect residual of the inverse image of a nonsolvable
subgroup is nontrivial. Projective centralizers commute with that residual
already in `SL₃(F)`, by the perfect centralizer lifting theorem.

The degree-three constituent calculation then makes the lifted centralizer
solvable: two commuting perfect actions cannot both be nontrivial. Its proof
uses actual invariant subspaces and quotients, and Schur's lemma over the finite
endomorphism field. Solvability descends to the projective centralizer and then
to the relative centralizer inside `U`.

This calculation in fact needs only nonsolvability of `N`; in particular it
does not assume normality in `U`. The stated interface retains the hypotheses
of the simple-core reduction's characteristic-two application.

Source: GLS3, proof of Theorem 6.5.3, `refs/KGroup/GLS3/chapter6.tex`,
printed p.347, the unique constituent of dimension greater than one and
Schur's lemma.
-/

namespace CFSG.Quasithin.MainConverse.LinearThreeSections

open scoped MatrixGroups

/-- A nonabelian simple subnormal subgroup has solvable relative centralizer.
Ambient normality of the subgroup is not required. -/
public theorem simple_subnormal_centralizer_isSolvable
    (f : ℕ) (_hf : 2 ≤ f) (F : Type) [Field F] [Finite F]
    (_hF : Nat.card F = 2 ^ f) (U : Subgroup PSL(3,F))
    (_hU : U ≠ ⊤) (_hgeom : ¬ FixesPointOrDual F U)
    (_hab : ¬ HasAbelianNormal U) (N : Subgroup U)
    (_hsubnormal : N.IsSubnormal) [IsSimpleGroup N]
    (hns : ¬ Group.IsSolvable N) :
    Group.IsSolvable (Subgroup.centralizer (N : Set U)) := by
  let A := N.map U.subtype
  let e := N.equivMapOfInjective U.subtype U.subtype_injective
  have hA : ¬ Group.IsSolvable A := by
    intro ha
    let := ha
    exact hns (Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective)
  let : Group.IsSolvable (Subgroup.centralizer (A : Set PSL(3,F))) :=
    Representation.PerfectDegreeThree.quotient_centralizer_isSolvable
      (Representation.specialLinearNatural 3)
      (Representation.specialLinearNatural_injective 3) (by simp)
      (Matrix.PSL3.projection F) (Matrix.PSL3.projection_surjective F)
      (by rw [Matrix.PSL3.projection_ker]) A hA
  let C := Subgroup.centralizer (N : Set U)
  have hle : C.map U.subtype ≤ Subgroup.centralizer (A : Set PSL(3,F)) :=
    Subgroup.map_centralizer_le_centralizer_image (N : Set U) U.subtype
  let : Group.IsSolvable (C.map U.subtype) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
  let eC := C.equivMapOfInjective U.subtype U.subtype_injective
  exact Group.isSolvable_of_isSolvable_injective (f := eC.toMonoidHom) eC.injective

end CFSG.Quasithin.MainConverse.LinearThreeSections
