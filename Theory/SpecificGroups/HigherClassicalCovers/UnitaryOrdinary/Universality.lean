module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.Basic
public import Theory.GroupTheory.CoveringKernelEquiv

/-!
# From central closure of SU to universality of its natural cover

The constructed universal cover of PSU maps onto the natural SU cover.
If every finite perfect central extension of that SU is injective, this
comparison is an isomorphism, with its original projection unchanged.
It identifies the two kernels and proves the universal property in every
target universe.

This is a conditional assembly lemma for the ordinary unitary rows of
Aschbacher--Smith I.1.3--4 (pp.407--408), not a central-closure theorem.
The central-closure premises must be proved separately for the actual SU
groups. The comparison follows the existing symplectic construction in
`SymplecticFour/CentralCovers/OddPrime/Assembly.lean`.
-/

public section

open BenderSuzuki.MatrixGroups Theory.GroupTheory

namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary

universe u w
variable {F : Type u} [Field F] [Finite F] {n : ℕ}

/-- Central closure of the actual matrix group suffices for its literal
projective map to be universal. This lemma retains the closure premise. -/
theorem naturalCover_isUniversal_of_closed (J : HermitianForm n F)
    [Group.IsPerfect J.specialSubgroup]
    [IsQuasisimple (ProjectiveSpecialUnitaryMatrixGroup J)]
    (hclosed : ∀ (E : Type u) [Group E] [Finite E]
      (f : PerfectCentralCovering.Cover E J.specialSubgroup),
      Function.Injective f.toMonoidHom) :
    letI := natural_isQuasisimple J
    Covering.IsUniversal.{u, u, w} (naturalCover J) := by
  let := natural_isQuasisimple J
  let c := PerfectCentralCovering.universalQuasisimpleCover
    (ProjectiveSpecialUnitaryMatrixGroup J)
  have hc : Covering.IsUniversal.{u, u, u} c :=
    PerfectCentralCovering.universalQuasisimpleCover_isUniversal _
  let a := hc.lift (naturalCover J)
  have ha := hc.lift_fac (naturalCover J)
  let e : PerfectCentralCovering.UniversalGroup
      (ProjectiveSpecialUnitaryMatrixGroup J) ≃* J.specialSubgroup :=
    MulEquiv.ofBijective a.toMonoidHom
      ⟨hclosed _ (PerfectCentralCovering.ofCovering a), a.surjective⟩
  let k := Covering.kerMulEquivOfSquare c.toMonoidHom
    (naturalCover J).toMonoidHom e (MulEquiv.refl _)
    (fun x => congrArg (fun f : Covering _ _ => f x) ha)
  apply Covering.isUniversal_of_kernel_card_le
  exact le_of_eq (Nat.card_congr k.toEquiv)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary
