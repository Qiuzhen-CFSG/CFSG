module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.Setup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.CyclicSetup
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.InnerPreimage
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup.ActorCoordinates.AbelianGeometry.FixedFour

/-!
# Abelian outer coordinates: the noncyclic branch and final reduction

Split on the literal inner preimage of the abelian automorphism two-group.
The noncyclic case supplies a marked four-group fixed pointwise by the
entire actor. Its marked placement and standard-fixer normalization give
rotation coordinates. In the cyclic case the separate placement contract
supplies either root coordinates or such a fixed four-group.

Two inputs remain explicit: CyclicInnerPlacement for the normalized model
and StandardFixerCoordinates for its identity Gram model. This theorem
assembles their consequences; it does not claim either input or E.1.14(7).
The application leaf transports the result to the original faithful ambient
action without being imported here.
Source: Aschbacher--Smith E.1.14(7), printed p.214, and A.3.21(a)--(b),
printed p.55; Aschbacher (1982), Lemma 4.11.
-/

public section
open Matrix Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
open InnerGeometry.SemidihedralTorus
open AbelianGeometry
variable {F : Type} [Field F] [Finite F]
/-- The cyclic branch and the standard-four fixer suffice; the noncyclic
inner-preimage branch is discharged by the actual fixed four-group. -/
theorem abelianOuterCoordinateGeometry_of_cyclicInnerPlacement
    (J : HermitianForm 3 F) [IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J)]
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hcard : Nat.card F = p ^ 2) (hc : ∀ x, J.conj x = x ^ p)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hfix : StandardFixerCoordinates (HermitianForm.IdentityGram.identityGram J))
    (hcyclic : CyclicInnerPlacement J) : AbelianOuterCoordinateGeometry J := by
  intro U hU hcomm γ hγ hγU w hw hwU
  let : IsMulCommutative U := hcomm
  have hfour_or_root : RootActionCoordinates J U w ∨
      ∃ B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J),
        IsElementaryAbelian 2 B ∧ Nat.card B = 4 ∧ w ∈ B ∧
          ∀ a ∈ U, ∀ x ∈ B, a x = x := by
    by_cases hC : IsCyclic (U.comap MulAut.conj)
    · exact hcyclic U hU hcomm hC γ hγ hγU w hw hwU
    · have h2 : (2 : F) ≠ 0 := Field.two_ne_zero_of_odd_card F (by rw [hcard]; exact ho.pow)
      exact Or.inr (fixed_four_of_noncyclic_innerPreimage J
        (projective_center_eq_bot J hJ h2) U hU hC w hw hwU)
  rcases hfour_or_root with ⟨J', hconj, hroot⟩ | ⟨B, hBe, hB, hwB, hBU⟩
  · exact ⟨J', hconj, Or.inl hroot⟩
  · let := hBe
    obtain ⟨h2, e, he, hact⟩ := rotation_coordinates_of_fixed_four J hp ho hcard hc
      U hU w hw B hB hwB hBU hfix
    exact ⟨HermitianForm.IdentityGram.identityGram J, rfl, Or.inr ⟨rfl, h2, e, he, hact⟩⟩
end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.OuterFamilies.FourActors.CentralizerGeometry.InvertedOddSubgroup
