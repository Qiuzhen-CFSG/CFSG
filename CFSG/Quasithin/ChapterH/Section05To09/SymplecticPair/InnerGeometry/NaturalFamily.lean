module

public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.InnerGeometry.NaturalFamily.Paired
public import CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair.InnerGeometry.NaturalFamily.RootCriterion
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.NaturalFamily.RootGeometry

/-!
# Native fixed-space families in H.7

In the standard Sylow, a natural-family member at parameter 2n lies in
the plane radical. Membership is equivalent to having relative corank 2n
over its intersection with every actual transvection root. The plane radical
attains the family, the next family is empty, and the natural parameter is 2n.

The concrete long-root geometry discharges both premises of `RootCriterion`:
roots fix more than the natural plane, and any radical subgroup fixing an
extra vector lies in such a root. The paired family at parameter 2n is empty
for the full symplectic group and its genuine derived subgroup, as proved in
`Paired`; both paired parameters are strictly below 2n.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.7,
printed pp.388–389.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- A natural-family member in the standard Sylow fixes exactly the natural plane. -/
theorem natural_family_fixedSpace {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {A : Subgroup (Sp F)} (hAU : A ≤ unipotent)
    (hA : A ∈ ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n)) :
    fixedSpace (binaryNatural (F := F)) A = (plane F).restrictScalars (ZMod 2) :=
  natural_family_fixedSpace_of_root_detection
    (fun _ => exists_sylowTransvectionRoot_of_fixedSpace_ne) hF hn hAU hA

/-- H.7's natural-family criterion, using the actual indices of
`A ∩ R` in `A` for every conjugate transvection root in the standard Sylow. -/
theorem natural_mem_iff {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n)
    {A : Subgroup (Sp F)} (hAU : A ≤ unipotent) :
    A ∈ ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n) ↔
      IsElementaryTwo A ∧ A ≤ planeRadical ∧
        ∀ R : Subgroup (Sp F), IsSylowTransvectionRoot R →
          Nat.log 2 ((A ⊓ R).relIndex A) = 2*n :=
  natural_mem_iff_of_root_geometry sylowTransvectionRoot_geometry
    (fun _ => exists_sylowTransvectionRoot_of_fixedSpace_ne) hF hn hAU

/-- The actual plane radical attains the natural family at parameter 2n. -/
theorem planeRadical_mem_natural_family {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) :
    planeRadical (F := F) ∈ ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n) :=
  planeRadical_mem_natural_family_of_root_geometry sylowTransvectionRoot_geometry
    (fun _ => exists_sylowTransvectionRoot_of_fixedSpace_ne) hF hn

/-- No elementary subgroup of the full symplectic group attains parameter 2n+1. -/
theorem natural_next_family_empty {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    ChapterE.fixedSpaceFamily (binaryNatural (F := F)) (2*n+1) = ∅ :=
  natural_next_family_empty_of_root_geometry sylowTransvectionRoot_geometry
    (fun _ => exists_sylowTransvectionRoot_of_fixedSpace_ne) hF hn

/-- The native natural symplectic module has parameter a = 2n. -/
theorem natural_moduleA_eq {n : ℕ} (hF : Nat.card F = 2^n) (hn : 0 < n) :
    ChapterE.moduleA (binaryNatural (F := F)) = (2*n : ℕ) :=
  natural_moduleA_eq_of_root_geometry sylowTransvectionRoot_geometry
    (fun _ => exists_sylowTransvectionRoot_of_fixedSpace_ne) hF hn

end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
