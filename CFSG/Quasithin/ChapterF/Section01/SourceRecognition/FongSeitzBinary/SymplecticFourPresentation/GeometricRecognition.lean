module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticFourPresentation.Recognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SymplecticFourPresentation.GeometricApplication

/-!
# Symplectic recognition of the actual universal geometric quotient

Compose the constructed root-preserving symplectic equivalence with the
existing geometric marking of the original amalgam. Local characteristic
two is transported from the actual endpoints by those same equivalences.
The left, middle, and right formulas retain the literal quotient map out
of the universal completion, and both original inclusion squares commute.
This identifies the finite quotient's marked amalgam; no descent from the
universal completion to a separate ambient group is claimed.

Source: DGS, Groups and Graphs, Theorem D, printed pp.224–226,
and its geometric quotient construction (3.6)–(3.7), pp.77–80.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.SymplecticFour.RootPresentation
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R]
variable (α : RankTwoAmalgam L B R) (T : Set (SourceVertex α)) (n : ℕ)
variable (hL : Function.Injective α.left) (hR : Function.Injective α.right)
variable (hbase : ∀ i, base (Universal.cosetFamily α) i ∈ T)
variable (hdeg : TwoNeighborsIn (sourceGraph α) T)
variable (htrans : BasedPathTransitive (X := α.Universal) (sourceGraph α) (n+1))
variable (hline : NoBranchingIn (sourceGraph α) T)
variable (hunique : ApartmentsUnique (X := α.Universal) (sourceGraph α) T (n+1))
variable (hexchange : ChosenApartmentExchange (X := α.Universal) (sourceGraph α) T n)
variable (hn : 1 < n)
variable (hcore : ((Universal.left α).range ⊓ (Universal.right α).range).normalCore = ⊥)
variable (d : RootQuotientData (quotientMap α T n))
variable (hB : d.B = originalMiddle α)
variable (hP : ∀ i, d.endpoint i = Universal.cosetFamily α i)
variable (hBN : d.B.map (quotientMap α T n) ⊓ d.N.map (quotientMap α T n) =
  (d.B ⊓ d.N).map (quotientMap α T n))

local notation "Q" => recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
  hexchange hn hcore d hB hP hBN

variable {F : Type*} [Field F]

variable [Finite F] [CharP F 2] [Finite L] [Finite R]
variable (hleft : Subgroup.centralizer (pCore 2 L : Set L) ≤ pCore 2 L)
variable (hright : Subgroup.centralizer (pCore 2 R : Set R) ≤ pCore 2 R)
local notation "e" => geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique
  hexchange hn hcore d hB hP hBN


include hleft hright in
private theorem geometric_c2_local_cores (i : Fin 2) :
    Subgroup.centralizer (pCore 2 ((Q).tits.standardParabolic {(Q).simple i}) :
      Set ((Q).tits.standardParabolic {(Q).simple i})) ≤
      pCore 2 ((Q).tits.standardParabolic {(Q).simple i}) := by
  fin_cases i
  · exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e).left).mp hleft
  · exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (e).right).mp hright

/-- Root recognition applied to the literal finite quotient of the universal
completion, with local characteristic two transported from its actual endpoints. -/
def geometric_c2_comparison (split : SplitData (Q).tits)
    (roots : C2Presentation.RootData (F := F) Q split) : RankTwoAmalgam.Iso α
      (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F) :=
  (e).trans (roots.markedIso (by
    exact geometric_c2_local_cores α T n hL hR hbase hdeg htrans hline
      hunique hexchange hn hcore d hB hP hBN hleft hright))

@[simp] theorem geometric_c2_comparison_left_apply (split : SplitData (Q).tits)
    (roots : C2Presentation.RootData (F := F) Q split) (a : L) :
    ((geometric_c2_comparison α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN hleft hright split roots).left a : Theory.SpecificGroups.SymplecticFour.Sp F) =
      roots.equiv (quotientMap α T n (Universal.left α a)) := by
  change roots.equiv ((e).left a : α.Universal ⧸ (Q).D) = _
  rw [geometricMarkedIso_left_apply]

/-- The entire original middle group follows the same universal quotient map. -/
@[simp] theorem geometric_c2_comparison_middle_apply (split : SplitData (Q).tits)
    (roots : C2Presentation.RootData (F := F) Q split) (b : B) :
    ((geometric_c2_comparison α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN hleft hright split roots).middle b : Theory.SpecificGroups.SymplecticFour.Sp F) =
      roots.equiv (quotientMap α T n (Universal.left α (α.left b))) := by
  change roots.equiv ((e).middle b : α.Universal ⧸ (Q).D) = _
  rw [geometricMarkedIso_middle_apply]

@[simp] theorem geometric_c2_comparison_right_apply (split : SplitData (Q).tits)
    (roots : C2Presentation.RootData (F := F) Q split) (a : R) :
    ((geometric_c2_comparison α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN hleft hright split roots).right a : Theory.SpecificGroups.SymplecticFour.Sp F) =
      roots.equiv (quotientMap α T n (Universal.right α a)) := by
  change roots.equiv ((e).right a : α.Universal ⧸ (Q).D) = _
  rw [geometricMarkedIso_right_apply]

/-- Both original inclusion squares use the same whole-Borel comparison. -/
theorem geometric_c2_comparison_squares (split : SplitData (Q).tits)
    (roots : C2Presentation.RootData (F := F) Q split) (b : B) :
    let c := geometric_c2_comparison α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN hleft hright split roots
    c.left (α.left b) = (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).left (c.middle b) ∧
    c.right (α.right b) = (CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).right (c.middle b) :=
  ⟨(geometric_c2_comparison α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
    d hB hP hBN hleft hright split roots).left_commutes b,
    (geometric_c2_comparison α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
    d hB hP hBN hleft hright split roots).right_commutes b⟩

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
