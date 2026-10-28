module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2Presentation.Input
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.GeometricQuotient

/-!
# C₂ relations on the literal geometric quotient

The presented C₂ group maps onto the exact finite quotient constructed from
the universal completion. Its positive subgroup has the supplied split U
as image, so every element of that U has four-root coordinates. The same
rank-two marking internally supplies the order-greater-than-two condition.
These are applications of the explicit root contract, not a recognition of
the quotient as Sp₄. No descent to a separate ambient source group occurs.

Source: DGS, Theorem D, printed p.224, after the geometric quotient
construction (3.6)–(3.7), pp.77–80; Steinberg §6, pp.68–74.
-/

public noncomputable section
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

/-- The same geometric quotient, not a replacement model or family tag. -/
theorem geometric_c2_presentation_surjective [Finite L] [Finite R]
    (split : SplitData (Q).tits) (roots : C2Presentation.RootData (F := F) Q split) :
    Function.Surjective roots.presentationMap := roots.presentationMap_surjective

variable [Finite F] [CharP F 2]

/-- Positive collection on the literal quotient of the universal completion. -/
theorem geometric_c2_positive_normal_form [Finite L] [Finite R]
    (split : SplitData (Q).tits) (roots : C2Presentation.RootData (F := F) Q split)
    (g : α.Universal ⧸ (Q).D) (hg : g ∈ split.U) :
    ∃ b k w v : F, roots.x 6 (.ofAdd b) * roots.x 0 (.ofAdd k) *
      roots.x 4 (.ofAdd w) * roots.x 2 (.ofAdd v) = g :=
  roots.positive_normal_form g hg

/-- Marked rank two discharges the small nondegeneracy premise internally. -/
theorem geometric_c2_two_lt_card [Finite L] [Finite R] :
    2 < Nat.card (α.Universal ⧸ (Q).D) := C2Presentation.two_lt_card Q

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
