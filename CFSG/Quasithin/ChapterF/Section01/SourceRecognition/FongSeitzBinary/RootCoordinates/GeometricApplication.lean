module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.SimplePanels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.GeometricQuotient

/-!
# Root-coordinate counting on the geometric marked quotient

Apply the constructed dihedral coordinates and the split endpoint-index
recurrence to `GeometricQuotient.recognitionQuotient`, using its actual
`geometricMarkedIso`. Both indices are those of the original amalgam
structure maps. The universal completion may be infinite; only its
constructed quotient must be finite. No descent to a separately generated
source group and no perfect-factor assumption is introduced.

Source: DGS, *Groups and Graphs*, Part II, (3.6)–(3.7), pp.77–80 and
Theorem D, p.224; Carter §2.5.3–11 and rank-one Bruhat counting. The
constructed longest element supplies opposite Borel disjointness, simple
root coordinates and the root-order index formula. The same simple roots
give the literal punctured-panel charts. The general ordered-root recurrence
and marked Lie recognition remain separate steps.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
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

/-- The two original structure-map indices through the genuine geometric marking. -/
theorem geometric_split_endpoint_indices [Finite L] [Finite R]
    (split : SplitData (Q).tits) :
    α.left.range.index = 1 +
      ((split.U ⊓ unipotentConjugate split ((Q).simple 0)).subgroupOf split.U).index ∧
    α.right.range.index = 1 +
      ((split.U ⊓ unipotentConjugate split ((Q).simple 1)).subgroupOf split.U).index :=
  marked_amalgam_indices Q split
    (geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore
      d hB hP hBN)

/-- The constructed dihedral coordinates on the finite quotient of the universal carrier. -/
theorem geometric_marked_dihedral_coordinates [Finite L] [Finite R] :
    2 ≤ rotationOrder Q ∧
      weylEquiv Q ((Q).simple 0) = DihedralGroup.sr 0 ∧
      weylEquiv Q ((Q).simple 1) = DihedralGroup.sr 1 ∧
      Nat.card (Weyl Q) = 2 * rotationOrder Q :=
  ⟨rotationOrder_ge_two Q, weylEquiv_simple_zero Q, weylEquiv_simple_one Q, weyl_card Q⟩

/-- Exact simple-root orders count the original amalgam's full overlap inclusions. -/
theorem geometric_simpleRoot_endpoint_indices [Finite L] [Finite R]
    (split : SplitData (Q).tits) :
    α.left.range.index = 1 + Nat.card (simpleRoot Q split 0) ∧
    α.right.range.index = 1 + Nat.card (simpleRoot Q split 1) := by
  have h := geometric_split_endpoint_indices α T n hL hR hbase hdeg htrans hline hunique
    hexchange hn hcore d hB hP hBN split
  change α.left.range.index = 1 + ((simpleRemainder Q split 0).subgroupOf split.U).index ∧
    α.right.range.index = 1 + ((simpleRemainder Q split 1).subgroupOf split.U).index at h
  rwa [simpleRemainder_index, simpleRemainder_index] at h

/-- Opposite disjointness on the same finite quotient of the universal carrier. -/
theorem geometric_split_opposite [Finite L] [Finite R] (split : SplitData (Q).tits) :
    (Q).tits.B ⊓ borelConjugate (longest Q) = (Q).tits.B ⊓ (Q).tits.N ∧
    (Q).tits.B ⊓ unipotentConjugate split (longest Q) = ⊥ :=
  ⟨borel_inf_opposite Q split, borel_inf_opposite_unipotent Q split⟩

/-- The same roots and original B,N give actual bijective panel charts. -/
theorem geometric_simpleRoot_panel [Finite L] [Finite R] (split : SplitData (Q).tits)
    (i : Fin 2) (ni : (Q).tits.N)
    (hni : QuotientGroup.mk' (((Q).tits.B ⊓ (Q).tits.N).subgroupOf (Q).tits.N) ni = (Q).simple i) :
    simpleRoot Q split i ≠ ⊥ ∧ simpleRoot Q split i ≤ split.U ∧
      (Q).tits.B ⊓ (Q).tits.N ≤ Subgroup.normalizer (simpleRoot Q split i : Set _) ∧
      Function.Bijective (simplePanelMap Q split i ni hni) :=
  ⟨simpleRoot_ne_bot Q split i, simpleRoot_le Q split i,
    torus_normalizes_simpleRoot Q split i, simplePanelMap_bijective Q split i ni hni⟩

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
