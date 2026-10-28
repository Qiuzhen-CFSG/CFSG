module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.GeometricApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.BruhatCoordinates
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderedProducts
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.RootCoordinates.OrderFormulas

/-!
# Ordered-root coordinates on the universal-completion quotient

The finite geometric recognition quotient has the same two panel roots,
unique refined Bruhat coordinates and unique ordered positive-root
coordinates. Its normal-subgroup generation lemma retains the whole
quotient. The numerical formulas use the original amalgam's two structure
map indices through geometricMarkedIso and the entire original overlap.
The universal completion itself may be infinite. No map to the separately
generated original J or perfectness assumption is required.

Sources: Carter 2.5.10–2.5.17, `refs/KGroup/GLS3/Chapter2Ca2.tex`;
DGS, *Groups and Graphs*, Part II, (3.6)–(3.7) and Theorem D.
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

/-- Unique refined Bruhat coordinates on the same geometric marked quotient. -/
theorem geometric_bruhat_unique [Finite L] [Finite R] (split : SplitData (Q).tits)
    (w : Weyl Q) (nw : (Q).tits.N)
    (hw : QuotientGroup.mk' (((Q).tits.B ⊓ (Q).tits.N).subgroupOf (Q).tits.N) nw = w)
    (x : α.Universal ⧸ (Q).D) (hx : x ∈ (Q).tits.bruhatCell w) :
    ∃! p : (Q).tits.B × rootIntersection split (longest Q) w,
      (p.1 : α.Universal ⧸ (Q).D)*nw*p.2 = x := by
  let e := bruhatCoordinates Q split w nw hw
  let z : (Q).tits.bruhatCell w := ⟨x,hx⟩
  refine ⟨e.symm z, ?_, ?_⟩
  · exact (bruhatCoordinates_apply Q split w nw hw (e.symm z).1 (e.symm z).2).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply z))
  · intro p hp
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext ((bruhatCoordinates_apply Q split w nw hw p.1 p.2).trans hp)

/-- The positive factors are conjugates of the same two panel roots, inside the same U. -/
theorem geometric_positive_factors [Finite L] [Finite R] (split : SplitData (Q).tits)
    (b : Bool) (A : Subgroup (α.Universal ⧸ (Q).D))
    (hA : A ∈ orderedRoots Q split b (rotationOrder Q)) :
    ∃ i : Fin 2, ∃ ni : (Q).tits.N,
      A = rightConjugate (simpleRoot Q split i) (ni : α.Universal ⧸ (Q).D) ∧
      A ≤ split.U ∧ (Q).tits.B ⊓ (Q).tits.N ≤ Subgroup.normalizer (A : Set _) := by
  obtain ⟨i,ni,he⟩ := orderedRoots_are_simple_conjugates Q split b _ A hA
  have hle := orderedRoots_le Q split b _ le_rfl A hA
  rw [alternatingWord_longest, longest_inv, rootIntersection_longest] at hle
  exact ⟨i,ni,he,hle,orderedRoots_torus_normalizes Q split b _ A hA⟩

/-- Literal ordered multiplication gives unique coordinates on the geometric U. -/
theorem geometric_unipotent_ordered_unique [Finite L] [Finite R] (split : SplitData (Q).tits)
    (b : Bool) (x : split.U) :
    ∃! p : RootTuple (orderedRoots Q split b (rotationOrder Q)),
      rootProduct (orderedRoots Q split b (rotationOrder Q)) p = (x : α.Universal ⧸ (Q).D) := by
  let e := unipotentOrderedCoordinates Q split b
  refine ⟨e.symm x, ?_, ?_⟩
  · exact (unipotentOrderedCoordinates_apply Q split b (e.symm x)).symm.trans
      (congrArg Subtype.val (e.apply_symm_apply x))
  · intro p hp
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext ((unipotentOrderedCoordinates_apply Q split b p).trans hp)

/-- Root containment in a normal subgroup propagates to the whole geometric U. -/
theorem geometric_unipotent_le_normal_of_simpleRoots_le [Finite L] [Finite R]
    (split : SplitData (Q).tits) (K : Subgroup (α.Universal ⧸ (Q).D)) [K.Normal]
    (hK : ∀ i, simpleRoot Q split i ≤ K) : split.U ≤ K :=
  unipotent_le_normal_of_simpleRoots_le Q split K hK

/-- Odd m equates the actual two amalgam indices, with the full original middle. -/
theorem geometric_endpoint_indices_eq_of_odd [Finite L] [Finite R]
    (split : SplitData (Q).tits) (hm : Odd (rotationOrder Q)) :
    α.left.range.index = α.right.range.index := by
  have hi := geometric_simpleRoot_endpoint_indices α T n hL hR hbase hdeg htrans hline hunique
    hexchange hn hcore d hB hP hBN split
  rw [hi.1,hi.2,simpleRoot_card_eq_of_odd Q split hm]

/-- Even-parameter U order in the literal original amalgam indices. -/
theorem geometric_unipotent_card_even [Finite L] [Finite R] (split : SplitData (Q).tits)
    (k : ℕ) (hm : rotationOrder Q = 2*k) :
    Nat.card split.U = ((α.left.range.index-1)*(α.right.range.index-1))^k := by
  have hi := geometric_simpleRoot_endpoint_indices α T n hL hR hbase hdeg htrans hline hunique
    hexchange hn hcore d hB hP hBN split
  rw [hi.1,hi.2]
  simpa only [Nat.add_sub_cancel_left] using unipotent_card_even Q split k hm

/-- Odd-parameter U order in the literal original amalgam index. -/
theorem geometric_unipotent_card_odd [Finite L] [Finite R] (split : SplitData (Q).tits)
    (hm : Odd (rotationOrder Q)) :
    Nat.card split.U = (α.left.range.index-1)^rotationOrder Q := by
  have hi := geometric_simpleRoot_endpoint_indices α T n hL hR hbase hdeg htrans hline hunique
    hexchange hn hcore d hB hP hBN split
  rw [hi.1]
  simpa only [Nat.add_sub_cancel_left] using unipotent_card_odd_pow Q split hm

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
