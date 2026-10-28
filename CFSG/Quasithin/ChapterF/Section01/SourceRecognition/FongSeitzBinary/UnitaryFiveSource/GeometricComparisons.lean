module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryFiveSource.SourceComparisons

/-!
# The constructed U₅ source on a marked geometric quotient

The earlier profile is carried on a marked quotient through an arbitrary
`RankTwoAmalgam.Iso`. The comparison keeps one projective equivalence for the
whole Borel and all three flag factors. The concrete apartment specialization
constructs `geometricMarkedIso` and proves all three literal universal
`quotientMap` equations without an additional quotient equivalence.
Source: Fong--Seitz II (8C), pp.202–210; DGS (15.2), pp.226–228.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Subgroup Subgroup.CosetGeometry RankTwoAmalgam
open Theory.SpecificGroups.UnitaryFive
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitaryFiveSource
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryFiveSource
open UnitarySource.Combined
open CFSG.Quasithin.ChapterF.Source
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

section GeometricProfile

variable {G K E : Type*} [Group G] [Field K] [Finite K] [CharP K 2]
  [Field E] [Finite E] [CharP E 2]
  {L₀ : Fin 2 → Subgroup G} {S : Subgroup G}
  {Q : MarkedQuotient (recognitionEndpoints α)}
  (split : SplitData Q.tits)
  (mark : Iso (RankTwoAmalgam.ofSubgroups (parabolic L₀ S 0)
    (parabolic L₀ S 0 ⊓ parabolic L₀ S 1) (parabolic L₀ S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L₀ S) (hm : rotationOrder Q = 4)
  (m : ℕ) (hmpos : 0 < m) (i j : Fin 2) (hij : i ≠ j)
  (p : FiveProfile L₀ S Q split K E m i j)
  (other : Iso α Q.standardAmalgam)

include mark h hm hmpos hij p other in
/-- The source profile gives a projective model on one marked geometric
quotient. Its three flag maps are all transported by the supplied marking. -/
theorem geometric_unitaryFive_source_comparison :
    ∃ (M : CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model (2^m))
      (f : M.Carrier ≃* (α.Universal ⧸ Q.D))
      (c : Iso α (MarkedAmalgam.flag M.leftParabolic M.rightParabolic j)),
      M.overlap.map f.toMonoidHom = Q.tits.B ∧
      (∀ a : L, (c.left a : M.Carrier) =
        f.symm (other.left a : α.Universal ⧸ Q.D)) ∧
      (∀ b : B, (c.middle b : M.Carrier) =
        f.symm (other.middle b : α.Universal ⧸ Q.D)) ∧
      (∀ a : R, (c.right a : M.Carrier) =
        f.symm (other.right a : α.Universal ⧸ Q.D)) := by
  obtain ⟨M,f,c,hBorel,hleft',hmiddle',hright'⟩ :=
    profile_model_other_comparison Q split mark h hm m hmpos i j hij p α other
  refine ⟨M,f,c,hBorel,?_,?_,?_⟩
  · intro a
    exact hleft' a
  · intro b
    exact hmiddle' b
  · intro a
    exact hright' a

include mark h hm hmpos hij p other in
/-- Transport the marked comparison across a supplied quotient equivalence.
The conclusion keeps the literal universal `quotientMap` in all three
geometric squares while leaving the quotient equivalence explicit. -/
theorem geometric_unitaryFive_source_comparison_quotientMap
    (q : (α.Universal ⧸ Q.D) ≃* QuotientGroup α T n)
    (hqleft : ∀ a : L, q (other.left a : α.Universal ⧸ Q.D) =
      quotientMap α T n (Universal.left α a))
    (hqmiddle : ∀ b : B, q (other.middle b : α.Universal ⧸ Q.D) =
      quotientMap α T n (Universal.left α (α.left b)))
    (hqright : ∀ a : R, q (other.right a : α.Universal ⧸ Q.D) =
      quotientMap α T n (Universal.right α a)) :
    ∃ (M : CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model (2^m))
      (f : M.Carrier ≃* (α.Universal ⧸ Q.D))
      (c : Iso α (MarkedAmalgam.flag M.leftParabolic M.rightParabolic j)),
      M.overlap.map f.toMonoidHom = Q.tits.B ∧
      (∀ a : L, q (f (c.left a : M.Carrier)) =
        quotientMap α T n (Universal.left α a)) ∧
      (∀ b : B, q (f (c.middle b : M.Carrier)) =
        quotientMap α T n (Universal.left α (α.left b))) ∧
      (∀ a : R, q (f (c.right a : M.Carrier)) =
        quotientMap α T n (Universal.right α a)) := by
  obtain ⟨M, f, c, hBorel, hleft, hmiddle, hright⟩ :=
    geometric_unitaryFive_source_comparison (α := α) split mark h hm m hmpos i j hij p other
  refine ⟨M, f, c, hBorel, ?_, ?_, ?_⟩
  · intro a
    calc
      q (f (c.left a : M.Carrier)) = q (other.left a : α.Universal ⧸ Q.D) := by
        rw [hleft a]
        simp
      _ = quotientMap α T n (Universal.left α a) := hqleft a
  · intro b
    calc
      q (f (c.middle b : M.Carrier)) = q (other.middle b : α.Universal ⧸ Q.D) := by
        rw [hmiddle b]
        simp
      _ = quotientMap α T n (Universal.left α (α.left b)) := hqmiddle b
  · intro a
    calc
      q (f (c.right a : M.Carrier)) = q (other.right a : α.Universal ⧸ Q.D) := by
        rw [hright a]
        simp
      _ = quotientMap α T n (Universal.right α a) := hqright a

end GeometricProfile

section ConcreteGeometricProfile

-- Keep the concrete quotient explicit in section-variable types: notation
-- expanding section parameters here can lose their dependency bindings.
variable [Finite L] [Finite R]
variable {G K E : Type*} [Group G] [Field K] [Finite K] [CharP K 2]
  [Field E] [Finite E] [CharP E 2]
  {L₀ : Fin 2 → Subgroup G} {S : Subgroup G}
  (split : SplitData (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN).tits)
  (mark : Iso (RankTwoAmalgam.ofSubgroups (parabolic L₀ S 0)
    (parabolic L₀ S 0 ⊓ parabolic L₀ S 1) (parabolic L₀ S 1) inf_le_left inf_le_right)
    (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN).standardAmalgam)
  (h : HypothesisF11 L₀ S) (hm : rotationOrder (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN) = 4)
  (m : ℕ) (hmpos : 0 < m) (i j : Fin 2) (hij : i ≠ j)
  (p : FiveProfile L₀ S (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN) split K E m i j)

include mark h hm hmpos hij p in
/-- The actual apartment quotient carries the constructed U₅ model, with
both endpoints and the full overlap mapped by the literal universal quotient.
The geometric marking and its three squares are constructed, not assumed. -/
theorem geometric_unitaryFive_source_comparison_concrete :
    ∃ (M : CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model (2^m))
      (f : M.Carrier ≃* (α.Universal ⧸ (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN).D))
      (c : Iso α (MarkedAmalgam.flag M.leftParabolic M.rightParabolic j)),
      M.overlap.map f.toMonoidHom = (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN).tits.B ∧
      (∀ a : L, (c.left a : M.Carrier) =
        f.symm (quotientMap α T n (Universal.left α a))) ∧
      (∀ b : B, (c.middle b : M.Carrier) =
        f.symm (quotientMap α T n (Universal.left α (α.left b)))) ∧
      (∀ a : R, (c.right a : M.Carrier) =
        f.symm (quotientMap α T n (Universal.right α a))) := by
  let other : Iso α (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN).standardAmalgam :=
    geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN
  obtain ⟨M,f,c,hBorel,hleft',hmiddle',hright'⟩ :=
    profile_model_other_comparison
      (G := G) (X := α.Universal) (K := K) (E := E)
      (L := L₀) (S := S) (P := recognitionEndpoints α)
      (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN) split mark h hm m hmpos i j hij p α other
  refine ⟨M,f,c,hBorel,?_,?_,?_⟩
  · intro a
    exact (hleft' a).trans (congrArg f.symm
      (geometricMarkedIso_left_apply α T n hL hR hbase hdeg htrans hline hunique
        hexchange hn hcore d hB hP hBN a))
  · intro b
    exact (hmiddle' b).trans (congrArg f.symm
      (geometricMarkedIso_middle_apply α T n hL hR hbase hdeg htrans hline hunique
        hexchange hn hcore d hB hP hBN b))
  · intro a
    exact (hright' a).trans (congrArg f.symm
      (geometricMarkedIso_right_apply α T n hL hR hbase hdeg htrans hline hunique
        hexchange hn hcore d hB hP hBN a))

end ConcreteGeometricProfile

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
