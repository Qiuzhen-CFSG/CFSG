module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitarySource.TensorEquationApplication
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.GeometricComparisons

/-!
# U₄ source recognition on the geometric universal quotient

Compose the original-parabolic marking with geometricMarkedIso and
construct the complete FourData there. The projective comparison then
restricts to both full endpoints and their overlap using the literal
universal quotientMap in all three formulas. Only the endpoints are
assumed finite; the universal completion may be infinite.
The earlier quadratic profile and remainder containments stay explicit.
Source: DGS Theorem D, p.224 and (15.2), pp.226--228;
Fong--Seitz I (6A)(b), pp.37--38, and II (8B), pp.201--202.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open Theory.GroupTheory Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitaryPresentation
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Subgroup.CosetGeometry RankTwoAmalgam
universe u
variable {L B R : Type u} [Group L] [Group B] [Group R] [Finite L] [Finite R]
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

open Subgroup
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary
open CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.UnitarySource
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Representation.OrthogonalFourMinus.FiniteModel
variable {G F k : Type*} [Group G]
  [Field F] [Finite F] [CharP F 2] [Field k] [Finite k] [CharP k 2]
  {J : Fin 2 → Subgroup G} {S : Subgroup G}
  (sourceMark : Iso
    (RankTwoAmalgam.ofSubgroups (parabolic J S 0)
      (parabolic J S 0 ⊓ parabolic J S 1) (parabolic J S 1) inf_le_left inf_le_right) α)
  (h : HypothesisF11 J S) (split : SplitData ((recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN)).tits)
  (hm : rotationOrder (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN) = 4) (i j : Fin 2) (hij : i ≠ j)
  (hVi : simpleRemainder (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN) split i ≤ localKernel (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN) i)
  (hVj : simpleRemainder (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN) split j ≤ localKernel (recognitionQuotient α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN) j)
  (fi : (S ⊔ J i).subgroupOf (parabolic J S i) →* SL(2,F))
  (fj : (S ⊔ J j).subgroupOf (parabolic J S j) →* SL(2,k))
  (hfi : Function.Surjective fi) (hfj : Function.Surjective fj)
  (hki : fi.ker = (pCore 2 (parabolic J S i)).subgroupOf ((S ⊔ J i).subgroupOf (parabolic J S i)))
  (hkj : fj.ker = (pCore 2 (parabolic J S j)).subgroupOf ((S ⊔ J j).subgroupOf (parabolic J S j)))
  (hfields : Nat.card F = Nat.card k ^ 2)
  (hindexi : (commonBorel J S).relIndex (parabolic J S i) = Nat.card F + 1)
  (hindexj : (commonBorel J S).relIndex (parabolic J S j) = Nat.card k + 1)
  (helem : IsElementaryAbelian 2 ((parabolic J S i).pCoreIn 2))
  (hQi : letI := QuadrangleStructure.original_core_normal_in_sylow (L := J) (S := S) i
    IsElementaryAbelian 2 (S ⧸ ((parabolic J S i).pCoreIn 2).subgroupOf S))
  (hQj : letI := QuadrangleStructure.original_core_normal_in_sylow (L := J) (S := S) j
    IsElementaryAbelian 2 (S ⧸ ((parabolic J S j).pCoreIn 2).subgroupOf S))
  (hne : ⁅(parabolic J S j).pCoreIn 2,(parabolic J S j).pCoreIn 2⁆ ≠ ⊥)
  (m : ℕ) [NeZero m] (hk : Nat.card k = 2^m)

include sourceMark h hm hij hVi hVj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne hk in
/-- Source reconstruction on the geometric universal quotient, with all
three literal quotientMap formulas and the full endpoint/overlap marking. -/
theorem geometric_quadratic_unitaryFour_comparison :
    ∃ (eqv : PSU (Field m) (form (Field m) (conjugation m) (conjugation_involutive m)) ≃* (α.Universal ⧸ (Q).D))
      (c : Iso α (MarkedAmalgam.flag
        ((pointParabolicSU (Field m) (form (Field m) (conjugation m) (conjugation_involutive m))).map
          (project (Field m) (form (Field m) (conjugation m) (conjugation_involutive m))))
        ((planeParabolicSU (Field m) (form (Field m) (conjugation m) (conjugation_involutive m))).map
          (project (Field m) (form (Field m) (conjugation m) (conjugation_involutive m)))) j)),
      (∀ a : L, (c.left a : PSU (Field m) (form (Field m) (conjugation m) (conjugation_involutive m))) =
        eqv.symm (quotientMap α T n (Universal.left α a))) ∧
      (∀ a : B, (c.middle a : PSU (Field m) (form (Field m) (conjugation m) (conjugation_involutive m))) =
        eqv.symm (quotientMap α T n (Universal.left α (α.left a)))) ∧
      (∀ a : R, (c.right a : PSU (Field m) (form (Field m) (conjugation m) (conjugation_involutive m))) =
        eqv.symm (quotientMap α T n (Universal.right α a))) := by
  let mark := geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN
  obtain ⟨roots,_⟩ := marked_quadratic_fourData
    (G := G) (X := α.Universal) (F := F) (k := k) (L := J) (S := S)
    (P := recognitionEndpoints α) (Q) (sourceMark.trans mark) h split hm i j hij
    hVi hVj fi fj hfi hfj hki hkj hfields hindexi hindexj helem hQi hQj hne m hk
  refine ⟨roots.projectiveEquiv (conjugation m) (conjugation_involutive m) hm,
    geometric_unitaryFour_comparison α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN
      hm (conjugation m) (conjugation_involutive m) split roots,?_,?_,?_⟩
  · exact geometric_unitaryFour_left α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN
      hm (conjugation m) (conjugation_involutive m) split roots
  · exact geometric_unitaryFour_middle α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN
      hm (conjugation m) (conjugation_involutive m) split roots
  · exact geometric_unitaryFour_right α T n hL hR hbase hdeg htrans hline hunique hexchange hn hcore d hB hP hBN
      hm (conjugation m) (conjugation_involutive m) split roots

end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
