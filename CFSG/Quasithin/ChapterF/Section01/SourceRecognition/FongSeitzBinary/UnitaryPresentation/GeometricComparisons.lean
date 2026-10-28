module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryPresentation.ProjectiveMarkings
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.RootCoordinates.GeometricApplication
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.Irreducibility
public import Theory.Quasithin.EvenCharacteristic

/-!
# Unitary comparisons for the geometric universal quotient

The projective unitary equivalence restricts to the original endpoints and
their full overlap through `geometricMarkedIso`. All three maps use the same
literal `quotientMap` of the universal completion, in either orientation.
Local characteristic two kills the source center for the general-q U₅
scalar descent. Source equations and generation remain explicit inputs.
Source: DGS, Groups and Graphs, Theorem D, printed p.224 and (15.2),
pp.226–228; Aschbacher–Smith F.1.12, printed pp.263–264.
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

variable {E : Type*} [Field E]

variable [Finite E] [CharP E 2] [Finite L] [Finite R]
variable (hleft : Subgroup.centralizer (pCore 2 L : Set L) ≤ pCore 2 L)
local notation "e" => geometricMarkedIso α T n hL hR hbase hdeg htrans hline hunique
  hexchange hn hcore d hB hP hBN
include hleft in
theorem geometric_unitary_center (split : SplitData (Q).tits) :
    Subgroup.center (α.Universal ⧸ (Q).D)=⊥ := by
  apply split.center_eq_bot_of_borel_core
  have hc : Subgroup.centralizer (pCore 2 ((Q).tits.standardParabolic {(Q).simple 0}) :
      Set ((Q).tits.standardParabolic {(Q).simple 0})) ≤
      pCore 2 ((Q).tits.standardParabolic {(Q).simple 0}) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 (e).left).mp hleft
  exact le_bot_iff.mp ((Q).parabolic_normalCore_eq_bot split 0 hc ▸
    Subgroup.normalCore_mono ((Q).tits.B_le_standardParabolic {(Q).simple 0}))

section Four
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag

def geometric_unitaryFour_comparison {i : Fin 2} (hrot : rotationOrder Q=4)
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (split : SplitData (Q).tits) (roots : FourData Q split i σ hσ) : RankTwoAmalgam.Iso α
    (MarkedAmalgam.flag ((pointParabolicSU E (form E σ hσ)).map (project E (form E σ hσ)))
      ((planeParabolicSU E (form E σ hσ)).map (project E (form E σ hσ))) i) :=
  (e).trans (roots.markedIso σ hσ hrot)

@[simp] theorem geometric_unitaryFour_left {i : Fin 2} (hrot : rotationOrder Q=4)
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (split : SplitData (Q).tits) (roots : FourData Q split i σ hσ) (a : L) :
    ((geometric_unitaryFour_comparison α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN hrot σ hσ split roots).left a : PSU E (form E σ hσ))=
      (roots.projectiveEquiv σ hσ hrot).symm (quotientMap α T n (Universal.left α a)) := by
  change (roots.projectiveEquiv σ hσ hrot).symm ((e).left a : α.Universal ⧸ (Q).D)=_
  rw [geometricMarkedIso_left_apply]

@[simp] theorem geometric_unitaryFour_middle {i : Fin 2} (hrot : rotationOrder Q=4)
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (split : SplitData (Q).tits) (roots : FourData Q split i σ hσ) (b : B) :
    ((geometric_unitaryFour_comparison α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN hrot σ hσ split roots).middle b : PSU E (form E σ hσ))=
      (roots.projectiveEquiv σ hσ hrot).symm (quotientMap α T n (Universal.left α (α.left b))) := by
  change (roots.projectiveEquiv σ hσ hrot).symm ((e).middle b : α.Universal ⧸ (Q).D)=_
  rw [geometricMarkedIso_middle_apply]

@[simp] theorem geometric_unitaryFour_right {i : Fin 2} (hrot : rotationOrder Q=4)
    (σ : E ≃+* E) (hσ : Function.Involutive σ)
    (split : SplitData (Q).tits) (roots : FourData Q split i σ hσ) (a : R) :
    ((geometric_unitaryFour_comparison α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN hrot σ hσ split roots).right a : PSU E (form E σ hσ))=
      (roots.projectiveEquiv σ hσ hrot).symm (quotientMap α T n (Universal.right α a)) := by
  change (roots.projectiveEquiv σ hσ hrot).symm ((e).right a : α.Universal ⧸ (Q).D)=_
  rw [geometricMarkedIso_right_apply]
end Four

section Five
open Theory.SpecificGroups.UnitaryFive

local notation "hZ" => geometric_unitary_center α T n hL hR hbase hdeg htrans hline hunique
  hexchange hn hcore d hB hP hBN hleft

def geometric_unitaryFive_comparison {i : Fin 2} (hrot : rotationOrder Q=4)
    (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
    (split : SplitData (Q).tits) (roots : FiveData Q split i J) : RankTwoAmalgam.Iso α
    (MarkedAmalgam.flag (lineParabolic J) (planeParabolic J) i) :=
  (e).trans (roots.markedIso J κ hκ hJ hrot (hZ split))

@[simp] theorem geometric_unitaryFive_left {i : Fin 2} (hrot : rotationOrder Q=4)
    (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
    (split : SplitData (Q).tits) (roots : FiveData Q split i J) (a : L) :
    ((geometric_unitaryFive_comparison α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN hleft hrot J κ hκ hJ split roots).left a :
        ProjectiveSpecialUnitaryMatrixGroup J)=
      (roots.projectiveEquiv J κ hκ hJ hrot (hZ split)).symm (quotientMap α T n (Universal.left α a)) := by
  change (roots.projectiveEquiv J κ hκ hJ hrot (hZ split)).symm ((e).left a : α.Universal ⧸ (Q).D)=_
  rw [geometricMarkedIso_left_apply]

@[simp] theorem geometric_unitaryFive_middle {i : Fin 2} (hrot : rotationOrder Q=4)
    (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
    (split : SplitData (Q).tits) (roots : FiveData Q split i J) (b : B) :
    ((geometric_unitaryFive_comparison α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN hleft hrot J κ hκ hJ split roots).middle b :
        ProjectiveSpecialUnitaryMatrixGroup J)=
      (roots.projectiveEquiv J κ hκ hJ hrot (hZ split)).symm
        (quotientMap α T n (Universal.left α (α.left b))) := by
  change (roots.projectiveEquiv J κ hκ hJ hrot (hZ split)).symm ((e).middle b : α.Universal ⧸ (Q).D)=_
  rw [geometricMarkedIso_middle_apply]

@[simp] theorem geometric_unitaryFive_right {i : Fin 2} (hrot : rotationOrder Q=4)
    (J : HermitianForm 5 E) (κ : E) (hκ : κ+J.conj κ=1) (hJ : J.form=1)
    (split : SplitData (Q).tits) (roots : FiveData Q split i J) (a : R) :
    ((geometric_unitaryFive_comparison α T n hL hR hbase hdeg htrans hline hunique
      hexchange hn hcore d hB hP hBN hleft hrot J κ hκ hJ split roots).right a :
        ProjectiveSpecialUnitaryMatrixGroup J)=
      (roots.projectiveEquiv J κ hκ hJ hrot (hZ split)).symm (quotientMap α T n (Universal.right α a)) := by
  change (roots.projectiveEquiv J κ hκ hJ hrot (hZ split)).symm ((e).right a : α.Universal ⧸ (Q).D)=_
  rw [geometricMarkedIso_right_apply]
end Five
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
