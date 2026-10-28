module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.GeometryTransfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.InnerFamilies.Centralizer.Residual
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LinearModels
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal.NormalTransfer
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.OddSections
public import Theory.SpecificGroups.SL2.ResidualTwoExtension
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# The actual prime-field centralizer quotient for the eight-actor branch

The residual Sylow supplement has solvable residual SL₂(F), equal to its
two-residual. Its radical is a two-group, and its radical quotient has
simple generalized Fitting subgroup PSL₂(F). The faithful prime-field
action identifies that quotient with PSL₂(F) or PGL₂(F).

For p > 5 the two existing concrete PSL₂/PGL₂ geometry contracts therefore
give E-generation of this literal quotient. Lifting through the radical
and the centralizer's solvable quotient, followed by matrix mixing, gives
escape for the original eight-actor family. The two model geometry inputs
and the nonsplit mixing input remain explicit. No K-group hypothesis or
classification of composition factors is added to the caller's contract.

Source: Aschbacher--Smith A.3.21(a), p.55, E.1.8, E.1.10 and E.1.14(6)--(7),
pp.210--214; Aschbacher (1982), Lemmas 4.10--4.11.
-/

public section
open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
open PSLTwoGeneration.PrimeGeometry
variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

local instance : Finite (PGL2 F) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

/-- The kernel, simple socle, actual model and Sylow supplement are all
properties of the literal residual-overgroup quotient. -/
theorem residual_quotient_structure
    (ho : Odd (Nat.card F)) (hl : 3 < Nat.card F)
    {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hzL : z ∈ innerPart F) (hz : orderOf z = 2)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) :
    let K := PSUThreeGeneration.centralizerResidualOvergroup T z
    let Q := K ⧸ solvableRadical K
    IsPGroup 2 (solvableRadical K) ∧ IsSimpleGroup (generalizedFitting Q) ∧
      Nonempty (generalizedFitting Q ≃* PSL2 F) ∧
      ∀ S : Sylow 2 Q, generalizedFitting Q ⊔ (S : Subgroup Q) = ⊤ := by
  obtain ⟨ec⟩ := inner_centralizer_residual_equiv F ho hl z hzL hz
  let e := (innerCentralizerSupplement_residualEquiv F hTz).trans ec
  exact Theory.SpecificGroups.SL2.ResidualTwoExtension.radical_quotient_structure
    ho hl e (innerCentralizerSupplement_pResidual_eq F hTz)

/-- The prime-field geometry is used on the two literal linear models.
All intrinsic E1 calculations, simple-socle structure and small actors
are discharged here; no SQTK catalogue premise is needed for this reduction. -/
theorem residual_quotient_isEGenerated_of_linear_geometry {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 5 < p) (hF : Nat.card F = p)
    (hinner : ∀ S : Sylow 2 (PSL2 F), ConcreteLocalGeometryAt S)
    (hdiagonal : ∀ S : Sylow 2 (PGL2 F), ConcreteLocalGeometryAt S)
    {T : Sylow 2 (graphExtension F)} {z : graphExtension F}
    (hzL : z ∈ innerPart F) (hz : orderOf z = 2)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) :
    let K := PSUThreeGeneration.centralizerResidualOvergroup T z
    IsEGenerated 1 (K ⧸ solvableRadical K) := by
  let K := PSUThreeGeneration.centralizerResidualOvergroup T z
  let Q := K ⧸ solvableRadical K
  obtain ⟨_, hs, ⟨e⟩, hS⟩ := residual_quotient_structure F (hF ▸ ho)
    (by omega) hzL hz hTz
  let _ : IsSimpleGroup (generalizedFitting Q) := hs
  let _ : Group.IsPerfect (PSL2 F) := psl2_isPerfect_of_card_gt_three F (by omega)
  let _ : Group.IsPerfect (generalizedFitting Q) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have ha : ¬ IsMulCommutative (generalizedFitting Q) :=
    Group.IsPerfect.not_isMulCommutative _
  have hC : centralizer (generalizedFitting Q : Set Q) = ⊥ :=
    SimpleSocle.centralizer_eq_bot ha
  have hcore : pCore 2 Q = ⊥ :=
    SimpleSocle.pCore_eq_bot (solvableRadical_quotient_solvableRadical (G := K)) 2
  have hq : IsOddPrimePower (Nat.card F) := ⟨p, 1, hp, ho, le_rfl, by simpa using hF⟩
  obtain hei | hed := linear_models_of_normal_prime_psl
    (generalizedFitting Q) hp ho hF hl e hC
  all_goals
    apply PSLTwoGeneration.isEGenerated_of_component_and_large_escape
      (fun S A _ _ hne => ValuesEvenClassical.RankOneUpper.eCaseComponent_top
        ha S (hS S) (S : Subgroup Q) A hne)
  · intro S
    let j : Q →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL.comp hei.some.toMonoidHom
    exact largeFamilyEscapeAt_of_concrete_localModels S hcore
      (kleinFour_selfCentralizing_of_embedding hq j
        (Matrix.ProjectiveSpecialLinearGroup.toPGL_injective.comp hei.some.injective))
      (Diagonal.concreteGeometry_of_equiv hei.some.symm hinner S)
  · intro S
    exact largeFamilyEscapeAt_of_concrete_localModels S hcore
      (kleinFour_selfCentralizing_of_embedding hq hed.some.toMonoidHom hed.some.injective)
      (Diagonal.concreteGeometry_of_equiv hed.some.symm hdiagonal S)

/-- For p > 5, the only remaining inputs are the existing two PSL₂ model
geometries and the existing odd-torus mixing construction. -/
theorem familyEscapes_of_positioned_eight_actor_of_prime_geometry {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hl : 5 < p) (hF : Nat.card F = p)
    (hinner : ∀ S : Sylow 2 (PSL2 F), ConcreteLocalGeometryAt S)
    (hdiagonal : ∀ S : Sylow 2 (PGL2 F), ConcreteLocalGeometryAt S)
    (hnonsplit : p % 4 = 3 → InnerGenerationGeometry.FourGroupOddMixing F)
    (T : Sylow 2 (graphExtension F)) (Ω : Set (Subgroup (graphExtension F)))
    (hΩ : IsElementaryFamily Ω) (hlarge : LargeActors F T Ω)
    (houter : ¬ HasInnerActor F T Ω) (M : Subgroup (graphExtension F))
    (hTM : (T : Subgroup _) ≤ M) (hM : M ≠ ⊤)
    (hN : normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M)
    (A : Subgroup (graphExtension F)) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup _))
    (hcard : Nat.card A = 8) (hfour : Nat.card (A ⊓ innerPart F : Subgroup _) = 4)
    (z : graphExtension F) (hz : orderOf z = 2) (hzL : z ∈ innerPart F) (hzA : z ∈ A)
    (hTz : (T : Subgroup _) ≤ centralizer ({z} : Set _)) : FamilyEscapes F T Ω M :=
  familyEscapes_of_residual_quotient_generation F
    (centralizerGeometry_of_residue_mixing F ho hF hnonsplit)
    T Ω hΩ hlarge houter M hTM hM hN A hA hAT hcard hfour z hz hzL hzA hTz
    (residual_quotient_isEGenerated_of_linear_geometry F hp ho hl hF
      hinner hdiagonal hzL hz hTz)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors
