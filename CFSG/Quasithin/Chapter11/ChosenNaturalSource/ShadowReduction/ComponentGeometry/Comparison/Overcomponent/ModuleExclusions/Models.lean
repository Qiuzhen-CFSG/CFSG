module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Embeddings
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.Classification.CentralQuotients
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.FixedHeptad
public import Theory.SpecificGroups.Janko4.Model.Center
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import BenderSuzuki.External.Huppert.II.theorem_10_13

/-!
# Negative comparisons for all six proper-overcomponent pairs

The larger two-core quotients are M23, J4, or odd prime linear/unitary
three-dimensional groups. The B.4/B.5 central-quotient restrictions exclude
each one. In the special linear and special unitary rows, the proof passes
through the actual projective quotient and retains the covering center.

ModuleExclusions applies this comparison to the original chosen seed,
its marked doubled orbit, and the orthogonal-minus alternative. This does
not derive the proper-embedding shortlist from A.3.12.
Source: Aschbacher--Smith 11.4.2, printed p.776, using B.4.2 and B.5.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
open Quasisimple.Classification Chapter1.Section02.LocalModels

private def centerlessTargetEquiv {A B : Type*} [Group A] [Group B]
    [IsQuasisimple A] [Nontrivial B]
    (f : A →* B) (hf : Function.Surjective f) (hz : center B = ⊥) :
    (A ⧸ center A) ≃* B :=
  (IsQuasisimple.centralQuotientEquiv f hf).trans
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot)

private theorem not_sporadic {A B : Type*} [Group A] [Group B]
    [IsQuasisimple A] (h : CentralQuotientRestrictions (A ⧸ center A))
    (e : A ≃* B) (hz : center B = ⊥)
    (hm : ChapterA.Section02.IsTheoremCSporadicModel B) : False := by
  let : IsSimpleGroup (A ⧸ center A) := IsQuasisimple.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  let : Nontrivial B := e.injective.nontrivial
  exact h.not_sporadic (hm.of_mulEquiv
    (centerlessTargetEquiv e.toMonoidHom e.surjective hz))

private theorem not_linear {A : Type*} [Group A] [IsQuasisimple A]
    (h : CentralQuotientRestrictions (A ⧸ center A))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL A 3 p ∨ Source.IsSL A 3 p) : False := by
  apply h.not_odd_psl3 p hp ho
  rcases hm with hm | hm
  · obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    exact ⟨F,inferInstance,inferInstance,hc,⟨centerlessTargetEquiv e.toMonoidHom e.surjective
      (Group.IsPerfect.center_quotient_center_eq_bot _)⟩⟩
  · obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let f := (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) F))).comp e.toMonoidHom
    exact ⟨F,inferInstance,inferInstance,hc,⟨centerlessTargetEquiv f
      ((QuotientGroup.mk'_surjective _).comp e.surjective)
      (Group.IsPerfect.center_quotient_center_eq_bot _)⟩⟩

private theorem psu_prime_simple {F : Type*} [Field F] [Finite F]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 F)
    {p : ℕ} (hp : p.Prime) (hlo : 2 < p)
    (hc : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p) :
    IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fact p.Prime := ⟨hp⟩
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj p 1 (by decide)
    (by simpa using hc) (by simpa using hconj)
  exact BenderSuzuki.External.huppert_II_10_13 J p hlo hc (by simpa using hf)

private theorem centerless_of_simple_perfect {B : Type*} [Group B]
    [IsSimpleGroup B] [Group.IsPerfect B] : center B = ⊥ :=
  (IsSimpleGroup.eq_bot_or_eq_top_of_normal (center B) inferInstance).resolve_right
    (fun he => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp he))

private theorem not_unitary {A : Type*} [Group A] [IsQuasisimple A]
    (h : CentralQuotientRestrictions (A ⧸ center A))
    {p : ℕ} (hp : p.Prime) (hlo : 3 < p)
    (hm : ClassicalGroup.IsPSU A 3 p ∨ IsSU A 3 p) : False := by
  have hn : p = 3 := by
    apply h.odd_psu3 p hp (hp.odd_of_ne_two (by omega))
    rcases hm with hm | hm
    · obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
      let := psu_prime_simple J hp (by omega) hc hconj
      let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
      exact ⟨F,inferInstance,inferInstance,J,hc,hconj,
        ⟨centerlessTargetEquiv e.toMonoidHom e.surjective centerless_of_simple_perfect⟩⟩
    · obtain ⟨F,_,_,J,hc,hconj,⟨e⟩⟩ := hm
      let := psu_prime_simple J hp (by omega) hc hconj
      let f := J.specialToProjective.comp e.toMonoidHom
      have hf : Function.Surjective f := J.specialToProjective_surjective.comp e.surjective
      let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
        Group.IsPerfect.ofSurjective hf
      exact ⟨F,inferInstance,inferInstance,J,hc,hconj,
        ⟨centerlessTargetEquiv f hf centerless_of_simple_perfect⟩⟩
  omega

/-- Every larger quotient in the full six-pair shortlist violates the
central-quotient restrictions of B.4/B.5. Special covers are retained. -/
theorem not_restrictions_of_pair {G : Type*} [Group G] (B J : Subgroup G)
    [IsQuasisimple (J ⧸ pCore 2 J)] (hp : QuasisimplePair B J) :
    ¬ CentralQuotientRestrictions
      ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := by
  intro h
  cases hp with
  | linearFourMathieu _ he | alternatingMathieu _ he | mathieu _ he =>
    exact not_sporadic h he.some Sporadic.Mathieu.M23Geometry.m23_center_eq_bot
      (Or.inl ⟨.m23, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)
  | mathieuCoverJanko _ he =>
    exact not_sporadic h he.some Janko4.model_center_eq_bot
      (Or.inl ⟨.j4, (by intro hh; cases hh), ⟨MulEquiv.refl _⟩⟩)
  | primeLinear p hp hlo u _ he =>
    cases u with
    | false => exact not_linear h hp (hp.odd_of_ne_two (by omega)) he
    | true => exact not_unitary h hp (by omega) he
  | elementaryLinear p hp hlo _ he =>
    exact not_linear h hp (hp.odd_of_ne_two (by omega)) he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.ModuleExclusions
