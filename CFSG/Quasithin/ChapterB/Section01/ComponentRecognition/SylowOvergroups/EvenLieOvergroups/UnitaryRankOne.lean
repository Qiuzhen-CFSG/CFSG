module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.RankOneReduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.GroupAction.RegularCentralizerEmbedding.Sylow

/-!
# Proper Sylow overgroups in the concrete projective unitary group

The faithful PSU₃ action on isotropic points has a Sylow subgroup acting
regularly away from the point fixed by its normalizer. The centralizer of
this Sylow embeds in the regular group and is therefore a two-group;
Sylow maximality makes the Sylow self-centralizing. Together with the
exhaustive proper-overgroup containment and solvability from F.1.3(1), this
proves the generalized-Fitting bound used in B.1.13.

The matrix field has order (2^n)² and its stored conjugation is the 2^n-power
Frobenius. Actual matrix-induced projective equivalences transport arbitrary
Hermitian forms. Every positive n, including n = 1, is covered. The model
is the genuine image of SU₃ under GL → PGL; central-cover lifting is separate.

Source: Aschbacher–Smith, combined manuscript, B.1.13, printed p.74
(PDF p.85), and F.1.3(1), printed pp.259–260.
-/

public section

open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterF.Source

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

/-- The actual projective unitary action supplies the Sylow centralizer bound,
for arbitrary Hermitian forms and every positive binary exponent. -/
theorem sylowCenterControl_psu3
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    SylowCenterControl (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J)
  obtain ⟨C, hC⟩ := Unitary.FormTransport.exists_standard_basis J n hn hcard hconj
  apply sylowCenterControl_of_equiv (Unitary.FormTransport.projectiveEquiv J C hC)
  let J0 := Unitary.FormTransport.standardForm J
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J0) :=
    Finite.of_surjective _ (Unitary.suProjection_surjective J0)
  obtain ⟨ρ, a, S, _, hproper, _, hρ, _, _, hN, hregular, _⟩ :=
    Unitary.standard_psu_borel_data J0 n hn hcard hconj rfl
  exact sylowCenterControl_of_selfCentralizing_sylow S
    (S.centralizer_le_of_faithful_regular_compl ρ hρ a hN hproper hregular)

/-- Proper Sylow overgroups in any actual PSU₃ model satisfy the source
generalized-Fitting bound, including the field parameter n = 1. -/
theorem properSylowFittingBound_psu3
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    {G : Type*} [Group G] [Finite G]
    (e : G ≃* ProjectiveSpecialUnitaryMatrixGroup J) : ProperSylowFittingBound G :=
  properSylowFittingBound_of_rankOne_equiv e
    (rankOneSylowFacts_psu3 J n hn hcard hconj)
    (sylowCenterControl_psu3 J n hn hcard hconj)

/-- Discharge the B.1.13 proper-overgroup premise for a component identified
with an actual PSU₃ model, using the literal local component intersection. -/
theorem eq_component_of_psu3
    {G : Type*} [Group G] [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (e : L ≃* ProjectiveSpecialUnitaryMatrixGroup J) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_psu3 J n hn hcard hconj e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
