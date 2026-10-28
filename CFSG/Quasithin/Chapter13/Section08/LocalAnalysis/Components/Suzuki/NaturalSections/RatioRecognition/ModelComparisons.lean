module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition.FFExclusion
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.Natural
public import Theory.SpecificGroups.Suzuki.TwoCoreExtensionOrder


/-!
# Suzuki model comparisons and adjustment of markings

The order of a positive-parameter Suzuki matrix group is prime to three.
Actual equivalences therefore exclude the non-Suzuki models in F.9.18(4iii),
(5i), (5ii) and (5iiib,c). Special/projective comparisons use the canonical
quotient equivalences, and quasisimplicity is inherited when needed.

Order divisibility forces divisibility of the odd Suzuki field degrees.
Applying this in both directions proves parameter rigidity. Thus a natural
module identification obtained at any positive Suzuki parameter transports
to the consumer's parameter. Its group marking is constructed from that
identification; an automorphism relates it to any initially supplied marking.

These are comparisons and transport results, not the B.4.5 classification
or its Suzuki recognition consequence. The latter still needs the full
source alternatives to construct the initial natural action identification.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2/B.4.5,
printed pp.86–87, and F.9.18, pp.325–326; the Suzuki order formula is
Huppert–Blackburn III, XI.3.3, as proved in the imported model development.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition

variable {L : Type*} [Group L] {k m : ℕ}

/-- An actual isomorphism determines the positive Suzuki parameter. -/
theorem suzuki_parameter_eq (hk : 0 < k) (hm : 0 < m)
    (e : SuzukiMatrixGroup k ≃* SuzukiMatrixGroup m) : k = m := by
  have hc := Nat.card_congr e.toEquiv
  have hkm := suzukiMatrixGroup_degree_dvd_of_card_dvd hk hm (dvd_of_eq hc)
  have hmk := suzukiMatrixGroup_degree_dvd_of_card_dvd hm hk (dvd_of_eq hc.symm)
  have := Nat.dvd_antisymm hkm hmk
  omega

/-- Transport the checked three-free order through the given equivalence. -/
theorem three_free_of_equiv_suzuki (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) :
    ¬ 3 ∣ Nat.card L := by
  rw [Nat.card_congr e.toEquiv]
  exact suzukiMatrixGroup_three_free m hm

/-- An order divisible by three excludes an actual Suzuki identification. -/
theorem not_equiv_of_three_dvd (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    {M : Type*} [Group M] (hM : 3 ∣ Nat.card M) : ¬ Nonempty (L ≃* M) := by
  rintro ⟨f⟩
  apply three_free_of_equiv_suzuki hm e
  simpa only [Nat.card_congr f.toEquiv] using hM

/-- None of the quasisimple B.4.2/B.5.1 models is a positive-parameter Suzuki group. -/
theorem not_quasisimpleModel_of_equiv_suzuki [Finite L] [IsQuasisimple L]
    (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) : ¬ QuasisimpleModel L := by
  intro h
  exact three_free_of_equiv_suzuki hm e (three_dvd_card_quasisimpleModel h)

/-- None of the B.5.6 direct-factor models is a positive-parameter Suzuki group. -/
theorem not_factorModel_of_equiv_suzuki (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) :
    ¬ FactorModel L := by
  intro h
  exact three_free_of_equiv_suzuki hm e (three_dvd_card_factorModel h)

/-- Exclude a special-linear rank-one model using its cubic matrix. -/
theorem not_equiv_linearTwo (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    (F : Type*) [Field F] : ¬ Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 2) F) :=
  not_equiv_of_three_dvd hm e (Theory.SpecificGroups.three_dvd_card_sl_two F)

/-- Exclude the projective rank-one case in F.9.18(5i) and the orthogonal option in (5iiia). -/
theorem not_equiv_projectiveTwo (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    (F : Type*) [Field F] [CharP F 2] :
    ¬ Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  rintro ⟨f⟩
  exact not_equiv_linearTwo hm e F ⟨f.trans Atlas.RankOneFieldAutomorphisms.slEquivPSL.symm⟩

/-- Exclude the rank-three natural case in F.9.18(4iii). -/
theorem not_equiv_linearThree (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    (F : Type*) [Field F] [CharP F 2] :
    ¬ Nonempty (L ≃* Matrix.SpecialLinearGroup (Fin 3) F) :=
  not_equiv_of_three_dvd hm e (Theory.SpecificGroups.three_dvd_card_sl_three F)

/-- Exclude F.9.18(5ii), (5iiib) and (5iiic), retaining the actual projective quotient. -/
theorem not_equiv_binaryProjectiveThree (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) :
    ¬ Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) := by
  rintro ⟨f⟩
  exact not_equiv_linearThree hm e (ZMod 2)
    ⟨f.trans (slProjectiveEquiv (sl_binary_center_eq_bot 3 (by decide))).symm⟩

/-- Exclude in particular the alternating groups A₅, A₆ and A₇. -/
theorem not_equiv_alternating (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    (n : ℕ) (hn : 3 ≤ n) : ¬ Nonempty (L ≃* alternatingGroup (Fin n)) :=
  not_equiv_of_three_dvd hm e (three_dvd_card_alternating n hn)

/-- Exclude the symplectic case in F.9.18(4iii). -/
theorem not_equiv_symplecticFour (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    (F : BinaryField) : ¬ Nonempty (L ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) := by
  apply not_equiv_of_three_dvd hm e
  rw [Theory.SpecificGroups.SymplecticFour.card_sp, F.card_eq]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
    (Theory.SpecificGroups.three_dvd_even_square_sub_one F.degree) _) _

/-- Exclude the L₄(2) and L₅(2) cases in F.9.18(4iii). -/
theorem not_equiv_binaryProjective [Finite L] [IsQuasisimple L]
    (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) (d : ℕ) (hd : d = 4 ∨ d = 5) :
    ¬ Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin d) (ZMod 2)) := by
  rintro ⟨f⟩
  have g : L ≃* Matrix.SpecialLinearGroup (Fin d) (ZMod 2) :=
    f.trans (slProjectiveEquiv (sl_binary_center_eq_bot d (by omega))).symm
  apply not_quasisimpleModel_of_equiv_suzuki hm e
  rcases hd with rfl | rfl
  · exact .linearFourTwo g
  · exact .linearFiveTwo g

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) L V)

/-- Transport an established natural identification to the uniquely determined parameter. -/
noncomputable def naturalParameterTransport (hk : 0 < k) (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m) (a : ActionEquiv σ (natural k)) :
    ActionEquiv σ (natural m) := by
  have he := suzuki_parameter_eq hk hm (a.groupEquiv.symm.trans e)
  subst k
  exact a

/-- A natural identification at some positive parameter gives one at the prescribed parameter. -/
theorem exists_natural_with_parameter (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    (h : ∃ k, 0 < k ∧ Nonempty (ActionEquiv σ (natural k))) :
    Nonempty (ActionEquiv σ (natural m)) := by
  obtain ⟨k, hk, ⟨a⟩⟩ := h
  exact ⟨naturalParameterTransport σ hk hm e a⟩

/-- Construct the automorphism adjusting an arbitrary marking to an established natural identification. -/
theorem exists_adjusted_marking (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m)
    (h : ∃ k, 0 < k ∧ Nonempty (ActionEquiv σ (natural k))) :
    ∃ α : MulAut (SuzukiMatrixGroup m),
      ∃ f : V ≃ₗ[ZMod 2] (Fin 4 → BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * m + 1)),
        ∀ g v, f (σ g v) = natural m (α (e g)) (f v) := by
  obtain ⟨a⟩ := exists_natural_with_parameter σ hm e h
  refine ⟨e.symm.trans a.groupEquiv, a.linearEquiv, ?_⟩
  intro g v
  simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using a.intertwines g v

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.RatioRecognition
