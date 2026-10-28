module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.StarGeometry
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.StarGeneration
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ElementaryBranch
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.ThreeAlternatives.ExtraspecialBranch

/-!
# The two complete three-group alternatives in 15.3.7

The star quotient has class at most two and prime rank exactly two, and is
genuinely isomorphic to `Y/O₂(Y)`, by StarGeometry. StarGeneration proves
order-three generation from the actual residual and the intersection-core
inverter. The class-two exponent lemma then proves that it is a three-group,
so A.1.24 supplies actual E₉ or prime Heisenberg isomorphisms.

The elementary branch identifies `O₂(Y) = C_Y(V)` and `Y = O^{3′}(M)`.
The extraspecial branch identifies the literal central preimage with `C_Y(V)`,
proves cyclicity of the actual Rc action image, identifies `Y = θ(M)`, and
proves cyclicity of every Sylow three-subgroup of `M ∩ Mc`.

`residual_alternatives` assembles all these conclusions from `SourceInputs`,
without an extra generation or model premise. This remains a conditional
helper for 15.3.7: the ResidualStructure assembly owner must supply the
preceding action calculations, genuine 14.1.17 outputs, standing local
hypotheses and general local conclusions listed in ThreeAlternatives.Inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Lemmas A.1.24
and 15.3.7, printed pp.25 and 1122.
-/

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
variable {G : Type*} [Group G] [Finite G]
variable {M Mc V : Subgroup G} {T : Sylow 2 G} {d : NaturalOrthogonalAction M V}

/-- Class two converts order-three generation into the three-group assertion. -/
public theorem star_isThreeGroup_of_omega (h : SourceInputs M Mc V T d)
    (homega : omega₁ (star M (residualY M Mc)) (p := 3) = ⊤) :
    IsPGroup 3 (star M (residualY M Mc)) := by
  have he := exponent_dvd_prime_of_omega_one_eq_top (by decide : 3 ≠ 2)
    (star_class_two h) homega
  intro x
  exact ⟨1, by simpa using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he x⟩

/-- A.1.24 applied to the literal star residual, retaining genuine models. -/
public theorem star_models_of_omega (h : SourceInputs M Mc V T d)
    (homega : omega₁ (star M (residualY M Mc)) (p := 3) = ⊤) :
    (Nat.card (star M (residualY M Mc)) = 9 ∧
      Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) ∨
    (Nat.card (star M (residualY M Mc)) = 27 ∧
      IsExtraspecial 3 (star M (residualY M Mc)) ∧
      Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3)) := by
  exact ChapterA.lemma_A_1_24 (by decide) (star_isThreeGroup_of_omega h homega)
    homega (star_class_two h) (star_rank h)

/-- The model isomorphisms concern Y/O₂(Y), via its proved star identification. -/
public theorem core_quotient_models_of_omega (h : SourceInputs M Mc V T d)
    (homega : omega₁ (star M (residualY M Mc)) (p := 3) = ⊤) :
    Nonempty ((residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* ElementaryNine) ∨
    Nonempty ((residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* HeisenbergPrime 3) := by
  rcases star_models_of_omega h homega with ⟨_, ⟨e⟩⟩ | ⟨_, _, ⟨e⟩⟩
  · exact Or.inl ⟨(residualCoreQuotientEquivStar M Mc).trans e⟩
  · exact Or.inr ⟨(residualCoreQuotientEquivStar M Mc).trans e⟩

/-- The actual star residual is a three-group, with generation discharged. -/
public theorem star_isThreeGroup (h : SourceInputs M Mc V T d) :
    IsPGroup 3 (star M (residualY M Mc)) :=
  star_isThreeGroup_of_omega h (star_omega_eq_top h)

/-- The genuine A.1.24 alternatives for the star residual, from the preceding
source inputs alone. -/
public theorem star_models (h : SourceInputs M Mc V T d) :
    (Nat.card (star M (residualY M Mc)) = 9 ∧
      Nonempty (star M (residualY M Mc) ≃* ElementaryNine)) ∨
    (Nat.card (star M (residualY M Mc)) = 27 ∧
      IsExtraspecial 3 (star M (residualY M Mc)) ∧
      Nonempty (star M (residualY M Mc) ≃* HeisenbergPrime 3)) :=
  star_models_of_omega h (star_omega_eq_top h)

/-- Actual model isomorphisms for the intrinsic quotient `Y/O₂(Y)`. -/
public theorem core_quotient_models (h : SourceInputs M Mc V T d) :
    Nonempty ((residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* ElementaryNine) ∨
    Nonempty ((residualY M Mc ⧸ pCore 2 (residualY M Mc)) ≃* HeisenbergPrime 3) :=
  core_quotient_models_of_omega h (star_omega_eq_top h)

/-- Both complete alternatives of 15.3.7 for the literal residual. All generation
and A.1.24 branch premises are discharged; only the published preceding source
inputs remain for the full source-theorem assembly. -/
public theorem residual_alternatives (h : SourceInputs M Mc V T d) :
    ElementaryAlternative M Mc V ∨ ExtraspecialAlternative M Mc V d := by
  rcases star_models h with ⟨_, he⟩ | ⟨hcard, hextra, he⟩
  · exact Or.inl (elementaryAlternative_of_star_equiv h he)
  · exact Or.inr (extraspecialAlternative_of_star_model h hcard hextra he)

end CFSG.Quasithin.Chapter15.Section03.ThreeAlternatives
