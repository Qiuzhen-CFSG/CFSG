module

public import CFSG.Quasithin.Chapter15.Section03.InitialSource.SmallAction
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.NaturalModels


/-!
# The actual natural-action alternatives of 14.1.7

The original reduced quotient action has one or two natural factors,
no fixed summand, trivial factor centralizer and full factor-permutation
image. The compatible recognition theorems identify this same action
with natural SL₂(2), or with the full actual split binary four-dimensional
isometry group. Both actor and vector coordinates are retained; this is
stronger than an abstract group-family recognition.

Source: Aschbacher–Smith, 14.1.7, printed p.977.
-/

public section

open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.InitialSource
universe u
variable {G : Type u} [Group G] [Finite G]

theorem reduced_natural_models_from_source
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hcase : M ≠ Mc ∨ Nat.card (centralInvolutions T) = 2)
    (U : Subgroup M) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ ((T.subtype hM.2 : Sylow 2 M) : Subgroup M) ≤
      centralizer (U : Set M)) :
    letI := hU.normal
    letI := hU.elementary
    let q := QuotientGroup.mk' (centralizer (U : Set M))
    let ρ := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    (∃ (c : Additive U ≃ₗ[ZMod 2] (Fin 2 → ZMod 2))
      (e : (M ⧸ centralizer (U : Set M)) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)),
      ∀ g v, c (ρ g v) = Representation.specialLinearNatural 2 (e g) (c v)) ∨
    (∃ (c : Additive U ≃ₗ[ZMod 2] OrthogonalFourBinary.Space)
      (e : (M ⧸ centralizer (U : Set M)) ≃* OrthogonalFourBinary.TerminalLines.IsometryGroup),
      ∀ g v, c (ρ g v) = (e g).val (c v)) := by
  let := hU.normal
  let := hU.elementary
  obtain ⟨d, hn, _, _, _, _, _, hW, hcentral, honto, _, _⟩ :=
    reduced_small_action_from_source hA hC hG T hempty hM hunique hcase U hU hJ
  rcases hn with hn | hn
  · exact Or.inl (d.toSolvableFFFactors.one_factor_natural_coordinates hn hW hcentral)
  · exact Or.inr (d.toSolvableFFFactors.two_factor_orthogonal_coordinates hn
      (NormalElementaryQuotient.representation_injective _ _ _ _) hW hcentral honto)

end CFSG.Quasithin.Chapter15.Section03.InitialSource
