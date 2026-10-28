module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Reduction
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.LocalData
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.Rank
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.ActionSelection
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.SourceResiduals
public import Theory.Quasithin.Rank
public import CFSG.Quasithin.Defs

/-!
# The rank construction in the noncontained extraspecial branch of 13.8.13

The action alternative constructs an elementary subgroup of order 27
inside the literal image of L₁P in H/O₂(H). Its three-rank is therefore
at least three. Odd-rank monotonicity for the quotient by O₂(H) contradicts
the actual strong-quasithin bound on H.

The rank witness, commuting inverter, Heisenberg identification and action
alternative are all constructed from the cubic residual generators and the
literal Frattini irreducibility. The source-model endpoint also constructs
those generators, using L₁ in the simple case and the two separate cubic
marks L₁,+ and L₀ in the covered case. No branch-specific action, elementary
subgroup or rank bound is an input to that endpoint.

`false_of_source_earlier` connects this argument to the genuine standing
`LocalSetup`, identifying L₁ with the literal `sourceOne`. The earlier
natural-model alternative and covered factorization 13.2.2(3) remain
explicit through `EarlierLocalInputs`. Their source proofs belong to the
§13.2 and §13.5 developments; this module does not assert their discharge.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.13, printed p.951 (PDF p.968), and A.1.33(1), printed p.29.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial
variable {G : Type*} [Group G] [Finite G]
variable {H L₁ T M Vα : Subgroup G}

/-- Construct the rank witness in the actual L₁P image, including its placement. -/
theorem exists_elementary_in_join_of_action_alternative
    (r : ReducedOdd 3 H L₁ T M Vα) [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (ha : ActionAlternative r) :
    ∃ A : Subgroup (Source.Hstar H), A ≤ Source.starImage H (L₁ ⊔ r.P) ∧
      IsElementaryAbelian 3 A ∧ Nat.card A = 27 := by
  let := r.Pstar_normal
  have hPJ := starImage_mono H (show r.P ≤ L₁ ⊔ r.P from le_sup_right)
  rcases ha with ⟨X, hXL, hX, hX3, hne⟩ | ⟨x, hxL, hx, hxP, hxV⟩
  · let hXH : X ≤ H := hXL.trans (le_sup_left.trans (r.generated ▸ le_sup_right))
    apply elementary_of_cubic_residual (Source.starImage H r.P)
      (Source.starImage H (L₁ ⊔ r.P)) hc hexp hPJ hX hX3 (starMap H X hXH) ?_ hne
    intro x
    exact mem_map_of_mem (QuotientGroup.mk' (pCore 2 H))
      (show inclusion hXH x ∈ (L₁ ⊔ r.P).subgroupOf H from mem_sup_left (hXL x.property))
  · exact elementary_of_inner_actor (Source.starImage H r.P)
      (Source.starImage H (L₁ ⊔ r.P)) hc hexp hPJ x
      (starImage_mono H le_sup_left hxL) hx hxP hxV

/-- The constructed witness gives the source lower bound in the literal join. -/
theorem rank_join_ge_three_of_action_alternative
    (r : ReducedOdd 3 H L₁ T M Vα) [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (ha : ActionAlternative r) :
    3 ≤ primeRank 3 (Source.starImage H (L₁ ⊔ r.P)) := by
  obtain ⟨A, hAJ, hA, hAc⟩ := exists_elementary_in_join_of_action_alternative r hc hexp ha
  let := hA
  let := IsElementaryAbelian.subgroupOf (p := 3) hAJ
  exact IsElementaryAbelian.primeRank_ge_of_card
    (A.subgroupOf (Source.starImage H (L₁ ⊔ r.P)))
    ((Nat.card_congr (subgroupOfEquivOfLe hAJ).toEquiv).trans hAc)

/-- Transport the constructed odd-rank obstruction through the literal
two-core quotient. The local action alternative remains to be supplied. -/
theorem false_of_action_alternative
    (r : ReducedOdd 3 H L₁ T M Vα) [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (hr : IsStronglyQuasithin H) (ha : ActionAlternative r) : False := by
  have hlower := rank_join_ge_three_of_action_alternative r hc hexp ha
  have hJ := primeRank_subgroup_le 3 (Source.starImage H (L₁ ⊔ r.P))
  have hquot : primeRank 3 (Source.Hstar H) ≤ primeRank 3 H :=
    primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup
  have hupper := hr 3 Nat.prime_three (by decide)
  omega

/-- Irreducibility and the earlier cubic generators construct an elementary
subgroup of order 27 in the literal L₁P image. In particular, neither the
action alternative nor the elementary subgroup is an input. -/
theorem exists_elementary_in_join_of_cubicGeneration
    (r : ReducedOdd 3 H L₁ T M Vα) (d : CubicGeneration L₁ T)
    [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (hnot : ¬ Source.starImage H L₁ ≤ Source.starImage H r.P) :
    ∃ A : Subgroup (Source.Hstar H), A ≤ Source.starImage H (L₁ ⊔ r.P) ∧
      IsElementaryAbelian 3 A ∧ Nat.card A = 27 :=
  exists_elementary_in_join_of_action_alternative r hc hexp
    (actionAlternative_of_cubicGeneration r d hnot)

/-- The source lower bound follows from the local cubic residual structure,
with the nontrivial Frattini action or inner cubic actor constructed. -/
theorem rank_join_ge_three_of_cubicGeneration
    (r : ReducedOdd 3 H L₁ T M Vα) (d : CubicGeneration L₁ T)
    [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (hnot : ¬ Source.starImage H L₁ ≤ Source.starImage H r.P) :
    3 ≤ primeRank 3 (Source.starImage H (L₁ ⊔ r.P)) :=
  rank_join_ge_three_of_action_alternative r hc hexp
    (actionAlternative_of_cubicGeneration r d hnot)

/-- The extraspecial noncontained branch contradicts strong quasithinness
once the earlier cubic residual structure is supplied. -/
theorem false_of_cubicGeneration
    (r : ReducedOdd 3 H L₁ T M Vα) (d : CubicGeneration L₁ T)
    [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (hnot : ¬ Source.starImage H L₁ ≤ Source.starImage H r.P)
    (hr : IsStronglyQuasithin H) : False :=
  false_of_action_alternative r hc hexp hr
    (actionAlternative_of_cubicGeneration r d hnot)

open TransvectionRecognition.Component.ModelExtension
open ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement

/-- Apply the rank contradiction to the actual natural models for the
source residual. Only the earlier model alternative and covered
factorization remain explicit; all cubic and action facts are derived. -/
theorem false_of_source_models
    {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
    (r : ReducedOdd 3 H (sourceOne L T V₁) T M Vα)
    (models : Nonempty (TransvectionParabolic.EarlierCore.ComponentSetup T L V V₁ V₂ V₃) ∨
      Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃))
    (factorization : ∀ _d : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃,
      one L T V₁ = plus L T V₁ ⊔ zero L)
    [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (hnot : ¬ Source.starImage H (sourceOne L T V₁) ≤ Source.starImage H r.P)
    (hr : IsStronglyQuasithin H) : False :=
  false_of_cubicGeneration r (SourceResiduals.of_models models factorization) hc hexp hnot hr

/-- The standing-setup application, on the original selected P and literal
two-core quotient. EarlierLocalInputs is used only for the natural models
and 13.2.2(3); its independent earlier-source obligations are retained. -/
theorem false_of_source_earlier
    {T : Sylow 2 G} {L V V₁ V₂ V₃ G₁ : Subgroup G}
    (s : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (earlier : TransvectionRecognition.Solvable.EarlierLocalInputs (G := G))
    (hL₁ : L₁ = sourceOne L T V₁)
    (r : ReducedOdd 3 H L₁ T M Vα)
    [IsExtraspecial 3 (Source.starImage H r.P)]
    (hc : Nat.card (Source.starImage H r.P) = 27)
    (hexp : ∀ x : Source.starImage H r.P, x ^ 3 = 1)
    (hnot : ¬ Source.starImage H L₁ ≤ Source.starImage H r.P)
    (hr : IsStronglyQuasithin H) : False := by
  subst L₁
  exact false_of_source_models r (earlier.natural_models T L V V₁ V₂ V₃ M G₁ s)
    (earlier.covered_factorization L T V V₁ V₃) hc hexp hnot hr

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Three.Extraspecial

end
