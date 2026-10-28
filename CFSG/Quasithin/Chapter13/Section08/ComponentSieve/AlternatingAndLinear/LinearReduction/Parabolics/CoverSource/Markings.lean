module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.PairNormalizers
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.FiveElimination

/-!
# Exact covered overlap and the marked degree-four and degree-five outputs

The star of L₁ is the full two-residual of (L₁T)*. In common flag
coordinates its normalizer is precisely the two-node parabolic.
Relative normality in H∩M and O₂(H) ≤ T then recover the actual equality
H∩M = L₁T. Lifting through that same two-group kernel turns the genuine
one-sided source restriction N_G(L₀) ≤ M into the starred normalizer
inequality; equality of N_G(L₀) with M is never required.

The two dimension-specific theorems retain the supplied component
marking extended to H*, with both ordered residuals and the same Sylow
basis. In degree four the nodes are the two endpoints and the retained
projective line has binary rank two. In degree five these are precisely
the inputs to the existing strict-overgroup elimination, connected by
`exclude_five_source`. The natural setup also supplies the actual E₉
quotient and excludes degree three by its factor of nine.

These are conditional source deductions. The genuine natural action,
13.2.2(3) factorization, 13.2.2(9) normalizer bound, relative normality,
and component/Sylow setup remain explicit earlier inputs. Uniform
13.8.21(1) is required by the elimination adapter. This module does not
claim the remaining natural-module conclusion or H = G₁ in 13.8.25.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.8.25, printed pp.959–960 (PDF pp.976–977).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
open BinaryLinear.OuterCyclic
open BinaryLinear.InvariantNodeActions (minimalParabolic)
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction

variable {G : Type*} [Group G] [Finite G]

/-- The star of L₁ is the full two-residual of the star of L₁T. -/
theorem star_one_residual (H L T V₁ : Subgroup G)
    (hLH : one L T V₁ ≤ H) (hTH : T ≤ H) (hT : IsPGroup 2 T)
    (hTV : T ≤ normalizer (V₁ : Set G)) :
    residual (Source.starImage H (one L T V₁ ⊔ T)) = Source.starImage H (one L T V₁) := by
  rw [← star_residual H _ (sup_le hLH hTH)]
  exact congrArg (Source.starImage H)
    (embedded_pResidual_join_pGroup (one L T V₁) T (residual_isPPerfect _) hT
      (T_normalizes_one L T V₁ hTV))

/-- Normalizer computation in the model recovers the original overlap,
using the literal two-residual and the full O₂(H) kernel. -/
theorem overlap_of_model_residual {B : Type*} [Group B]
    (H M L T V₁ : Subgroup G)
    (hLH : one L T V₁ ≤ H) (hLM : one L T V₁ ≤ M)
    (hTH : T ≤ H) (hTM : T ≤ M) (hTV : T ≤ normalizer (V₁ : Set G))
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hn : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (eH : Source.Hstar H ≃* B) (P : Subgroup B)
    (hbase : (Source.starImage H (one L T V₁ ⊔ T)).map eH.toMonoidHom = P)
    (hN : normalizer (residual P : Set B) = P) : H ⊓ M = one L T V₁ ⊔ T := by
  have ht : IsPGroup 2 T := by
    have ht := S.isPGroup'.map H.subtype
    rwa [hS, map_subgroupOf_eq_of_le hTH] at ht
  apply overlap_eq_of_star_normalizer H M _ T hLH hLM hTH hTM S hS hn
  apply (Subgroup.map_le_map_iff_of_injective (f := eH.toMonoidHom) eH.injective).mp
  rw [Subgroup.map_normalizer_eq_of_bijective _ eH.bijective,
    ← star_one_residual H L T V₁ hLH hTH ht hTV,
    FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.residual,
    map_embedded_pResidual, hbase]
  exact hN.le

/-- In the covered source setup the factor of nine excludes degree three.
The source quotient orders are computed from the natural action. -/
theorem dimension_at_least_four (H K L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K) (hK : (K.subgroupOf H).IsCComponent)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    {n : ℕ} (hn : 3 ≤ n) (e : (K ⧸ pCore 2 K) ≃* PSL n) : 4 ≤ n := by
  by_contra h
  have he : n = 3 := by omega
  subst n
  exact exclude_three H K L T V₁ hKH hK hLK d.normalizes_L d.line_stable
    hcover hfactor (d.plus_core_card hfactor) e

/-- The covered degree-four source has the two ordered end nodes. The same
whole-group marking retains both residuals, the Sylow flag and the rank-two
parabolic, whose projective line has binary dimension two. -/
theorem four_source_markings (H K M L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hKH : K ≤ H) (hTH : T ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* PSL 4) :
    ∃ (hs : Source.starImage H T ≤ Source.starImage H K)
      (b : Basis 3) (beta delta : Fin 3),
      beta ≠ delta ∧ (beta.val + 1 < delta.val ∨ delta.val + 1 < beta.val) ∧
      let eH := wholeLinearModel H K T hKH hTH hK hKT hs e
      (Source.starImage H (one L T V₁ ⊔ T)).map eH.toMonoidHom =
        fourParabolic b {beta, delta} ∧
      (Source.starImage H (zero L)).map eH.toMonoidHom = fourNodeResidual b beta ∧
      (Source.starImage H (plus L T V₁)).map eH.toMonoidHom = fourNodeResidual b delta ∧
      (Source.starImage H T).map eH.toMonoidHom = cutStabilizer b Set.univ ∧
      H ⊓ M = one L T V₁ ⊔ T ∧
      normalizer (Source.starImage H (zero L) : Set (Source.Hstar H)) ≤
        normalizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) ∧
      plus L T V₁ ≤ one L T V₁ ∧ Source.QH H ≤ T ∧
      ((beta = 0 ∧ delta = 2) ∨ (beta = 2 ∧ delta = 0)) ∧
      Module.finrank (ZMod 2) (cutSpace b 1) = 2 := by
  obtain ⟨hs, b, beta, delta, hne, hgap, _, _, _, _, _, hflag, hzero, hplus, hbase⟩ :=
    source_marked_pair H K L T V V₁ V₃ d hKH hTH hLK hK hKn hKT hcover hfactor S hS
      (by omega : 3 = 3 ∨ 3 = 4) e
  let eH := wholeLinearModel H K T hKH hTH hK hKT hs e
  have hinter : H ⊓ M = one L T V₁ ⊔ T :=
    overlap_of_model_residual H M L T V₁ (hLK.trans hKH) hLM hTH hTM d.line_stable
      S hS hrel eH (fourParabolic b {beta, delta}) hbase
      (fourPair_residual_normalizer_of_nonadjacent b beta delta hgap)
  refine ⟨hs, b, beta, delta, hne, hgap, hbase, hzero, hplus, hflag, hinter,
    zero_star_normalizer_le_plus H M L T V₁ (hLK.trans hKH) hTH
      d.normalizes_L d.line_stable S hS hfactor hNM hinter,
    plus_le_one L T V₁ d.line_stable, twoCore_le_T H T hTH S hS, ?_, ?_⟩
  · have hend : ∀ i j : Fin 3, (i.val + 1 < j.val ∨ j.val + 1 < i.val) →
        ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) := by decide +kernel
    exact hend beta delta hgap
  · exact cutSpace_finrank b 1

/-- The precise degree-five inputs for `exclude_five_marked_pair`. The ordered
nodes, subgroup identities, exact overlap and starred normalizer bound are
all deduced; none is an input premise. -/
theorem five_source_markings (H K M L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hKH : K ≤ H) (hTH : T ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* PSL 5) :
    ∃ (hs : Source.starImage H T ≤ Source.starImage H K)
      (b : Basis 4) (beta delta : Fin 4),
      beta ≠ delta ∧ (beta.val + 1 < delta.val ∨ delta.val + 1 < beta.val) ∧
      let eH := wholeLinearModel H K T hKH hTH hK hKT hs e
      (Source.starImage H (one L T V₁ ⊔ T)).map eH.toMonoidHom =
        fiveParabolic b {beta, delta} ∧
      (Source.starImage H (zero L)).map eH.toMonoidHom = fiveNodeResidual b beta ∧
      (Source.starImage H (plus L T V₁)).map eH.toMonoidHom = fiveNodeResidual b delta ∧
      (Source.starImage H T).map eH.toMonoidHom = cutStabilizer b Set.univ ∧
      H ⊓ M = one L T V₁ ⊔ T ∧
      normalizer (Source.starImage H (zero L) : Set (Source.Hstar H)) ≤
        normalizer (Source.starImage H (plus L T V₁) : Set (Source.Hstar H)) ∧
      plus L T V₁ ≤ one L T V₁ ∧ Source.QH H ≤ T := by
  obtain ⟨hs, b, beta, delta, hne, hgap, _, _, _, _, _, hflag, hzero, hplus, hbase⟩ :=
    source_marked_pair H K L T V V₁ V₃ d hKH hTH hLK hK hKn hKT hcover hfactor S hS
      (by omega : 4 = 3 ∨ 4 = 4) e
  let eH := wholeLinearModel H K T hKH hTH hK hKT hs e
  have hinter : H ⊓ M = one L T V₁ ⊔ T :=
    overlap_of_model_residual H M L T V₁ (hLK.trans hKH) hLM hTH hTM d.line_stable
      S hS hrel eH (fiveParabolic b {beta, delta}) hbase
      (fivePair_residual_normalizer b beta delta hgap)
  refine ⟨hs, b, beta, delta, hne, hgap, hbase, hzero, hplus, hflag, hinter,
    zero_star_normalizer_le_plus H M L T V₁ (hLK.trans hKH) hTH
      d.normalizes_L d.line_stable S hS hfactor hNM hinter,
    plus_le_one L T V₁ d.line_stable, twoCore_le_T H T hTH S hS⟩

/-- The literal source quotient is elementary abelian of order nine,
with its two cubic residual directions constructed from the natural setup. -/
theorem source_elementary_quotient (L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L) :
    Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 9 ∧
      IsMulCommutative (one L T V₁ ⧸ pCore 2 (one L T V₁)) ∧
      ∀ x : one L T V₁ ⧸ pCore 2 (one L T V₁), x ^ 3 = 1 :=
  ⟨one_quotient_card L T V₁ d.normalizes_L d.line_stable hfactor
      d.zero_core_card (d.plus_core_card hfactor),
    one_quotient_commutative L T V₁ d.normalizes_L d.line_stable hfactor
      d.zero_core_card (d.plus_core_card hfactor),
    one_quotient_cube L T V₁ d.normalizes_L d.line_stable hfactor
      d.zero_core_card (d.plus_core_card hfactor)⟩

/-- Connect the constructed source markings directly to the existing
strict-overgroup contradiction. Uniform 13.8.21(1) remains the explicit
earlier chapter input; every flag, residual, overlap and normalizer premise
of the geometric elimination is discharged here. -/
theorem exclude_five_source (H K G₁ M L T V V₁ V₃ : Subgroup G)
    (d : NaturalSetup L T V V₁ V₃)
    (hH : H ∈ Source.Hz (one L T V₁) T G₁ M)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (e : (K ⧸ pCore 2 K) ≃* PSL 5)
    (h21 : ∀ (Y D : Subgroup G), Y ∈ Source.Hz (one L T V₁) T G₁ M → D ≤ Y →
      (D.subgroupOf Y).IsCComponent → one L T V₁ ≤ D) : False := by
  have hTH : T ≤ H := le_sup_right.trans hH.1.2
  obtain ⟨hs, b, beta, delta, _, hgap, hbase, hzero, hplus, _, hinter, hn, hp, hcore⟩ :=
    five_source_markings H K M L T V V₁ V₃ d hKH hTH hLK hLM hTM hK hKn hKT
      hcover hfactor S hS hrel hNM e
  exact exclude_five_marked_pair (one L T V₁) (zero L) (plus L T V₁) T G₁ M H hH
    (wholeLinearModel H K T hKH hTH hK hKT hs e) b beta delta hgap hbase hzero hplus
    hp hn hinter hcore h21

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
end
