module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource.LocalAlgebra
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The two actual covered Sylow overgroups

The candidates are literally L₀*(T*∩K*) and L₁,+*(T*∩K*).
Their two-residuals recover the original starred source subgroups.
Consequently the order-nine quotient of L₁ forces the candidates to be
distinct. Normalization is individual, not merely preservation of a pair.

Once their deleted flags have been constructed, these facts discharge
the hypotheses of the invariant-two-node theorem, giving T* ≤ K* while
retaining the supplied component equivalence. Flag construction is not
asserted by the conditional last theorem.

Source: Aschbacher–Smith 13.8.25, printed p.960 (1 March 2004 manuscript).
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
variable {G : Type*} [Group G] [Finite G]

/-- The actual source Sylow overgroup attached to A, before flag recognition. -/
def candidate (H K T A : Subgroup G) : Subgroup (Source.Hstar H) :=
  Source.starImage H A ⊔ (Source.starImage H T ⊓ Source.starImage H K)

omit [Finite G] in
theorem candidate_le_component (H K T A : Subgroup G) (hAK : A ≤ K) :
    candidate H K T A ≤ Source.starImage H K :=
  sup_le (map_mono (subgroupOf_mono H hAK)) inf_le_right

omit [Finite G] in
/-- Both factors are individually normalized by the original T*. -/
theorem candidate_normalized (H K T A : Subgroup G)
    (hTK : T ≤ normalizer (K : Set G)) (hTA : T ≤ normalizer (A : Set G)) :
    Source.starImage H T ≤ normalizer (candidate H K T A : Set (Source.Hstar H)) := by
  have hn := ((le_inf (Source.starImage H T).le_normalizer
    (star_normalizes H T K hTK)).trans inf_normalizer_le_normalizer_inf)
  exact (le_inf (star_normalizes H T A hTA) hn).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
/-- The actual two-residual of a candidate retains its source mark. -/
theorem candidate_residual (H K T A : Subgroup G) (hAH : A ≤ H)
    (hp : IsPPerfect 2 A) (hT : IsPGroup 2 T)
    (hTA : T ≤ normalizer (A : Set G)) :
    residual (candidate H K T A) = Source.starImage H A := by
  have hp' := hp.of_surjective (starMap H A hAH) (starMap_surjective H A hAH)
  have ht : IsPGroup 2 (Source.starImage H T) := hT.comap_subtype.map _
  exact embedded_pResidual_join_pGroup _ _ hp'
    (ht.of_injective (inclusion inf_le_left) (inclusion_injective inf_le_left))
    (inf_le_left.trans (star_normalizes H T A hTA))

/-- The genuine order-nine quotient distinguishes the starred marks even
though neither marked subgroup itself need have order three. -/
theorem star_marks_ne (H L T V₁ : Subgroup G) (hLH : one L T V₁ ≤ H)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    Source.starImage H (zero L) ≠ Source.starImage H (plus L T V₁) := by
  intro he
  have h0H := (zero_le_one_of_factorization L T V₁ hfactor).trans hLH
  have hpH := (plus_le_one L T V₁ hTV).trans hLH
  have hgen : Source.starImage H (one L T V₁) =
      Source.starImage H (plus L T V₁) := by
    conv_lhs => rw [hfactor]
    rw [Source.starImage, subgroupOf_sup hpH h0H, Subgroup.map_sup]
    change Source.starImage H (plus L T V₁) ⊔ Source.starImage H (zero L) = _
    rw [he, sup_idem]
  have h9 : Nat.card (Source.starImage H (one L T V₁) ⧸
      pCore 2 (Source.starImage H (one L T V₁))) = 9 :=
    (Nat.card_congr (starCoreQuotientEquiv H (one L T V₁) hLH).toEquiv).symm.trans
      (one_quotient_card L T V₁ hTL hTV hfactor (zero_quotient_card L hcover) hplus)
  have h3 : Nat.card (Source.starImage H (plus L T V₁) ⧸
      pCore 2 (Source.starImage H (plus L T V₁))) = 3 :=
    (Nat.card_congr (starCoreQuotientEquiv H (plus L T V₁) hpH).toEquiv).symm.trans hplus
  rw [hgen] at h9
  omega

/-- Equal candidates would have equal two-residuals, contrary to the
two marked cubic directions generating the order-nine source quotient. -/
theorem candidates_ne (H K L T V₁ : Subgroup G) (hLH : one L T V₁ ≤ H)
    (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3) :
    candidate H K T (zero L) ≠ candidate H K T (plus L T V₁) := by
  intro he
  have hr := congrArg residual he
  rw [candidate_residual H K T (zero L)
    ((zero_le_one_of_factorization L T V₁ hfactor).trans hLH)
    (residual_isPPerfect _) hT (hTL.trans (normalizer_le_zero_normalizer L)),
    candidate_residual H K T (plus L T V₁) ((plus_le_one L T V₁ hTV).trans hLH)
      (residual_isPPerfect _) hT (T_normalizes_plus L T V₁ hTL hTV)] at hr
  exact star_marks_ne H L T V₁ hLH hTL hTV hcover hfactor hplus hr

/-- Apply the actual source-action theorem once the candidates' flags
have been constructed. All invariance and distinctness premises are derived. -/
theorem inner_of_candidate_flags (H K L T V₁ : Subgroup G)
    (hKH : K ≤ H) (hTH : T ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hKT : K ⊔ T = H)
    (hLH : one L T V₁ ≤ H) (hT : IsPGroup 2 T)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hplus : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4)
    (e : (K ⧸ pCore 2 K) ≃* PSL (m + 1))
    (b c : Basis m) (i j : Fin m)
    (hP : candidate H K T (zero L) =
      ambientFlagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag hm₀ b i))
    (hQ : candidate H K T (plus L T V₁) =
      ambientFlagStabilizer (starLinearEquiv H K hKH hK e) (deletedFlag hm₀ c j)) :
    Source.starImage H T ≤ Source.starImage H K := by
  have hTK := hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn)
  exact source_two_deletedFlags_le_component H K T hKH hTH hK hKn hT hKT S hS
    hm₀ hm₁ e b c i j _ _ hP hQ le_sup_right le_sup_right
    (candidates_ne H K L T V₁ hLH hT hTL hTV hcover hfactor hplus)
    (candidate_normalized H K T (zero L) hTK (hTL.trans (normalizer_le_zero_normalizer L)))
    (candidate_normalized H K T (plus L T V₁) hTK (T_normalizes_plus L T V₁ hTL hTV))

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.CoverSource
end
