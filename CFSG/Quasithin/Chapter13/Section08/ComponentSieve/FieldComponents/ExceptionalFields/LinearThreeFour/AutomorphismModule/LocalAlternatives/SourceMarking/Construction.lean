module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking.Borel
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking.Sylow
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking.PrescribedAction

/-!
# Constructing the full source Borel marking

B₀ is the preimage inside K of the normalizer of the actual source Sylow,
and B = O²(B₀). Its quotient gives B = θ(B) and m₃(B) = 2. The earlier
B≤M and overlap theta identity put B in L₁. The cubic factors then force
L₁* to normalize the marked Sylow and hence equal B₀*.

The constructor transports the actual L₀ and L₁,+ to SL₃(4), proves their
relative normality, two-perfectness, cubic core quotients and generation,
and transports the original t's action. All cores and quotient kernels
are retained. The complete source-facing assembly is in SourceMarking.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20, pp.954–955, with Notation 13.2.1 and 13.2.2(3), p.877.
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearThree.Geometry.CoveredProduct.ResidualPlacement.LocalAction
open HigherFieldReduction
variable {G : Type*} [Group G] [Finite G]
variable (H K T : Subgroup G) [(Source.starImage H K).Normal]
  (eK : Source.starImage H K ≃* SL) (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)

/-- The full preimage in K of the Borel at the source Sylow. -/
def sourceBorel₀ : Subgroup G :=
  borelLift H K hKH (modelBorel H K eK (sourceSylow H K T eK hT))

/-- The actual B = O²(B₀) of the source proof. -/
def sourceBorel : Subgroup G := borelResidual (sourceBorel₀ H K T eK hKH hT)

theorem sourceBorel_le_K : sourceBorel H K T eK hKH hT ≤ K :=
  (map_subtype_le _).trans (borelLift_le H K hKH _)

theorem sourceBorel_star : Source.starImage H (sourceBorel H K T eK hKH hT) =
    modelBorel H K eK (sourceSylow H K T eK hT) :=
  starImage_liftedBorelResidual H K hKH eK _

def sourceBorelQuotientEquiv :
    (sourceBorel H K T eK hKH hT ⧸ pCore 2 (sourceBorel H K T eK hKH hT)) ≃* (Fˣ × Fˣ) :=
  borelResidualQuotientEquiv H K _ eK _ ((borelLift_le H K hKH _).trans hKH)
    (starImage_borelLift H K hKH _ (modelBorel_le H K eK _))

theorem sourceBorel_threeRank : primeRank 3 (sourceBorel H K T eK hKH hT) = 2 :=
  rank_of_torus_quotient _ (sourceBorelQuotientEquiv H K T eK hKH hT)

theorem sourceBorel_theta : sourceBorel H K T eK hKH hT =
    closure {x : G | x ∈ sourceBorel H K T eK hKH hT ∧ orderOf x = 3} :=
  theta_eq_of_torus_quotient _ (isPPerfect_embedded_pResidual 2 _)
    (sourceBorelQuotientEquiv H K T eK hKH hT)

/-- The earlier B≤M conclusion and the exact overlap theta identity give B≤L₁. -/
theorem sourceBorel_le_one (L M V₁ : Subgroup G)
    (hBM : sourceBorel H K T eK hKH hT ≤ M)
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3}) :
    sourceBorel H K T eK hKH hT ≤ one L T V₁ := by
  rw [sourceBorel_theta H K T eK hKH hT, htheta]
  apply Subgroup.closure_mono
  intro x hx
  exact ⟨⟨hKH (sourceBorel_le_K H K T eK hKH hT hx.1), hBM hx.1⟩, hx.2⟩

/-- Cubic source factors force L₁* to be the entire Borel, with its core retained. -/
theorem one_star_eq_borel (L V₁ : Subgroup G)
    (hLK : one L T V₁ ≤ K)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hz : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hx : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (hBL : sourceBorel H K T eK hKH hT ≤ one L T V₁) :
    Source.starImage H (one L T V₁) = modelBorel H K eK (sourceSylow H K T eK hT) := by
  let S := sourceSylow H K T eK hT
  have hB : modelBorel H K eK S ≤ Source.starImage H (one L T V₁) := by
    rw [← sourceBorel_star H K T eK hKH hT]
    exact starImage_mono H hBL
  have hBmodel : normalizer (S : Set SL) ≤ modelImage H K (one L T V₁) eK := by
    have hm := comap_mono (f := sourceActor H K eK) hB
    rw [modelBorel, comap_map_eq_self_of_injective (sourceActor_injective H K eK)] at hm
    exact hm
  have hp : IsPGroup 3
      (modelImage H K (one L T V₁) eK ⧸ pCore 2 (modelImage H K (one L T V₁) eK)) :=
    (one_core_threeGroup L T V₁ hTL hTV hfactor hz hx).of_equiv
      (modelCoreQuotientEquiv H K (one L T V₁) eK (hLK.trans hKH) hLK)
  have hn := le_sylowNormalizer_of_threeCore _ S (S.toSubgroup.le_normalizer.trans hBmodel) hp
  have hstar : Source.starImage H (one L T V₁) ≤ modelBorel H K eK S := by
    rw [← modelImage_map H K (one L T V₁) eK hLK]
    exact map_mono hn
  exact starImage_eq_modelBorel_of_normalizes H K _ eK S (starImage_mono H hLK) hB
    (hstar.trans (modelBorel H K eK S).le_normalizer)

/-- Construct every marked-factor field, using the original t and both actual residuals. -/
def marking (L V₁ : Subgroup G)
    (hLK : one L T V₁ ≤ K)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hz : Nat.card (zero L ⧸ pCore 2 (zero L)) = 3)
    (hx : Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3)
    (hBL : sourceBorel H K T eK hKH hT ≤ one L T V₁)
    (t : H) (htT : t.val ∈ T) (htL : t.val ∈ L)
    (hinv : ∀ q : plus L T V₁ ⧸ pCore 2 (plus L T V₁),
      coreAction (plus L T V₁) ⟨t.val, T_normalizes_plus L T V₁ hTL hTV htT⟩ q = q⁻¹) :
    SourceBorelMarking H K L T V₁ eK (QuotientGroup.mk' (pCore 2 H) t) := by
  let S := sourceSylow H K T eK hT
  have hZH := (zero_le_one_of_factorization L T V₁ hfactor).trans (hLK.trans hKH)
  have hZK := (zero_le_one_of_factorization L T V₁ hfactor).trans hLK
  have hXH := (plus_le_one L T V₁ hTV).trans (hLK.trans hKH)
  have hXK := (plus_le_one L T V₁ hTV).trans hLK
  have hmodel : modelImage H K (one L T V₁) eK = normalizer (S : Set SL) := by
    unfold modelImage
    rw [one_star_eq_borel H K T eK hKH hT L V₁ hLK hTL hTV hfactor hz hx hBL,
      modelBorel, comap_map_eq_self_of_injective (sourceActor_injective H K eK)]
  have hzle : modelImage H K (zero L) eK ≤ normalizer (S : Set SL) := by
    rw [← hmodel]
    exact comap_mono (starImage_mono H (zero_le_one_of_factorization L T V₁ hfactor))
  have hxle : modelImage H K (plus L T V₁) eK ≤ normalizer (S : Set SL) := by
    rw [← hmodel]
    exact comap_mono (starImage_mono H (plus_le_one L T V₁ hTV))
  refine ⟨{
    sylow := S
    zeroFactor := modelImage H K (zero L) eK
    plusFactor := modelImage H K (plus L T V₁) eK
    zero_le := hzle
    plus_le := hxle
    zero_normal := ?_
    plus_normal := ?_
    zero_perfect := modelImage_isPPerfect H K (zero L) eK hZH hZK (zero_isPPerfect L)
    plus_perfect := modelImage_isPPerfect H K (plus L T V₁) eK hXH hXK (plus_isPPerfect L T V₁)
    zero_quotient_card := (model_quotient_card H K (zero L) eK hZH hZK).trans hz
    plus_quotient_card := (model_quotient_card H K (plus L T V₁) eK hXH hXK).trans hx
    generate := ?_
    sylow_stable := sourceSylow_stable H K T eK hT t htT
    fix_zero := model_fix_zero H K L eK hZH hZK t htL
    invert_plus := model_invert_of_coreAction H K (plus L T V₁) eK hXH hXK t
      (T_normalizes_plus L T V₁ hTL hTV htT) hinv }, rfl, rfl⟩
  · apply (normal_subgroupOf_iff_le_normalizer hzle).mpr
    rw [← hmodel]
    exact modelImage_normalizes H K _ _ eK (one_normalizes_zero L T V₁ hTL)
  · apply (normal_subgroupOf_iff_le_normalizer hxle).mpr
    rw [← hmodel]
    exact modelImage_normalizes H K _ _ eK (one_normalizes_plus L T V₁)
  · rw [← modelImage_sup H K _ _ eK hZH hXH hZK hXK,
      sup_comm (zero L), ← hfactor, hmodel]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
