module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.IntrinsicAction

/-!
# Source SL₃(4) graph alternatives with the retained two-cores

The actual B = O²(B₀), marked by T∩K, has the full Borel as image in
K* ≃ SL₃(4). Its three-rank selects the covered A₆ case. The two source
residuals L₀ and X = L₁,+ then supply the intrinsic marked factors.
The intrinsic alternatives give a central X* in the graph case, or a
central L₀* in the graph-field case. Perfectness of SL₃(4) lifts the
projective graph formula to the original prescribed t* action.

The comparison with the cyclic action commutator or fixed Borel uses its
two-residual, retaining the two-core. The full fixed Borel need not be
central; CoreObstruction provides a concrete obstruction to that stronger
printed identity. In the graph-field case, two-perfectness of L₀ and the
source overlap identities lift its central image to H-normalization.
The parent can then apply N_G(L₀) ≤ M and H ≰ M.

The earlier source clauses and standard-automorphism coverage remain
explicit inputs. No Borel marking, central-image equality, normalization
of L₀ by H, or involution hypothesis on t is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1, 13.2.2(3),(9) and its centralizer calculation, pp.877–878;
13.7.3(6),(9), p.936; proof of 13.8.20, pp.954–955 (PDF pp.971–972).
-/

@[expose] public section
open Subgroup Representation.SL3FourNaturalDual
open Matrix.PSL3.OuterSolvable
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open SourceMarking
variable {G : Type*} [Group G]

/-- The graph conclusion for the original t*, including X* and the residual
of the full cyclic action commutator on the actual L₁* model image. -/
def GraphAlternative (H K L T V₁ : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H) : Prop :=
  ∃ c : Matrix.GeneralLinearGroup (Fin 3) F,
    centerAction F (sourceConjugation H K eK t) = linearConj F c * graph F ∧
    (∀ g, sourceActor H K eK g * t = t * sourceActor H K eK
      (linearConjSL F c (Matrix.SpecialLinearGroup.inverseTranspose g))) ∧
    Source.starImage H (plus L T V₁) =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype ∧
    let C := commutatorSubgroup (zpowers (sourceConjugation H K eK t)) SL
      (modelImage H K (one L T V₁) eK)
    (pResidual 2 C).map C.subtype = center SL

/-- The graph-field conclusion retains the fixed Borel's two-part, supplies
the literal central L₀* image, and derives the normalizer step. -/
def GraphFieldAlternative (H K L T V₁ : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (t : Source.Hstar H) : Prop :=
  ∃ (c : Matrix.GeneralLinearGroup (Fin 3) F) (σ : F ≃+* F),
    σ ≠ 1 ∧
    centerAction F (sourceConjugation H K eK t) =
      linearConj F c * fieldAction F σ * graph F ∧
    Source.starImage H (zero L) =
      (center (Source.starImage H K)).map (Source.starImage H K).subtype ∧
    H ≤ normalizer (zero L : Set G) ∧
    let C := modelImage H K (one L T V₁) eK ⊓ (sourceConjugation H K eK t).fixedSubgroup
    (pResidual 2 C).map C.subtype = center SL

variable [Finite G]

/-- Assemble the actual source marking and the intrinsic alternatives. The
inputs from Notation 13.2.1 and 13.2.2 are conditional on the genuine covered
model. The overlap clauses are precisely 13.7.3(6),(9); B≤M is the preceding
Borel reduction on p.954. The constructor proves all intervening marking,
core, central-image and kernel-normalization facts. -/
theorem source_alternatives
    (H K L T M V V₁ V₃ : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hLK : one L T V₁ ≤ K)
    (hTL : T ≤ normalizer (L : Set G)) (hTV : T ≤ normalizer (V₁ : Set G))
    (hBM : sourceBorel H K T eK hKH hT ≤ M)
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      primeRank 3 (one L T V₁) = 1)
    (hcovered : ∀ _ : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      one L T V₁ = plus L T V₁ ⊔ zero L ∧
      Nat.card (zero L ⧸ pCore 2 (zero L)) = 3 ∧
      Nat.card (plus L T V₁ ⧸ pCore 2 (plus L T V₁)) = 3 ∧
      centralPreimage L = L ⊓ centralizer (V : Set G))
    (hcomm : ⁅V, Source.QH H⁆ = V₃) (hV₃ : V₃ ≤ V)
    (hoverlap : H ⊓ M = H ⊓ normalizer (V : Set G))
    (t : H) (htT : t.val ∈ T) (htL : t.val ∈ L)
    (hinv : ∀ _ : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      ∀ q : plus L T V₁ ⧸ pCore 2 (plus L T V₁),
      coreAction (plus L T V₁) ⟨t.val, T_normalizes_plus L T V₁ hTL hTV htT⟩ q = q⁻¹)
    (hcover : standard F = ⊤) :
    ∃ _ : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms,
      sourceBorel H K T eK hKH hT =
        closure {x : G | x ∈ sourceBorel H K T eK hKH hT ∧ orderOf x = 3} ∧
      sourceBorel H K T eK hKH hT ≤ one L T V₁ ∧
      primeRank 3 (sourceBorel H K T eK hKH hT) = 2 ∧
      Source.starImage H (one L T V₁) = modelBorel H K eK (sourceSylow H K T eK hT) ∧
      (Source.starImage H (one L T V₁)).pCoreIn 2 = Source.starImage H (T ⊓ K) ∧
      Nonempty ((Source.starImage H (one L T V₁) ⧸
        pCore 2 (Source.starImage H (one L T V₁))) ≃* (Fˣ × Fˣ)) ∧
      Source.QH H ≤ normalizer (zero L : Set G) ∧
      (GraphAlternative H K L T V₁ eK (QuotientGroup.mk' (pCore 2 H) t) ∨
       GraphFieldAlternative H K L T V₁ eK (QuotientGroup.mk' (pCore 2 H) t)) := by
  obtain ⟨eL, m, hmS, hBtheta, hBL, hBrank, hBstar, hQ⟩ :=
    exists_source_marking H K L T M V V₁ V₃ eK hKH hT hLK hTL hTV hBM htheta
      hmodels hordinary hcovered hcomm hV₃ hoverlap t htT htL hinv
  have hcore : (Source.starImage H (one L T V₁)).pCoreIn 2 =
      Source.starImage H (T ⊓ K) := by
    rw [hBstar, modelBorel_twoCore, sourceSylow_intersection,
      modelImage_map H K (T ⊓ K) eK inf_le_right]
  have htorus : Nonempty ((Source.starImage H (one L T V₁) ⧸
      pCore 2 (Source.starImage H (one L T V₁))) ≃* (Fˣ × Fˣ)) := by
    rw [hBstar]
    exact ⟨modelBorelQuotientEquiv H K eK (sourceSylow H K T eK hT)⟩
  refine ⟨eL, hBtheta, hBL, hBrank, hBstar, hcore, htorus, hQ, ?_⟩
  have hS : (m.factors.sylow : Subgroup SL) = sourceSylow H K T eK hT :=
    hmS.trans (sourceSylow_intersection H K T eK hT).symm
  have hB : modelImage H K (one L T V₁) eK = normalizer (m.factors.sylow : Set SL) := by
    unfold modelImage
    rw [hBstar, modelBorel, comap_map_eq_self_of_injective (sourceActor_injective H K eK)]
    exact congrArg (fun S : Subgroup SL => normalizer (S : Set SL)) hS.symm
  rcases IntrinsicAction.alternatives m.factors hcover with
    ⟨c, hc, hX, hres⟩ | ⟨c, σ, hσ, hc, hZ, hres⟩
  · have hXK : plus L T V₁ ≤ K := (plus_le_one L T V₁ hTV).trans hLK
    have hstar := starImage_eq_center_of_modelImage H K (plus L T V₁) eK
      (starImage_mono H hXK) (m.plus_eq.symm.trans hX)
    exact Or.inl ⟨c, hc, source_graph_relation H K eK _ c hc, hstar, hB ▸ hres⟩
  · have hZK : zero L ≤ K :=
      (LocalAction.zero_le_one_of_factorization L T V₁ (hcovered eL).1).trans hLK
    have hstar := starImage_eq_center_of_modelImage H K (zero L) eK
      (starImage_mono H hZK) (m.zero_eq.symm.trans hZ)
    exact Or.inr ⟨c, σ, hσ, hc, hstar,
      normalizes_of_central_starImage H K (zero L) (hZK.trans hKH) (zero_isPPerfect L) hQ hstar,
      hB ▸ hres⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives
