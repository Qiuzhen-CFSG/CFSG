module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking.Construction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking.KernelNormalization
public import Theory.Representation.HexacodeAction.Cover

/-!
# The source SL₃(4) Borel marking and kernel normalization

The source Sylow is constructed from T∩K through H/O₂(H) and the given
K* ≃ SL₃(4). Its lifted Borel residual B has the full Borel as star image,
B = θ(B), and three-rank two. The earlier B≤M and overlap theta identity
put B in L₁. Rank two excludes the ordinary A₆ case and selects an actual
isomorphism with the hexacode triple cover.

Notation 13.2.1 and 13.2.2(3) supply the cubic quotients and factorization.
Their relative normality makes L₁/O₂(L₁) a three-group, so the marked full
Sylow is normal in L₁*. Borel self-normalization identifies L₁* = B₀*.
The constructor proves every MarkedBorelFactors field for the actual
L₀ and L₁,+, including their own cores and the original t's action.
Independently, O₂,Z(L) = C_L(V) identifies L₀ with O²(C_{L₁}(V));
13.7.3(6),(9) then make Q_H normalize L₀.

This is the conditional source-marking task, not the automorphism
classification or the completed contradiction in 13.8.20. The exact earlier
source clauses listed in exists_source_marking remain explicit inputs,
including B≤M from the preceding Borel reduction. No marking, central-image
conclusion, equality M = N_G(L₀), or assumption t² = 1 is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and 13.2.2(3), printed p.877; the centralizer identity in
the proof of 13.2.2, p.878; 13.7.3(6),(9), p.936, and the local three-ranks
in the proof of 13.7.5, p.938; proof of 13.8.20, pp.954–955 (PDF 971–972).
-/

@[expose] public section
noncomputable section
open Subgroup Representation.SL3FourNaturalDual
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]

/-- Rank two of B rules out the ordinary A₆ case in the actual earlier model alternatives. -/
theorem covered_case (H K L T M V₁ : Subgroup G) [(Source.starImage H K).Normal]
    (eK : Source.starImage H K ≃* SL) (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    (hBM : sourceBorel H K T eK hKH hT ≤ M)
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      primeRank 3 (one L T V₁) = 1) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  rcases hmodels with hA | hA
  · have hle := sourceBorel_le_one H K T eK hKH hT L M V₁ hBM htheta
    have hr := Theory.GroupTheory.primeRank_le_of_injective 3 (inclusion hle)
      (inclusion_injective hle)
    rw [sourceBorel_threeRank H K T eK hKH hT, hordinary hA] at hr
    omega
  · exact hA

/-- Source-facing assembly. The earlier clauses are explicit, literal source statements:
B≤M from the preceding Borel reduction, the ordinary/covered local models and ordinary
three-rank from §13.7, Notation 13.2.1, 13.2.2(3), the p.878 centralizer identity,
and 13.7.3(6),(9). None assumes a marking or Q_H-normalization of L₀. -/
theorem exists_source_marking
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
      coreAction (plus L T V₁) ⟨t.val, T_normalizes_plus L T V₁ hTL hTV htT⟩ q = q⁻¹) :
    ∃ (_ : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
      (m : SourceBorelMarking H K L T V₁ eK (QuotientGroup.mk' (pCore 2 H) t)),
      (m.factors.sylow : Subgroup SL) = modelImage H K (T ⊓ K) eK ∧
      sourceBorel H K T eK hKH hT =
        closure {x : G | x ∈ sourceBorel H K T eK hKH hT ∧ orderOf x = 3} ∧
      sourceBorel H K T eK hKH hT ≤ one L T V₁ ∧
      primeRank 3 (sourceBorel H K T eK hKH hT) = 2 ∧
      Source.starImage H (one L T V₁) = modelBorel H K eK (sourceSylow H K T eK hT) ∧
      Source.QH H ≤ normalizer (zero L : Set G) := by
  obtain ⟨eL⟩ := covered_case H K L T M V₁ eK hKH hT hBM htheta hmodels hordinary
  obtain ⟨hfactor, hz, hx, hcentral⟩ := hcovered eL
  have hBL := sourceBorel_le_one H K T eK hKH hT L M V₁ hBM htheta
  let m := marking H K T eK hKH hT L V₁ hLK hTL hTV hfactor hz hx hBL t htT htL (hinv eL)
  refine ⟨eL, m, ?_, sourceBorel_theta H K T eK hKH hT, hBL,
    sourceBorel_threeRank H K T eK hKH hT,
    one_star_eq_borel H K T eK hKH hT L V₁ hLK hTL hTV hfactor hz hx hBL,
    kernel_normalizes_zero H L T M V V₁ V₃ hTL hfactor hcentral hcomm hV₃ hoverlap htheta⟩
  exact sourceSylow_intersection H K T eK hT

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.AutomorphismModule.LocalAlternatives.SourceMarking
