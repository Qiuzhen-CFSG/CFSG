module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.Alternatives
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel.Rank
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel.LocalInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel.Normalization

/-!
# The marked even-degree L₂ Borel placement in 13.8.20(a)

The actual Sylow marking selects B₀* inside K*. Solvability of L₁T makes
it normalize this Borel, and 13.8.13 puts the lift B₀ inside M. In even
degree, its residual B and the external cubic X give m₃(BX) > 1. The
exact theta identity excludes the ordinary A₆ local quotient.

For the covered natural flag, theta and the order-nine local quotient put
L₁ in BX. The T-invariant marked kernel of the cubic projection then
places L₀* in B*. Two-perfectness lifts this through O₂(H) ≤ T, giving
L₀ ≤ B. The local formula B_C = O³(B)L₀ consequently gives both B_C ≤ K
and B_C ≤ BX. The source index-three theorem now gives B ≤ C_G(V).

The explicit inputs are genuine standing data and earlier source conclusions:
the ordinary cubic local order, the covered natural flag, 13.2.2(3), the
§13.3 seed identity, 13.7.3(9), and the universal 13.8.13 exclusion. The
centralizing-residual formula, normalization of L, its centralization of V,
and the source index three remain the permitted local Borel identities.
No L₀ placement, B_C containment, or B-centralization is assumed. There is
no dependency on LocalBorel or on the parallel component-model reduction.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.20(a), printed p.954/PDF p.971.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
variable {G : Type*} [Group G] [Finite G]
variable (H K L T V V₁ V₃ M X : Subgroup G) (hKH : K ≤ H) [(K.subgroupOf H).Normal]
    (hgen : H = K ⊔ (one L T V₁ ⊔ T))
    (hT : Chapter1.IsSylowIn 2 T H)
    (hHV₁ : H ≤ normalizer (V₁ : Set G))
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁))
    (hordinary : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (one L T V₁ ⧸ pCore 2 (one L T V₁)) = 3)
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      Nonempty (LocalAction.NaturalSetup L T V V₁ V₃))
    (hfactor : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      one L T V₁ = plus L T V₁ ⊔ zero L)
    (hseed : V₃ = ⁅V₃, one L T V₁⁆)
    (htheta : one L T V₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (hex : ∀ J : Subgroup G, one L T V₁ ⊔ T ≤ J → J ≤ normalizer (V₁ : Set G) →
      Group.IsSolvable J → J ≤ M)
    (ha : ExternalXAlternative H K X)
    (S : Sylow 2 (Source.starImage H K))
    (hS : (S : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
      Source.starImage H T ⊓ Source.starImage H K)
    {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n)) (heven : Even n)

include hgen hT hHV₁ hlocal hordinary hcovered hfactor hseed htheta hex ha hS hn hmodel heven

/-- Derive the covered case and both required placements for the literal source lift. -/
theorem source_placements
    (hformula : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      let B := borelResidual (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
      centralizingResidual B (one L T V₁) L = residualIn 3 B ⊔ zero L) :
    let B := borelResidual (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
    1 < primeRank 3 (B ⊔ X : Subgroup G) ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      zero L ≤ B ∧ centralizingResidual B (one L T V₁) L ≤ K ∧
      centralizingResidual B (one L T V₁) L ≤ B ⊔ X := by
  let D := one L T V₁
  let B₀ := HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S)
  let B := borelResidual B₀
  have hDH : D ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hTp : IsPGroup 2 T := by
    obtain ⟨P,hP⟩ := hT
    rw [← hP]
    exact P.isPGroup'.map H.subtype
  obtain ⟨hXD,hXp,hXcard,hsol,_⟩ := selected_local_inputs L T V V₁ V₃ X hTp
    (hTH.trans hHV₁) hlocal hordinary hcovered hfactor hseed
  let : Group.IsSolvable (D ⊔ T : Subgroup G) := hsol
  obtain ⟨hn₀,hB₀M⟩ := source_borel_normalized_and_le_M H K D T (normalizer (V₁ : Set G)) M
    hKH hDH hTH S hn hmodel hS (hKH.trans hHV₁) ((sup_le hDH hTH).trans hHV₁) hex
  have hnB : D ⊔ T ≤ normalizer (B : Set G) :=
    hn₀.trans (normalizer_le_normalizer_characteristic_image B₀ (pResidual 2 B₀))
  have hBK : B ≤ K := (map_subtype_le _).trans (borelLift_le H K hKH _)
  have hBM : B ≤ M := (map_subtype_le _).trans hB₀M
  have hDM : D ≤ M := by
    rw [show D = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3} from htheta, closure_le]
    exact fun _ hx => hx.1.2
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hc : Nat.card (Source.starImage H X) = 3 := star_card_three H X ha.1 hXcard
  have hne : ¬ Source.starImage H X ≤ Source.starImage H K := by
    intro h
    exact ha.2.1 (LinearThree.Geometry.CoveredProduct.ResidualPlacement.le_of_star_le
      H K X hKH ha.1 hXp h)
  have hr : 1 < primeRank 3 (B ⊔ X : Subgroup G) :=
    rank_gt_one_of_external_cubic H K B X hKH hBK ha.1 hc hne ha.2.2.1
      (marked_borel_star_rank H K hKH S hn hmodel heven)
  have hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) :=
    hlocal.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  obtain ⟨hnot,hcov⟩ := covered_of_external_borel_rank H M L D B X (hBK.trans hKH) hBM
    ha.1 (hXD.trans hDM) htheta hmodels hordinary hr
  have hx : X = plus L T V₁ := by
    rcases hlocal with ⟨h,_⟩ | ⟨_,h⟩
    · exact (hnot h).elim
    · exact h
  obtain ⟨d⟩ := hcovered hcov
  have hf := hfactor hcov
  have hnX : D ≤ normalizer (X : Set G) := by rw [hx]; exact one_normalizes_plus L T V₁
  have hnJ : D ≤ normalizer ((B ⊔ X : Subgroup G) : Set G) :=
    (le_inf (le_sup_left.trans hnB) hnX).trans (normalizer_inf_normalizer_le_normalizer_sup B X)
  have hDJ : D ≤ B ⊔ X := marked_le_of_theta_rank H M D (B ⊔ X) htheta
    (sup_le (hBK.trans hKH) ha.1) (sup_le hBM (hXD.trans hDM)) hnJ
    (residual_isPPerfect _) (d.one_quotient_card hf) hr
  have hz : zero L ≤ B := zero_le_borel_of_marked_join H K B L T V V₁ V₃ d hf hKH hBK
    hDH hTH hT (le_sup_right.trans hnB) (isPPerfect_embedded_pResidual 2 B₀)
    (by simpa only [← hx] using hDJ) (by simpa only [← hx] using hc)
    (by simpa only [← hx] using hne) (by simpa only [← hx] using ha.2.2.1)
  have hCB : centralizingResidual B D L ≤ B := by
    rw [hformula hcov]
    exact sup_le (map_subtype_le _) hz
  exact ⟨hr,hcov,hz,hCB.trans hBK,hCB.trans le_sup_left⟩


/-- The source local index gives B-centralization after both placements
have been derived for the actual Borel lift. -/
theorem source_borel_centralizes
    (hformula : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      let B := borelResidual (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
      centralizingResidual B (one L T V₁) L = residualIn 3 B ⊔ zero L)
    (hL : let B := borelResidual (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
      B ⊔ one L T V₁ ≤ normalizer (L : Set G))
    (hindex : let B := borelResidual (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
      (centralizingResidual B (one L T V₁) L ⊔ B.pCoreIn 2).relIndex (B ⊔ X) = 3)
    (hC : let B := borelResidual (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S))
      centralizingResidual B (one L T V₁) L ≤ centralizer (V : Set G)) :
    borelResidual (HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S)) ≤
      centralizer (V : Set G) := by
  obtain ⟨_,_,_,hCK,hCJ⟩ := source_placements H K L T V V₁ V₃ M X hKH hgen hT hHV₁
    hlocal hordinary hcovered hfactor hseed htheta hex ha S hS hn hmodel heven hformula
  exact ExternalModules.borel_centralizes_of_local_index H K (one L T V₁) L X V hKH
    (SylowBorel.relativeBorel (Source.starImage H K) S) ha.2.1 hCK hCJ hL hindex hC

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.MarkedBorel

end
