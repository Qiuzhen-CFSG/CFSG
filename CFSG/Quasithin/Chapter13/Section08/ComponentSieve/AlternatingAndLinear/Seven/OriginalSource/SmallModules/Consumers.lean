module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.SmallModules
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.OriginalSource.SevenPointInputs
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection
/-!
# Both source partition consumers with the appendix inputs discharged

The marked small-module classification and arbitrary faithful seven-point
module theorems now feed both literal source branches. The three-pairs branch
constructs rank one and both natural sections; the four-plus-three branch
constructs the natural maximal quotient and its residual markings. Only
preceding local-source and critical geometry inputs remain explicit. Final
original-family assembly is owned by qt-d-138-linear-seven-source, with
preceding source premises supplied through qt-d-138-linear-source.

Source: Aschbacher–Smith 13.8.24, printed pp.958–959/PDF pp.975–976.
-/
public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
open PairsBranch PairsBranch.ModuleSelection
open FourThreeBranch.NaturalSelection
universe u
variable {G : Type u} [Group G] [Finite G]
section Pair
variable (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
theorem source_pair_branch_outputs
    (L L₁ T G₁ M K Uγ A₁ : Subgroup G)
    (a : LocalRank.CompatibleAction H K)
    (hplacement : Source.starImage H L₁ ⊔ Source.starImage H T = pairStabilizer.comap a.φ)
    (htheta : L₁ = LocalRank.theta (H ⊓ M))
    (hV₃ : V₃ ≠ ⊥) (hVcomm : ⁅V₃, L₁⁆ = V₃)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (hcovered : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      primeRank 3 L₁ = 2)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hV₁ : V₁ ≤ Source.UH H V₃)
    (hK : (K.subgroupOf H).IsCComponent) (hLK : L₁ ≤ K)
    (hgen : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hmonolith : ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ →
      Source.starImage H K ≤ N)
    (hnorm : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hseed : IsIrreducible
      (sourceSeed H V₃ V₁ ρ hρ L₁ (le_sup_left.trans hnorm)).toRepresentation)
    (hdim : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) = 2)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (hA : IsElementaryTwo (Source.starImage H Uγ))
    (hquad : IsQuadratic ρ (Source.starImage H Uγ))
    (hbound : fixedCodim ρ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ))
    (hcritical :
      sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) Uγ A₁) ≤
        fixedSpace ρ (Source.starImage H Uγ) ∨
      IsAtom (sourceImage H V₃ V₁ A₁) ∧
        ∀ x ∈ Source.starImage H Uγ,
          ∀ d ∈ sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) Uγ A₁),
            ρ x d - d ∈ sourceImage H V₃ V₁ A₁)
    (hD : Module.finrank (ZMod 2)
      ((Additive (Source.Utilde H V₃ V₁)) ⧸
        sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) Uγ A₁)) ≤
          rank (Source.starImage H Uγ))
    (h1376 : CentralAction.AlternatingNaturalImplication L L₁ T G₁ M ρ)
 :
    primeRank 3 L₁ = 1 ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
    (∃ e : BinaryPermutation.core (Fin 7) ≃ₗ[ZMod 2]
        ((Additive (Source.Utilde H V₃ V₁)) ⧸ W.toSubmodule),
      ∀ g v, e (BinaryPermutation.coreRepresentation (Fin 7) (a.φ g) v) =
        W.quotientRepresentation g (e v)) ∧
    Module.finrank (ZMod 2) ((Additive (Source.Utilde H V₃ V₁)) ⧸ W.toSubmodule) = 6 ∧
    (∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w) ∧
    rank (Source.starImage H Uγ) = 1 ∧
    Function.Injective W.toRepresentation ∧ Function.Injective W.quotientRepresentation ∧
    HasNaturalSubmodule W.toRepresentation a.φ ∧
    HasNaturalSubmodule W.quotientRepresentation a.φ ∧
    (∀ x ∈ Source.starImage H Uγ, x ≠ 1 → fixedCodim W.toRepresentation (zpowers x) = 1) ∧
    (∀ x ∈ Source.starImage H Uγ, x ≠ 1 → fixedCodim W.quotientRepresentation (zpowers x) = 1) ∧
    fixedCodim W.toRepresentation (Source.starImage H Uγ) = 1 ∧
    fixedCodim W.quotientRepresentation (Source.starImage H Uγ) = 1 ∧
    fixedCodim ρ (Source.starImage H Uγ) = 2 ∧
    (fixedSpace ρ (Source.starImage H Uγ)).map W.toSubmodule.mkQ =
      fixedSpace W.quotientRepresentation (Source.starImage H Uγ) := by
  exact PairsBranch.branch_outputs H V₃ V₁ L L₁ T G₁ M K Uγ A₁ a hplacement htheta
    hV₃ hVcomm hmodels hcovered ρ hρ hH hV₁ hK hLK hgen hmonolith hnorm hseed hdim
    W hW hA hquad hbound hcritical hD
    (source_small_quadratic a.φ a.faithful (Source.starImage H K) a.component_image)
    h1376 sevenPointNoStrongInput sevenPointRecognitionInput

end Pair
section FourThree
variable (H K L L₁ L₀ X T G₁ M V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ)
theorem source_four_three_natural_quotient
    (hbase : L₁ ⊔ T ≤ H) (hHG : H ≤ G₁)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (hK : (Source.starImage H K).map φ = alternatingGroup (Fin 7))
    (hP : Source.starImage H (L₁ ⊔ T) = fourThreeStabilizer.comap φ)
    (hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))
    (ha6 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (hlocal : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) →
      Nonempty (LocalResidualData L₁ L₀ X T))
    (hKH : K ≤ H) (hcomm : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (hmonolith : ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ →
      Source.starImage H K ≤ N)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (hnorm : L₁ ⊔ T ≤ normalizer (V₃ : Set G))
    (hseed : IsIrreducible
      (sourceSeed H V₃ V₁ ρ hρ L₁ (le_sup_left.trans hnorm)).toRepresentation)
    (hdim : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) = 2)
    (hcentral : L₀ ≤ centralizer (V₃ : Set G))
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
 :
    relativeStabilizer H φ = H ⊓ M ∧
      primeRank 3 L₁ = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      (Source.starImage H L₁).map φ = fourThreeTheta ∧
      Function.Surjective φ ∧
      (Source.starImage H (L₁ ⊔ T)).map φ = fourThreeStabilizer ∧
      IsNatural W.quotientRepresentation φ ∧
      HasNaturalSubmodule W.quotientRepresentation φ ∧
      (Source.starImage H X).map φ = threeFactor ∧
      (Source.starImage H L₀).map φ = fourResidualFactor := by
  exact FourThreeBranch.NaturalSelection.source_natural_quotient
    H K L L₁ L₀ X T G₁ M V₃ V₁ ρ hρ hbase hHG htheta h13 φ hφ hK hP
    hmodels ha6 hlocal hKH hcomm hmonolith W hW hnorm hseed hdim hcentral A hA hq hbound
    (source_small_quadratic φ hφ (Source.starImage H K) hK)

end FourThree
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.OriginalSource
