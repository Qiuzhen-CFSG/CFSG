module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Quotient
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.SeedMarking
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Action
public import Theory.LinearAlgebra.BinaryFourCubicNormalForm

/-!
# Natural quotient selection from the marked residual factors

The binary cubic normal form is now proved independently. Consequently a
three-cycle in either candidate for L₀ acts without fixed points on every
faithful four-dimensional A₇-module and on its dual. The nonzero image of
the actual seed V₃ in an actual maximal quotient excludes both alternatives.
The resulting natural identification uses the original seven-point map.
Its invariant rank-two seed then orders the two residual factors.

These are conditional structural adapters: the unordered residual marking
and, for the ordered conclusion, the surjectivity of the seven-point map
still have to be established from the local group data. Neither is asserted
by the representation argument.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959/PDF pp.975–976
(combined manuscript, 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
open PairsBranch PairsBranch.ModuleSelection

/-- Discharge the universal linear-algebra premise of the model exclusion. -/
theorem cubicNormalForm : CubicNormalForm := by
  intro F _ _ _ hdim t ht htne hfixed
  exact BinaryFourCubic.exists_basis_fixedPlaneMatrix hdim t ht htne hfixed

universe u
variable {G : Type u} [Group G] [Finite G]
  (H K L₁ L₀ X T V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ)

/-- The unordered residual marking suffices to exclude the genuine four-space
and four-plus-dual alternatives in the literal maximal source quotient. -/
theorem source_natural_quotient_of_marked_factors
    (hKH : K ≤ H) (hcomm : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (hK : (Source.starImage H K).map φ = alternatingGroup (Fin 7))
    (hmonolith : ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ →
      Source.starImage H K ≤ N)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (hL : L₁ ≤ normalizer (V₃ : Set G))
    [IsIrreducible (sourceSeed H V₃ V₁ ρ hρ L₁ hL).toRepresentation]
    (hdim : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) = 2)
    (hcentral : L₀ ≤ centralizer (V₃ : Set G))
    (hmark : MarkedFactors φ (Source.starImage H L₀) (Source.starImage H X))
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hclass : SmallQuadraticInput.{_, u} φ
      (componentInclusion φ hφ (Source.starImage H K) hK)) :
    IsNatural W.quotientRepresentation φ ∧ HasNaturalSubmodule W.quotientRepresentation φ :=
  source_natural_quotient_of_cubic_normal_form H K L₁ L₀ V₃ V₁ ρ hρ hKH hcomm
    φ hφ hK hmonolith W hW hL hdim hcentral hmark.exists_threeCycle
    A hA hq hbound hclass cubicNormalForm

/-- Retain the same quotient and map when ordering the factors. The seed's
rank and local invariance are transported from U_H/V₁; no new seed is chosen. -/
theorem source_natural_quotient_and_ordered_factors
    (hKH : K ≤ H) (hcomm : Source.UH H V₃ = ⁅Source.UH H V₃, K⁆)
    (φ : Source.Hstar H →* Equiv.Perm (Fin 7)) (hφ : Function.Injective φ)
    (hsurj : Function.Surjective φ)
    (hK : (Source.starImage H K).map φ = alternatingGroup (Fin 7))
    (hmonolith : ∀ N : Subgroup (Source.Hstar H), N.Normal → N ≠ ⊥ →
      Source.starImage H K ≤ N)
    (W : Subrepresentation ρ) (hW : IsCoatom W)
    (hLH : L₁ ≤ H) (hTH : T ≤ H)
    (hL : L₁ ≤ normalizer (V₃ : Set G)) (hT : T ≤ normalizer (V₃ : Set G))
    [IsIrreducible (sourceSeed H V₃ V₁ ρ hρ L₁ hL).toRepresentation]
    (hdim : Module.finrank (ZMod 2) (sourceImage H V₃ V₁ V₃) = 2)
    (hcentral : L₀ ≤ centralizer (V₃ : Set G))
    (hgen : L₀ ⊔ X = L₁)
    (hP : Source.starImage H (L₁ ⊔ T) = fourThreeStabilizer.comap φ)
    (hmark : MarkedFactors φ (Source.starImage H L₀) (Source.starImage H X))
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hclass : SmallQuadraticInput.{_, u} φ
      (componentInclusion φ hφ (Source.starImage H K) hK)) :
    IsNatural W.quotientRepresentation φ ∧
      HasNaturalSubmodule W.quotientRepresentation φ ∧
      (Source.starImage H X).map φ = threeFactor ∧
      (Source.starImage H L₀).map φ = fourResidualFactor := by
  obtain ⟨hn, he⟩ := source_natural_quotient_of_marked_factors H K L₁ L₀ X V₃ V₁
    ρ hρ hKH hcomm φ hφ hK hmonolith W hW hL hdim hcentral hmark A hA hq hbound hclass
  let V := sourceSeed H V₃ V₁ ρ hρ L₁ hL
  let D := quotientSeed ρ (Source.starImage H L₁) W V
  have hstar : Source.starImage H L₁ ⊔ Source.starImage H T =
      Source.starImage H (L₁ ⊔ T) := (LocalGeometry.starImage_sup H L₁ T hLH hTH).symm
  have hsplit : Source.starImage H L₀ ⊔ Source.starImage H X = Source.starImage H L₁ := by
    rw [← LocalGeometry.starImage_sup H L₀ X
      ((le_sup_left.trans_eq hgen).trans hLH)
      ((le_sup_right.trans_eq hgen).trans hLH), hgen]
  have hstable : Source.starImage H L₁ ⊔ Source.starImage H T ≤
      subspaceStabilizer ρ V.toSubmodule := by
    rw [hstar]
    exact source_image_stable H V₃ V₁ ρ hρ (L₁ ⊔ T) V₃ (sup_le hL hT)
  have hlocal : ((Source.starImage H L₀ ⊔ Source.starImage H X) ⊔
      Source.starImage H T).map φ = fourThreeStabilizer := by
    rw [hsplit, hstar, hP, map_comap_eq_self_of_surjective hsurj]
  have hordered := ordered_marking_of_natural_seed W.quotientRepresentation φ
    (Source.starImage H L₀) (Source.starImage H X) (Source.starImage H T) hn hmark
    D.toSubmodule
    (quotientSeed_finrank ρ (Source.starImage H L₁) W hW.1 V
      (source_seed_generates H V₃ V₁ ρ hρ) hdim)
    (quotient_image_fixed ρ W V.toSubmodule (Source.starImage H L₀)
      (source_seed_fixed_of_centralizes H L₀ V₃ V₁ ρ hρ hcentral))
    (by rw [hsplit]; exact quotientSeed_stable ρ (Source.starImage H L₁) W V _ hstable)
    hlocal
  exact ⟨hn, he, hordered⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
