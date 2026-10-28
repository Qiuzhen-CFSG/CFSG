module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.CubicParity
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Structure.ResidualFactors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.FourThreeBranch.NaturalSelection.Selection

/-!
# Structural and natural-module selection in the four-plus-three branch

Starting with the actual action of H/O₂(H), the theta identity and 13.8.13
identify the relative stabilizer with H ∩ M and lift an elementary nine into
L₁. The earlier A₆/covered-A₆ alternatives therefore select the covered
quotient. Only then do we use the earlier local residual calculation: its
fixing/inverting actor forces an odd permutation, and its two-perfect factors
give the unordered O² marking. Thus the given faithful map fills S₇.

For the literal U_H/V₁ representation and an actual maximal proper
subrepresentation W, the genuine B.4 alternatives select a natural quotient
for that same map. The generating rank-two seed survives in this quotient;
its L₀-fixedness excludes the four-dimensional and four-plus-dual models,
and its local invariance orders the residual factors.

The earlier source facts remain precise inputs: the solvable-overgroup
implication, theta identity, actual quotient alternatives and their local
calculations, component generation and monolith property, source seed
properties, quadratic bound, and universal B.4 implication. Surjectivity,
residual markings and naturality are all conclusions. This completes the
selection step, not the later reciprocal-actor contradiction.

Source: Aschbacher–Smith, 13.8.24, printed pp.958–959/PDF pp.975–976,
using Notation 13.2.1, 13.2.2(3), 13.7.3(9), 13.7.5 and 13.8.13,21–23
(combined manuscript, 1 March 2004).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
open PairsBranch PairsBranch.ModuleSelection

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The structural deductions from the earlier local statements. In particular,
the elementary-nine local residual input is used only after the covered
alternative has been proved from the permutation geometry. -/
theorem source_structure
    (H K L L₁ L₀ X T G₁ M : Subgroup G)
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
      Nonempty (LocalResidualData L₁ L₀ X T)) :
    relativeStabilizer H φ = H ⊓ M ∧
      primeRank 3 L₁ = 2 ∧
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
      (Source.starImage H L₁).map φ = fourThreeTheta ∧
      Function.Surjective φ ∧
      MarkedFactors φ (Source.starImage H L₀) (Source.starImage H X) := by
  have hAlt : alternatingGroup (Fin 7) ≤ φ.range := by
    rw [← hK]
    rintro y ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  have hstab := relativeStabilizer_eq_inter_of_theta H L₁ T G₁ M
    hbase hHG htheta h13 φ hφ hAlt hP.le
  obtain ⟨hrank, hcovered⟩ := rank_and_covered_quotient_of_theta H L₁ T G₁ M L
    hbase hHG htheta h13 φ hφ hAlt hP.le hmodels ha6
  have hTheta := local_image_eq_fourThreeTheta H L₁ T G₁ M
    hbase hHG htheta h13 φ hφ hAlt hP.le
  obtain ⟨d⟩ := hlocal hcovered
  have hsurj := surjective_of_localResidualData H L₁ L₀ X T hbase φ hφ hAlt hP d hTheta
  have hmark := ResidualFactors.markedFactors_of_localResidualData
    H L₁ L₀ X T hbase φ hP.le d hTheta
  exact ⟨hstab, hrank, hcovered, hTheta, hsurj, hmark⟩

variable (H K L L₁ L₀ X T G₁ M V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
  (hρ : CentralAction.IsSourceAction H V₃ V₁ ρ)

/-- Source selection for case (2) of 13.8.8 in the four-plus-three partition.
The same faithful seven-point map is proved surjective and identifies the
literal maximal quotient with the natural module. Neither model selection,
exceptional-model exclusion nor either factor marking is an input. -/
theorem source_natural_quotient
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
    (hclass : SmallQuadraticInput.{_, u} φ
      (componentInclusion φ hφ (Source.starImage H K) hK)) :
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
  obtain ⟨hstab, hrank, hcovered, hTheta, hsurj, hmark⟩ :=
    source_structure H K L L₁ L₀ X T G₁ M hbase hHG htheta h13
      φ hφ hK hP hmodels ha6 hlocal
  obtain ⟨d⟩ := hlocal hcovered
  let := hseed
  have hselection := source_natural_quotient_and_ordered_factors H K L₁ L₀ X T V₃ V₁
    ρ hρ hKH hcomm φ hφ hsurj hK hmonolith W hW
    (le_sup_left.trans hbase) (le_sup_right.trans hbase)
    (le_sup_left.trans hnorm) (le_sup_right.trans hnorm)
    hdim hcentral d.generated hP hmark A hA hq hbound hclass
  have hlocalImage : (Source.starImage H (L₁ ⊔ T)).map φ = fourThreeStabilizer := by
    rw [hP, map_comap_eq_self_of_surjective hsurj]
  exact ⟨hstab, hrank, hcovered, hTheta, hsurj, hlocalImage, hselection⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.FourThreeBranch.NaturalSelection
