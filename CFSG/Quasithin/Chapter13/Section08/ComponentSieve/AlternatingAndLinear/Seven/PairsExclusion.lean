module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch

/-!
# The three-pairs contradiction in 13.8.24

The branch outputs construct the natural quotient, nontrivial K-action on W,
rank one, and compatible natural submodules in both faithful sections. Apply
the earlier 13.8.23(4) implication only after proving its two premises. The
pointwise centralizer in each literal section is then exactly Uγ*, contradicting
the strict containment. All earlier inputs remain explicit; this theorem closes
the three-pairs branch and does not assert the remaining four-plus-three case.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.24,
printed p.959/PDF p.976, using 13.8.23(4) on printed p.958.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
universe u
variable {G : Type u} [Group G] [Finite G]
  (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The three-pairs branch is impossible from the earlier source inputs.
The strict-centralizer implication is exactly the used conclusion of 13.8.23(4);
neither its rank-one premise nor nontrivial component action is assumed. -/
theorem exclude_pair_partition
    (L L₁ T G₁ M K Uγ A₁ : Subgroup G)
    (a : LocalRank.CompatibleAction H K)
    (hplacement : Source.starImage H (L₁ ⊔ T) = pairStabilizer.comap a.φ)
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
    (hclass : ModuleSelection.SmallQuadraticInput.{u, u} a.φ
      (ModuleSelection.componentInclusion a.φ a.faithful (Source.starImage H K) a.component_image))
    (h1376 : CentralAction.AlternatingNaturalImplication L L₁ T G₁ M ρ)
    (hno : ModuleSelection.SevenPointNoStrongInput.{u})
    (hrec : ModuleSelection.SevenPointRecognitionInput.{u})
    (h23 : rank (Source.starImage H Uγ) = 1 →
      (∃ k ∈ Source.starImage H K, ∃ w : W.toSubmodule, W.toRepresentation k w ≠ w) →
      Source.starImage H Uγ < subspaceKernel W.toRepresentation
        (fixedSpace W.toRepresentation (Source.starImage H Uγ)) ⊤ ∨
      Source.starImage H Uγ < subspaceKernel W.quotientRepresentation
        (fixedSpace W.quotientRepresentation (Source.starImage H Uγ)) ⊤) : False := by
  have hp : Source.starImage H L₁ ⊔ Source.starImage H T = pairStabilizer.comap a.φ := by
    simpa only [Source.starImage, subgroupOf_sup (le_sup_left.trans hH.1.2)
      (le_sup_right.trans hH.1.2), Subgroup.map_sup] using hplacement
  obtain ⟨_, _, _, _, hKW, hr, _, _, hnatW, hnatQ, _, _, hcW, hcQ, _, _⟩ :=
    branch_outputs H V₃ V₁ L L₁ T G₁ M K Uγ A₁ a hp htheta
      hV₃ hVcomm hmodels hcovered ρ hρ hH hV₁ hK hLK hgen hmonolith hnorm
      hseed hdim W hW hA hquad hbound hcritical hD hclass h1376 hno hrec
  obtain ⟨jW, hjW, heW⟩ := hnatW
  obtain ⟨jQ, hjQ, heQ⟩ := hnatQ
  rcases h23 hr hKW with hs | hs
  · exact (ne_of_lt hs)
      (pointwiseCentralizer_of_fixedCodim_one W.toRepresentation a.φ a.faithful
        jW hjW heW hA hcW).symm
  · exact (ne_of_lt hs)
      (pointwiseCentralizer_of_fixedCodim_one W.quotientRepresentation a.φ a.faithful
        jQ hjQ heQ hA hcQ).symm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
