module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.Sieve
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.SourceModule
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.LocalRank
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.PairsBranch.ModuleSelection

/-!
# Assembly of the three-pairs branch

From the relative partition stabilizer we obtain m₃(L₁)=1 and exclude the
covered-A₆ local quotient. The actual rank-two seed excludes both exceptional
module alternatives. The selected natural quotient then makes 13.7.6(3)
applicable under the temporary assumption that K centralizes W. Its covered
conclusion contradicts the A₆ quotient, proving that K moves W.

Both alternatives of 13.8.22 now feed the module sieve. The explicit universal
B.3/B.4 inputs exclude strong FF-modules and recognize a natural submodule
in a transvection section. The seven-point calculation gives m(Uγ*)=1;
13.8.23's codimension argument gives compatible natural submodules and
transvections on both literal sections.

The theorem retains the earlier source identities and the universal earlier
classification implications as explicit inputs. Neither naturality of the
selected quotient, nontrivial action on W, nor rank one is an input. The
parent supplies 13.8.23(4) and owns the final A₇ exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.24,
printed p.959/PDF p.976; earlier inputs on printed pp.938–939 and 957–958.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch

private theorem transvections_of_fixedCodim_one
    {J E : Type*} [Group J] [AddCommGroup E] [Module (ZMod 2) E]
    [FiniteDimensional (ZMod 2) E]
    (σ : Representation (ZMod 2) J E) (hσ : Function.Injective σ)
    (A : Subgroup J) (hc : fixedCodim σ A = 1) :
    ∀ a ∈ A, a ≠ 1 → fixedCodim σ (zpowers a) = 1 := by
  intro a ha hne
  have hle : fixedSpace σ A ≤ fixedSpace σ (zpowers a) :=
    fun v hv b => hv ⟨b, (zpowers_le.mpr ha) b.property⟩
  have hn := Submodule.finrank_mono hle
  have hnA := fixedCodim_add_finrank σ A
  have hna := fixedCodim_add_finrank σ (zpowers a)
  have hp := fixedCodim_pos_of_faithful σ hσ (by simpa using hne : zpowers a ≠ ⊥)
  omega

universe u
variable {G : Type u} [Group G] [Finite G]
  (H V₃ V₁ : Subgroup G)
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]

/-- The substantive three-pairs outputs, on the actual source action and its
literal maximal quotient. The seed, quadratic actor and critical subspace
are the images of V₃, Uγ and D_H, respectively. The critical alternative is
F.9.13(6) after passing to U_H/V₁: its nonzero line is the image of A₁,
not the rank-two image of V₃. Its quotient bound is the earlier 13.8.10 input.

The remaining inputs are theta and the local-model alternatives, 13.8.21's
component, monolith and generation conclusions, the source seed's dimension
and irreducibility, case (2) of 13.8.8, and the named universal earlier
implications. All branch-specific intermediate conclusions are proved here. -/
theorem branch_outputs
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
    (hclass : ModuleSelection.SmallQuadraticInput.{u, u} a.φ
      (ModuleSelection.componentInclusion a.φ a.faithful (Source.starImage H K) a.component_image))
    (h1376 : CentralAction.AlternatingNaturalImplication L L₁ T G₁ M ρ)
    (hno : ModuleSelection.SevenPointNoStrongInput.{u})
    (hrec : ModuleSelection.SevenPointRecognitionInput.{u}) :
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
  obtain ⟨hrL, ⟨eL⟩⟩ := LocalRank.rank_and_quotient H M K L L₁ T V₃ a
    hplacement htheta hV₃ hVcomm hmodels hcovered
  have hcomm := source_commutator_generated H V₃ V₁ ρ hρ K a.component_le hgen
  let V := sourceSeed H V₃ V₁ ρ hρ L₁ (le_sup_left.trans hnorm)
  let : IsIrreducible V.toRepresentation := hseed
  have hstable : Source.starImage H L₁ ⊔ Source.starImage H T ≤
      subspaceStabilizer ρ V.toSubmodule :=
    sup_le (source_image_stable H V₃ V₁ ρ hρ L₁ V₃ (le_sup_left.trans hnorm))
      (source_image_stable H V₃ V₁ ρ hρ T V₃ (le_sup_right.trans hnorm))
  obtain ⟨e, he⟩ := ModuleSelection.natural_quotient ρ a.φ a.faithful
    (Source.starImage H K) (Source.starImage H L₁) (Source.starImage H T)
    a.component_image (map_mono (subgroupOf_mono H hLK)) hmonolith hcomm hplacement
    W hW V (source_seed_generates H V₃ V₁ ρ hρ) hdim hstable
    (Source.starImage H Uγ) hA hquad hbound hclass
  have heinv : ∀ g q, e.symm (W.quotientRepresentation g q) =
      BinaryPermutation.coreRepresentation (Fin 7) (a.φ g) (e.symm q) := by
    intro g q
    apply e.injective
    rw [e.apply_symm_apply, he, e.apply_symm_apply]
  have hKW := CentralAction.nontrivial_on_submodule L L₁ T G₁ M K ρ hH hV₁ hρ
    a.component_le hK hgen a.φ a.faithful a.component_image eL W e.symm heinv h1376
  obtain ⟨hnoW, hnoQ, hrecW, hrecQ⟩ := ModuleSelection.sieve_inputs ρ a.φ a.faithful
    (Source.starImage H K) a.component_image hno hrec W
  have hcrit :
      sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) Uγ A₁) ≤
        fixedSpace ρ (Source.starImage H Uγ) ∨
      ∃ S : Submodule (ZMod 2) (Additive (Source.Utilde H V₃ V₁)), IsAtom S ∧
        ∀ x ∈ Source.starImage H Uγ,
          ∀ d ∈ sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) Uγ A₁), ρ x d - d ∈ S :=
    hcritical.imp_right (fun h => ⟨sourceImage H V₃ V₁ A₁, h⟩)
  obtain ⟨hr, hfaithW, hfaithQ, hnatW, hnatQ, hcW, hcQ, hc, hfix⟩ :=
    rank_one_and_natural_sections ρ a.φ a.faithful W (Source.starImage H K)
      (Source.starImage H Uγ) hmonolith hW.1 hcomm hKW hA hbound
      (sourceImage H V₃ V₁ (Source.DH (Source.UH H V₃) Uγ A₁)) hcrit hD
      hnoW hnoQ hrecW hrecQ
  have hdimQ : Module.finrank (ZMod 2)
      ((Additive (Source.Utilde H V₃ V₁)) ⧸ W.toSubmodule) = 6 := by
    rw [← e.finrank_eq, BinaryPermutation.finrank_core]
    decide
  exact ⟨hrL, ⟨eL⟩, ⟨e, he⟩, hdimQ, hKW, hr, hfaithW, hfaithQ, hnatW, hnatQ,
    transvections_of_fixedCodim_one W.toRepresentation hfaithW _ hcW,
    transvections_of_fixedCodim_one W.quotientRepresentation hfaithQ _ hcQ,
    hcW, hcQ, hc, hfix⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.PairsBranch
