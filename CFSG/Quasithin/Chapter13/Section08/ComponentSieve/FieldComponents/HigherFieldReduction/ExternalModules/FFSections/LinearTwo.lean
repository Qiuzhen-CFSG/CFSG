module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.ActionCases
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NaturalSections
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.Invariance
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.NoStrongMoved
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo.FiveReconstruction
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction

/-!
# The external L₂ natural layer and moved-tensor alternative

The complete B.4.2 action list leaves the natural action over the original
field size or the marked S₅ action with n = 2. Thompson replacement and the
proved B.7.2(1) discharge the universal invariance input to the no-strong
reduction. Applying all F.9.18(6) alternatives to the actual two-conjugate
constituent orbit proves W = [U,K*] for the literal U = U_H/V₁.

In the natural branch, the central bottom is literally W ∩ C_U(K*), and
compatible constituent and multiplicity identifications construct the tensor
layer while preserving the original Borel marking. Both field parities are
retained. In the exceptional branch the complete earlier Fitting alternative
and solvable supplement give full marked S₅ × S₃ coordinates on W.
Restricting displacement and quadraticity to W then excludes that branch
using exactly the earlier 13.8.18(4) implication and the actual conjugate
placement. No whole-U tensor identification is needed.

`source_layer_or_moved_coordinates` proves the alternatives and the no-strong
and moved-space conclusions. `source_natural_layer` also supplies the
exceptional endpoint's earlier inputs and leaves only the natural layer for
`ExternalModules.Natural`. The genuine source setup, constituent and orbit
coordinates, Fitting and critical-actor inputs are explicit intermediate
premises to be discharged by the parent FFSections/ExternalModules assembly.
These are source-facing assembly helpers, not an unconditional 13.8.20.
The old conditional constituent and whole-space APIs remain available.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20, printed pp.954–955; B.4.2, pp.86–87; F.9.18(6), pp.325–326.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped MatrixGroups IsMulCommutative
open Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

universe u v w
variable {G : Type w} [Group G] [Finite G]
    (H K X V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (s : S₃ →* Source.Hstar H)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (W : Subrepresentation ρ)

local notation "Kstar" => Source.starImage H K
local notation "C" => centralBottom ρ Kstar W
local notation "κ" => MonoidHom.comp ρ (Subgroup.subtype (Source.starImage H K))

/-- Construct the literal natural layer or retain the full marked S₅ constituent.
The only classification input is the complete universal B.4.2 implication.
The faithful constituent hypotheses and compatibility maps are the intermediate
SourceOrbit output; the still-needed moved-space equality is displayed explicitly. -/
theorem source_layer_or_five_constituent
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,v} 𝒦)
    {E : Type u} [Group E] [Finite E]
    {N : Type v} [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N)
    (hσ : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (b : Kstar ≃* generalizedFitting E)
    (a : SectionMultiplicity ρ s C W ≃ₗ[ZMod 2] N)
    (ha : ∀ k v, a (sectionMultiplicityAction ρ (Kstar).subtype s hs C W k v) =
      σ (b k) (a v))
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSL Kstar 2 (2^n))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hgen : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ Kstar)
    (S : Sylow 2 Kstar) (B₀ : Subgroup (Source.Hstar H))
    (hB : B₀.subgroupOf Kstar = normalizer (S : Set Kstar)) :
    (∃ F : BinaryField, F.degree = n ∧ ∃ e : Kstar ≃* SL(2,F.Carrier),
      (B₀.subgroupOf Kstar).map e.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F.Carrier ∧
      (C).toSubmodule ≤ Representation.invariants κ ∧
      (∀ (g : Kstar) (u : SeedAction.Space H V₃ V₁), κ g u - u ∈ W.toSubmodule) ∧
      Nonempty (NaturalLayers.TensorLayer κ (linearNatural F 2) e (C).toSubmodule W.toSubmodule)) ∨
    (n = 2 ∧ Nonempty (MarkedActionEquiv σ (offenderSubgroup σ) (generalizedFitting E)
      (BinaryPermutation.naturalRepresentation (Fin 5)) (alternatingGroup (Fin 5)))) := by
  have hm' : ClassicalGroup.IsPSL (generalizedFitting E) 2 (2^n) := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
    exact ⟨F, inferInstance, inferInstance, hF, ⟨b.symm.trans e⟩⟩
  cases constituentCase_of_ff σ hB42 hσ hff hn hm' with
  | natural F hF _ e =>
    left
    have ha' : ∀ k v,
        (a.trans e.linearEquiv) (sectionMultiplicityAction ρ (Kstar).subtype s hs C W k v) =
          HigherFieldBorelFixedSpaces.binaryNatural 2 ((b.trans e.groupEquiv) k)
            ((a.trans e.linearEquiv) v) := by
      intro k v
      change e.linearEquiv (a (sectionMultiplicityAction ρ (Kstar).subtype s hs C W k v)) = _
      rw [ha]
      exact e.intertwines (b k) (a v)
    obtain ⟨e', hB', hc, hq, layer⟩ := natural_layer ρ Kstar W s hs S
      (B₀.subgroupOf Kstar) hB (by rw [hmark]; exact hgen) hW
      (b.trans e.groupEquiv) (a.trans e.linearEquiv) ha'
    exact ⟨F, hF, e', hB', hc, hq, layer⟩
  | five hn e => exact Or.inr ⟨hn, ⟨e⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

end

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped MatrixGroups IsMulCommutative
open Theory.GroupTheory
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

universe u v

private theorem orbit_eq_of_two_conjugates
    {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (W : Subrepresentation ρ)
    (I : Submodule (ZMod 2) U) (x : D)
    (he : W.toSubmodule = I ⊔ I.map (ρ x)) : W.toSubmodule = orbitSpan ρ ⊤ I := by
  apply le_antisymm
  · rw [he]
    exact sup_le (le_orbitSpan ρ ⊤ I)
      (le_iSup (fun g : (⊤ : Subgroup D) => I.map (ρ g)) ⟨x, mem_top x⟩)
  · apply orbitSpan_le ρ (by rw [he]; exact le_sup_left)
    apply le_subspaceStabilizer
    intro g _ v hv
    exact W.apply_mem_toSubmodule g hv

section SourceAssembly
variable {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}} (hB42 : FullB42.{u,u} 𝒦)
    (H K X L L₁ L₁plus V₃ V₁ : Subgroup G) (T : Sylow 2 G)
    [(K.subgroupOf H).Normal] [(X.subgroupOf H).Normal]
    [(Source.starImage H K).Normal]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [Group.IsSolvable (L₁ ⊔ (T : Subgroup G) : Subgroup G)]
    (hH : IsSQTK 𝒦 H) (hgen : H = K ⊔ L₁ ⊔ (T : Subgroup G))
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = L₁) ∨
      (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧ X = L₁plus))
    (hfit : SolvableExclusion.ResidualAlternative L L₁ L₁plus
      (Components.Fitting.twoFittingResidual H))
    (hK : IsComponent (Source.Hstar H) (Source.starImage H K))
    {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn : 1 < n) (hcard : Nat.card F = 2^n)
    (eK : Source.starImage H K ≃* PSL(2,F))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (hρ : SeedAction.IsConjugation H V₃ V₁ ρ) (hfaithful : Function.Injective ρ)
    (s : S₃ →* Source.Hstar H) (hinj : Function.Injective s)
    (hs : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X)
    (hcubic : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤)
    {E N : Type u} [Group E] [Finite E]
    [AddCommGroup N] [Module (ZMod 2) N] [Finite N]
    (σ : Representation (ZMod 2) E N) (hσ : B4Hypotheses 𝒦 σ) (hff : IsFFModule σ)
    (r : FiveReconstruction.ConstituentRealization ρ (Source.starImage H K) σ
      (generalizedFitting E))
    (hactor : r.actor = Source.starImage H K ⊔ Source.starImage H (T : Subgroup G))
    (W : Subrepresentation ρ)
    (hne : r.space ≠ r.space.map (ρ (s cubic)))
    (horbit : W.toSubmodule = r.space ⊔ r.space.map (ρ (s cubic)))
    (a : SectionMultiplicity ρ s (centralBottom ρ (Source.starImage H K) W) W
      ≃ₗ[ZMod 2] N)
    (ha : ∀ k v,
      a (sectionMultiplicityAction ρ (Source.starImage H K).subtype s hs
        (centralBottom ρ (Source.starImage H K) W) W k v) = σ (r.component k) (a v))
    (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
    (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
    (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
    (S : Sylow 2 (Source.starImage H K)) (B₀ : Subgroup (Source.Hstar H))
    (hB : B₀.subgroupOf (Source.starImage H K) = normalizer (S : Set (Source.starImage H K)))

local notation "Kstar" => Source.starImage H K
local notation "C" => centralBottom ρ Kstar W
local notation "κ" => MonoidHom.comp ρ (Subgroup.subtype (Source.starImage H K))

include hB42 hH hgen hlocal hfit hK hn hcard eK hρ hfaithful hinj hs hmark hcubic
  hσ hff hactor hne horbit ha hA hAquad hbound hAfaith hB in
/-- Assemble the external L₂ alternatives from the actual source action and
realized KT constituent. The complete earlier Fitting alternative is selected
using the ordinary/covered local carrier. B.7.2 and replacement discharge
invariance; the two-conjugate orbit supplies the H-orbit input; no-strong and
both-FF exclusions prove the moved-space equality. The exceptional coordinates
are on W, with faithfulness proved from the source structural data. -/
theorem source_layer_or_moved_coordinates :
    Source.starImage H (T : Subgroup G) ≤ subspaceStabilizer ρ r.space ∧
    ¬ IsStrongFFModule (ρ.comp (Kstar ⊔ Source.starImage H (T : Subgroup G)).subtype) ∧
    (∀ C' D : Subrepresentation ρ,
      (¬ ∀ k ∈ Kstar, ∀ v, sectionRepresentation ρ C' D k v = v) →
      Function.Injective (sectionRepresentation ρ C' D) ∧
        ¬ IsStrongFFModule (imageRepresentation ((sectionRepresentation ρ C' D).comp
          (Kstar ⊔ Source.starImage H (T : Subgroup G)).subtype))) ∧
    W.toSubmodule = subspaceCommutator ρ ⊤ Kstar ∧
    ((∃ F' : BinaryField, F'.degree = n ∧ ∃ e : Kstar ≃* SL(2,F'.Carrier),
      (B₀.subgroupOf Kstar).map e.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F'.Carrier ∧
      (C).toSubmodule ≤ Representation.invariants κ ∧
      (∀ (g : Kstar) (u : SeedAction.Space H V₃ V₁), κ g u - u ∈ W.toSubmodule) ∧
      Nonempty (NaturalLayers.TensorLayer κ (linearNatural F' 2) e (C).toSubmodule W.toSubmodule)) ∨
      (n = 2 ∧ Nonempty (FiveReconstruction.FullCoordinates W.toRepresentation Kstar s))) := by
  have hselected := Structure.selected_fitting_alternative H L L₁ L₁plus X hlocal hfit
  obtain ⟨hno, hsections, hmoved⟩ := NoStrongMoved.source_no_strong_and_moved
    hB42 fullIrrInvariance H K X L₁ (T : Subgroup G) V₃ V₁ hH
    (by simpa only [sup_assoc] using hgen) hselected hK n hn hcard eK
    ρ hρ hfaithful s hinj hs hmark hcubic r.space r.irrPlus W
    (orbit_eq_of_two_conjugates ρ W r.space (s cubic) horbit) A hA hAquad hbound hAfaith
  refine ⟨?_, hno, hsections, hmoved, ?_⟩
  · exact le_trans (by rw [hactor]; exact le_sup_right) r.stable
  · rcases source_layer_or_five_constituent H K X V₃ V₁ ρ s hs W hB42 σ hσ hff
      r.component a ha hn ⟨F, inferInstance, inferInstance, hcard, ⟨eK⟩⟩
      hmark hcubic hmoved S B₀ hB with hnatural | ⟨hn₂, ⟨efive⟩⟩
    · exact Or.inl hnatural
    · exact Or.inr ⟨hn₂, FiveReconstruction.source_moved_full_coordinates
        H K X V₃ V₁ ρ s hs W L L₁ L₁plus (T : Subgroup G) hgen hlocal hfit
        σ efive r a ha hmark hcubic hne horbit⟩

include hB42 hH hgen hlocal hfit hK hn hcard eK hρ hfaithful hinj hs hmark hcubic
  hσ hff hactor hne horbit ha hA hAquad hbound hAfaith hB in
/-- The adequate L₂ source assembly: only the natural layer survives once
13.8.18(4), the actual H-conjugate placement, and source quadraticity are supplied.
The exceptional branch proves the no-transvection antecedent on U and uses
the faithful tensor action on W. No faithfulness-on-W, W = U, specialized
classification alternative, or final contradiction is an input. The original
Borel and both field parities are preserved for the natural endpoint. -/
theorem source_natural_layer
    (Vγ Vα T₀ : Subgroup G)
    (earlier_13_8_18_4 : SeedAction.IsConjugation H V₃ V₁ ρ →
      H = K ⊔ L₁ ⊔ (T : Subgroup G) →
      (∀ g, Module.finrank (ZMod 2) (LinearMap.range (ρ g - LinearMap.id)) ≠ 1) →
      1 < rank (Source.starImage H Vγ))
    (hVγH : Vγ ≤ H) (h : H)
    (hconj : Vγ.map (MulAut.conj (h : G)).toMonoidHom = Vα)
    (hplace : Source.starImage H Vα ≤ Source.starImage H T₀)
    (hcore : Source.starImage H T₀ =
      (Source.starImage H L₁ ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2)
    (hT₀K : Source.starImage H T₀ ≤ Kstar)
    (hquad : IsQuadratic ρ (Source.starImage H Vγ)) :
    ∃ F' : BinaryField, F'.degree = n ∧ ∃ e : Kstar ≃* SL(2,F'.Carrier),
      (B₀.subgroupOf Kstar).map e.toMonoidHom = Matrix.SpecialLinearGroup.rankOneBorel F'.Carrier ∧
      (C).toSubmodule ≤ Representation.invariants κ ∧
      (∀ (g : Kstar) (u : SeedAction.Space H V₃ V₁), κ g u - u ∈ W.toSubmodule) ∧
      Nonempty (NaturalLayers.TensorLayer κ (linearNatural F' 2) e (C).toSubmodule W.toSubmodule) := by
  obtain ⟨_, _, _, _, hcase⟩ := source_layer_or_moved_coordinates hB42
    H K X L L₁ L₁plus V₃ V₁ T hH hgen hlocal hfit hK n hn hcard eK
    ρ hρ hfaithful s hinj hs hmark hcubic σ hσ hff r hactor W hne horbit a ha
    A hA hAquad hbound hAfaith S B₀ hB
  rcases hcase with hnatural | ⟨_, ⟨c⟩⟩
  · exact hnatural
  · exact (FiveReconstruction.tensor_branch_impossible_on_moved
      H K L₁ V₃ V₁ Vγ Vα T₀ T ρ s W hρ hgen c earlier_13_8_18_4
      hVγH h hconj hplace hcore hT₀K hquad).elim

end SourceAssembly
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.LinearTwo

end
