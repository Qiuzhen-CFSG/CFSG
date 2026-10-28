module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SourceAssembly.Local

/-!
# Higher-field reduction to the exceptional outer-action alternative

This assembles the proof of 13.8.20 through “Therefore (b) holds.” The
source input retains the standing configuration, the legitimate H = KL₁T
reduction, all seven actual higher-field models and the exact earlier
local results. The ordinary and covered natural actions construct the
normalized source contexts and the original marked inverter.

In the external branch its strengthened Sylow-centralizer inverter proves
B ≤ C_G(V). The Borel is identified with the lift at the same component
Sylow used by the external theorem. The complete source external family
then supplies the rank sieve, supplement generation, FF and tensor branches,
and the same selected critical witness with its component placement.
Thus only the unchanged exceptional carrier and outer action remain.
The covered endpoint also retains fixation of the zero direction.

The full earlier F.9.18 and B.4.2 implications, their genuine source action
hypotheses, the earlier quadratic offender, and the enumerated earlier
critical geometry remain explicit, as authorized for this conditional
chapter reduction. No Borel centralization, auxiliary generation, selected
FF alternative, Sylow inverter or component-core equality is an input.
The field-component parent owns the subsequent exceptional-case exclusions.

Source: Aschbacher–Smith, proof of 13.8.20, printed pp.954–955,
through alternative (b), combined manuscript of 1 March 2004.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SourceAssembly
open LocalBorel LocalBorel.CentralizingCalculation
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
open ExternalModules
universe u v
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
local notation "D" => one L (T : Subgroup G) V₁

section Endpoint
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable [(K.subgroupOf H).Normal]
  [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
  (i : SourceInput.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : FFSections.SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁) (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (hmodel : Structure.HigherFieldCarrier (Source.starImage H K))
  (h12 : SolvableExclusion.ResidualAlternative L (one L (T : Subgroup G) V₁) (plus L (T : Subgroup G) V₁)
    (SolvableExclusion.residualInM H M))
  (hseed : V₃ = ⁅V₃, one L (T : Subgroup G) V₁⁆)
  (hF918 : FFSections.SourceOrbit.FullF918Four 𝒦) (hB42 : FullB42.{u,u} 𝒦)
  (A : Subgroup (Source.Hstar H)) (hA : IsElementaryTwo A)
  (hAquad : IsQuadratic ρ A) (hbound : fixedCodim ρ A ≤ 2 * rank A)
  (hAfaith : A ⊓ centralizer (Source.starImage H K : Set (Source.Hstar H)) = ⊥)
  (initial : CriticalGeometry.CriticalPair L (T : Subgroup G) H V)
  (e : CriticalInputs.EarlierInputs L (T : Subgroup G) H V V₃ V₁ ρ)

include i f hmodel h12 hseed hF918 hB42 hA hAquad hbound hAfaith initial e

/-- In the ordinary source case, the full dichotomy has only alternative (b).
The Sylow-centralizer inverter and Borel centralization are proved intermediates. -/
theorem exceptionalOuter_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G)) (hinv : InvertsTwoCoreQuotient D t.val) :
    ExceptionalOuterAlternative.{u,v} H K
      (QuotientGroup.mk' (pCore 2 H) ⟨t.val, i.member.1.2 (mem_sup_right t.property.1)⟩) := by
  let c := i.ordinarySourceContext a
  rcases c.sylowBorelAlternative_ordinary a t hinv with he | hb
  · have hcentral := ordinary_borel_centralizes c a he
    rw [borel_eq_external c f.component_le] at hcentral
    have hs := (Structure.MarkedBorel.ordinary_local_inputs L (T : Subgroup G) V₁
      T.isPGroup' i.standing.line_stable (source_residual_quotient_card a D rfl)).2
    exact (SourceCalculation.external_impossible H K D L V V₃ V₁ M T ρ P f
      (sourceSylow H K (T : Subgroup G) c.sylow_H)
      (ordinaryEarlierLocalData c a hseed i.universal) he.1 (module_le_H c) hmodel
      (fitting_alternative c hs i.universal h12) hcentral hF918 hB42
      A hA hAquad hbound hAfaith initial e).elim
  · exact hb

/-- In the covered source case, use J=BL₁ and the actual marked plus direction.
The full-product theorem centralizes B without a zero-placement or core-equality premise. -/
theorem exceptionalOuter_covered (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = plus L (T : Subgroup G) V₁ ⊔ zero L)
    (t : ((T : Subgroup G) ⊓ L : Subgroup G))
    (hinv : InvertsTwoCoreQuotient (plus L (T : Subgroup G) V₁) t.val) :
    ExceptionalOuterAlternative.{u,v} H K
      (QuotientGroup.mk' (pCore 2 H) ⟨t.val, i.member.1.2 (mem_sup_right t.property.1)⟩) := by
  let c := i.coveredSourceContext a hfactor
  rcases c.sylowBorelAlternative_covered a hfactor t hinv with he | hb
  · have hcentral := Covered.ZeroPlacement.FullProduct.External.borel_centralizes_of_Tstar_inverter
      c a hfactor he.1.2.2.2.1 he.2
    rw [borel_eq_external c f.component_le] at hcentral
    have hs := (Structure.MarkedBorel.covered_local_inputs L (T : Subgroup G) V V₁ V₃
      a hfactor hseed).2.2.1
    exact (SourceCalculation.external_impossible H K (plus L (T : Subgroup G) V₁) L V V₃ V₁ M T ρ P f
      (sourceSylow H K (T : Subgroup G) c.sylow_H)
      (coveredEarlierLocalData c a hfactor hseed i.universal) he.1 (module_le_H c) hmodel
      (fitting_alternative c hs i.universal h12) hcentral hF918 hB42
      A hA hAquad hbound hAfaith initial e).elim
  · exact hb

/-- The ordinary source endpoint constructs the prescribed inverter and proves
its unchanged exceptional-carrier and outer-action conclusion. -/
theorem exists_exceptionalOuter_ordinary (a : NaturalSetup L (T : Subgroup G) V V₁) :
    i.B ≤ M ∧ ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient D t.val ∧
      ExceptionalOuterAlternative.{u,v} H K
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, i.member.1.2 (mem_sup_right t.property.1)⟩) := by
  obtain ⟨hB, t, hinv, _⟩ := i.sylowBorelAlternative_ordinary a
  exact ⟨hB, t, hinv, exceptionalOuter_ordinary i ρ P f hmodel h12 hseed
    hF918 hB42 A hA hAquad hbound hAfaith initial e a t hinv⟩

/-- The covered endpoint also preserves fixation of the zero direction by the
same prescribed t; neither a Sylow inverter nor Borel centralization is assumed. -/
theorem exists_exceptionalOuter_covered (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
    (hfactor : D = plus L (T : Subgroup G) V₁ ⊔ zero L) :
    i.B ≤ M ∧ ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      InvertsTwoCoreQuotient (plus L (T : Subgroup G) V₁) t.val ∧
      coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1 ∧
      ExceptionalOuterAlternative.{u,v} H K
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, i.member.1.2 (mem_sup_right t.property.1)⟩) := by
  obtain ⟨hB, t, hinv, hz, _⟩ := i.sylowBorelAlternative_covered a hfactor
  exact ⟨hB, t, hinv, hz, exceptionalOuter_covered i ρ P f hmodel h12 hseed
    hF918 hB42 A hA hAquad hbound hAfaith initial e a hfactor t hinv⟩

/-- The higher-field Borel reduction in 13.8.20: the external alternative
is excluded in both source local cases, leaving the same exceptional carrier
and outer action. The marked inversion and covered zero fixation are retained. -/
theorem source_reduction
    (hlocal : Nonempty (NaturalSetup L (T : Subgroup G) V V₁) ∨
      ∃ _a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃,
        D = plus L (T : Subgroup G) V₁ ⊔ zero L) :
    i.B ≤ M ∧ ∃ t : ((T : Subgroup G) ⊓ L : Subgroup G),
      ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
          InvertsTwoCoreQuotient D t.val) ∨
        (SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) ∧
          Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
          InvertsTwoCoreQuotient (plus L (T : Subgroup G) V₁) t.val ∧
          coreAction (zero L) ⟨t.val, L_normalizes_zero L t.property.2⟩ = 1)) ∧
      ExceptionalOuterAlternative.{u,v} H K
        (QuotientGroup.mk' (pCore 2 H) ⟨t.val, i.member.1.2 (mem_sup_right t.property.1)⟩) := by
  rcases hlocal with hord | hcov
  · obtain ⟨a⟩ := hord
    obtain ⟨hB, t, hinv, hb⟩ := exists_exceptionalOuter_ordinary i ρ P f hmodel h12 hseed
      hF918 hB42 A hA hAquad hbound hAfaith initial e a
    exact ⟨hB, t, Or.inl ⟨⟨a.model⟩, hinv⟩, hb⟩
  · obtain ⟨a, hfactor⟩ := hcov
    obtain ⟨hB, t, hinv, hz, hb⟩ := exists_exceptionalOuter_covered i ρ P f hmodel h12 hseed
      hF918 hB42 A hA hAquad hbound hAfaith initial e a hfactor
    exact ⟨hB, t, Or.inr ⟨tripleCover_of_hex_mark a.cover, ⟨a.cover⟩, hinv, hz⟩, hb⟩

end Endpoint
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SourceAssembly
end
