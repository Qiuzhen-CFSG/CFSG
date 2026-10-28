module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.NaturalOrbit
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.LinearThreeLayers

/-!
# The original external odd PSL₃ exclusion

The original faithful FF multiplicity action supplies an actual natural or
dual constituent. Work on its full ambient orbit: the marked Borel has no
fixed vectors there, and the native quotient-layer theorem supplies the
remaining natural tensor layer when required. Borel and component fixed
spaces consequently agree on the original module. Borel centralization of
the source seed and the actual action kernel then give a contradiction.

No invariant cubic-pair or full F.9.18(4) premise remains. The component-central
complement is preserved. Applying this to the original Borel reduction
excludes every external higher-field branch and retains the exceptional
outer carriers, full covers, local cubic and prescribed inverter.

The exceptional outer contradictions, earlier binary/F9 premises and full
13.8.19–21 assembly remain with qt-d-138-fields-source. The original preceding
context retains its source producers and final owner qt-d-1381-source.
Source: Aschbacher–Smith, 13.8.20(a), printed pp.954–955.
-/

set_option backward.isDefEq.respectTransparency false

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open Representation.BinaryOffender.Homogeneous
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}
  [IsElementaryAbelian 2 (Source.UH H V₃)]

/-- Exclude the original external odd PSL₃ branch using its actual natural
constituent, full ambient orbit, marked Borel and source action kernel. -/
theorem source_external_linearThree_false
    [(Source.starImage H K).Normal]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X) (hx : ExternalSourceData H K X)
    (hseed : V₃ = ⁅V₃,X⁆)
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H)
    (hcentral : LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ centralizer (V : Set G))
    {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hm : ClassicalGroup.IsPSL (Source.starImage H K) 3 (2^n)) : False := by
  let Ks := Source.starImage H K
  let Xs := Source.starImage H X
  let : Xs.Normal := hx.2.2.1
  let : (K.subgroupOf H).Normal := c.component.normal
  let : IsQuasisimple Ks :=
    (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
      c.component.component).2
  obtain ⟨F,hF,hfin,hcard,⟨e₀⟩⟩ := hm
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let S := LocalBorel.sourceSylow H K (T : Subgroup G) hT
  let B₀ := LocalBorel.borelStar H K (T : Subgroup G) hT
  obtain ⟨e,hBe⟩ := RankTwo.exists_borel_marking (by omega : 0 < n) hcard e₀ S
  have hB₀ : (B₀.subgroupOf Ks).map e.toMonoidHom = Matrix.PSL3.LinearThree.borel F := by
    rw [show B₀.subgroupOf Ks = normalizer (S : Set Ks) from
      comap_map_eq_self_of_injective Ks.subtype_injective _]
    exact hBe
  let B := LocalBorel.borel H K (T : Subgroup G) hKH hT
  let Bs := (Source.starImage H B).subgroupOf Ks
  have hB := lifted_borel_residual_marking H K hKH B₀ (map_subtype_le _) e _ hB₀
  obtain ⟨s,_,hs,hmark,I,hI,_,_,hnat,_⟩ :=
    source_external_linearThree_constituent c act ha hx hseed hn ho hcard e
  obtain ⟨_,_,_,_,hg,_,_⟩ := source_external_cubic_action act X ha hx hseed
  have hsq := Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.IrreducibleReduction.sqtk_two_quotient
    (source_sqtk c) (pCore 2 H) pCore_isPGroup
  obtain ⟨A,hA,_⟩ := source_quotient_faithful_quadratic_actor c act
  have hfix := RankTwo.NaturalOrbit.fixedSpace_eq_invariants act.representation Ks Xs
    hsq hx.1 (source_external_common_centralizer c X hx) s hs hmark hg hn ho hcard e
    Bs hB I hI hnat A hA.1 hA.2.2
  have hF9 := c.f9 H c.component.local_overgroup
  have hHK := (normal_subgroupOf_iff_le_normalizer hKH).mp c.component.normal
  have hz := hF9.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hk := (OddReduction.source_kernel hF9).symm
  let : IsSimpleGroup (Ks ⧸ center Ks) := IsQuasisimple.simple
  let : Nontrivial Ks := (QuotientGroup.mk'_surjective (center Ks)).nontrivial
  have hne : Ks ≠ ⊥ := by
    intro he
    obtain ⟨k,hk⟩ := exists_ne (1 : Ks)
    exact hk (Subtype.ext (mem_bot.mp (he ▸ k.property)))
  exact SeedAction.contradiction_of_star_fixedSpace H V₃ V₁ K B hKH hF9.plus_le_H
    hHK hz hk hne act.representation act.conjugation
    (seed_commutator_of_borel_centralizes B V V₃ V₁ c.localSetup.seed_le hcentral) hfix.le
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K : Subgroup G}

/-- Every original higher-field component lies in the exceptional outer
branch. All external components are excluded, with the full covers and the
original local cubic, inverter and torus markings retained. -/
theorem source_borel_exceptional_outer
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (hfield : HigherFieldAlternative (K ⧸ pCore 2 K)) :
    letI : (Source.starImage H K).Normal :=
      c.component.normal.map _ (QuotientGroup.mk'_surjective _)
    ∃ (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H),
      LocalBorel.borel H K (T : Subgroup G) hKH hT ≤ M ∧
      ∃ (X : Subgroup G) (t : ((T : Subgroup G) ⊓ L : Subgroup G)),
        ((Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
          (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
            X = plus L T V₁ ∧ coreAction (zero L) ⟨t.val,L_normalizes_zero L t.property.2⟩ = 1)) ∧
        LocalBorel.CentralizingCalculation.InvertsTwoCoreQuotient X t.val ∧ V₃ = ⁅V₃,X⁆ ∧
        ExceptionalOuterAlternative.{u,0} H K
          (QuotientGroup.mk' (pCore 2 H)
            ⟨t.val,c.component.local_overgroup.1.2 (mem_sup_right t.property.1)⟩) := by
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  obtain ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,hcases⟩ :=
    source_borel_odd_linearThree_or_outer c act hfield
  refine ⟨hKH,hT,hBM,X,t,hlocal,hinv,hseed,?_⟩
  rcases hcases with ⟨ha,hcentral,hx,n,hn,ho,hm⟩ | he
  · exact (source_external_linearThree_false c act ha.1 hx hseed hKH hT hcentral hn ho hm).elim
  · exact he
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
