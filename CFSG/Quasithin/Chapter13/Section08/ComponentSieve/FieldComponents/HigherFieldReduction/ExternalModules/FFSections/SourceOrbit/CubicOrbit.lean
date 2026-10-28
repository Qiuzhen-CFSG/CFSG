module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.Quotients
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.Orbit
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.CubicOrbit.GroupGeneration
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Structure.ModelTypes
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Fitting
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The selected constituent's cubic orbit and central coordinates

The literal selected constituent is retained throughout. Cubic norm zero,
normality and generation by K*, X* and P give its two-conjugate orbit.
The inclusion I → W induces I/C_I(K*) → W/C_W(K*). One of the two canonical
coordinate projections is nonzero; irreducibility and the two-summand
dimension bound make it a K*-equivalence with the canonical multiplicity
space. Composing with the section tensor map gives tensor coordinates using
the selected central quotient itself.

The source group generation is derived here from H = KL₁T, L₁ = [L₁,T],
two-perfectness and the earlier small Fitting bound, conditional on abelian
Out(K*). Establishing this last fact for the actual three ExternalCarrier
models remains a prerequisite. The source theorem below is explicitly
conditional on it and is not the completed 13.8.20 source assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20(a), printed pp.954–955; A.1.40–42, pp.31–32; F.9.18(4), pp.325–326.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor Theory.GroupTheory
open scoped IsMulCommutative TensorProduct
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

universe u
variable {G : Type u} [Group G] [Finite G]
    (H K X L₁ T V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [(Source.starImage H K).Normal]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (P : Sylow 2 (Source.Hstar H)) (s : S₃ →* Source.Hstar H)
    (I : Submodule (ZMod 2) (SeedAction.Space H V₃ V₁))

/-- Actual source inputs and exact earlier conclusions. This record contains
neither the requested orbit identity nor a multiplicity equivalence. The
selected FF premise is supplied independently by Selection.ff_of_fourConclusion. -/
structure SourceCubicInputs (𝒦 : GroupClass.{u}) : Prop where
  conjugation : SeedAction.IsConjugation H V₃ V₁ ρ
  faithful : Function.Injective ρ
  generation : H = K ⊔ (L₁ ⊔ T)
  sylow_image : (P : Subgroup (Source.Hstar H)) = Source.starImage H T
  sqtk : IsSQTK 𝒦 H
  component : (K.subgroupOf H).IsCComponent
  component_normal : (K.subgroupOf H).Normal
  quasisimple : IsQuasisimple (Source.starImage H K)
  centerless : center (Source.starImage H K) = ⊥
  component_rank : primeRank 3 K ≤ 1
  model : Structure.ExternalCarrier (Source.starImage H K)
  solvable : Group.IsSolvable (L₁ ⊔ T : Subgroup G)
  one_twoPerfect : IsPPerfect 2 L₁
  one_commutator : ⁅L₁,T⁆ = L₁
  fitting : Components.Fitting.twoFittingResidual H = ⊥ ∨
    Components.Fitting.twoFittingResidual H = X
  cubic_card : Nat.card (Source.starImage H X) = 3
  cubic_normal : (Source.starImage H X).Normal
  embedding : Function.Injective s
  commuting : ∀ (k : Source.starImage H K) g, Commute (k : Source.Hstar H) (s g)
  mark : (alternatingGroup (Fin 3)).map s = Source.starImage H X
  cubic_generation : subspaceCommutator ρ ⊤ (Source.starImage H X) = ⊤
  selected : IsIrrPlusWith ρ (Source.starImage H K) P I
  invariant : (P : Subgroup (Source.Hstar H)) ≤ subspaceStabilizer ρ I
  ff : IsFFModule (imageRepresentation
    (constituentAction ρ (Source.starImage H K) P I selected.invariant invariant))

variable {𝒦 : GroupClass.{u}}
    (d : SourceCubicInputs H K X L₁ T V₃ V₁ ρ P s I 𝒦)

include d in
/-- Transport the full source supplement calculation through O₂(H), then
remove its centralizer coordinate using the small Fitting subgroup. -/
theorem source_actor_generation_of_outer_abelian
    [IsMulCommutative (MulAut.Outer (Source.starImage H K))] :
    Source.starImage H K ⊔ (Source.starImage H X ⊔ (P : Subgroup (Source.Hstar H))) = ⊤ := by
  have hKH : K ≤ H := by rw [d.generation]; exact le_sup_left
  have hDH : L₁ ≤ H := by rw [d.generation]; exact le_sup_left.trans le_sup_right
  have hTH : T ≤ H := by rw [d.generation]; exact le_sup_right.trans le_sup_right
  have hDPH : L₁ ⊔ T ≤ H := sup_le hDH hTH
  let q := QuotientGroup.mk' (pCore 2 H)
  have hsup (A B : Subgroup G) (hA : A ≤ H) (hB : B ≤ H) :
      Source.starImage H (A ⊔ B) = Source.starImage H A ⊔ Source.starImage H B := by
    unfold Source.starImage
    rw [subgroupOf_sup hA hB, Subgroup.map_sup]
  have hsol : Group.IsSolvable (Source.starImage H (L₁ ⊔ T)) := by
    let _ := d.solvable
    let _ : Group.IsSolvable ((L₁ ⊔ T).subgroupOf H) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe hDPH).toMonoidHom)
        (subgroupOfEquivOfLe hDPH).injective
    exact Group.isSolvable_of_surjective
      (q.subgroupMap_surjective ((L₁ ⊔ T).subgroupOf H))
  rw [hsup L₁ T hDH hTH, ← d.sylow_image] at hsol
  let _ := hsol
  have hDperfect : IsPPerfect 2 (Source.starImage H L₁) := by
    have hD := d.one_twoPerfect.of_surjective
      (subgroupOfEquivOfLe hDH).symm.toMonoidHom
      (subgroupOfEquivOfLe hDH).symm.surjective
    exact hD.of_surjective _ (q.subgroupMap_surjective (L₁.subgroupOf H))
  have hcomm : ⁅L₁.subgroupOf H,T.subgroupOf H⁆ = L₁.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hDH,
      map_subgroupOf_eq_of_le hTH, d.one_commutator]
  have hcommStar : ⁅Source.starImage H L₁,(P : Subgroup (Source.Hstar H))⁆ =
      Source.starImage H L₁ := by
    rw [d.sylow_image]
    change ⁅(L₁.subgroupOf H).map q,(T.subgroupOf H).map q⁆ =
      (L₁.subgroupOf H).map q
    rw [← map_commutator, hcomm]
  have hfit : fittingSubgroup (Source.Hstar H) ≤ Source.starImage H X := by
    rw [← Components.Fitting.twoFittingResidual_star H]
    rcases d.fitting with hf | hf
    · simp [hf, Source.starImage]
    · rw [hf]
  have hgen : Source.starImage H K ⊔
      (Source.starImage H L₁ ⊔ (P : Subgroup (Source.Hstar H))) = ⊤ := by
    rw [d.sylow_image, ← hsup L₁ T hDH hTH, ← hsup K (L₁ ⊔ T) hKH hDPH,
      ← d.generation]
    simp [Source.starImage, map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact (component_cubic_generation_of_outer_abelian
    (Source.starImage H K) (Source.starImage H L₁) (Source.starImage H X) P
    d.centerless hDperfect hcommStar hfit d.cubic_card hgen).2

include d in
/-- The selected source constituent has its literal two-conjugate orbit and
the central quotient has the proved multiplicity coordinates. The outer
automorphism premise remains to be discharged for the actual source carrier. -/
theorem source_selected_cubic_orbit_of_outer_abelian
    [IsMulCommutative (MulAut.Outer (Source.starImage H K))] :
    (s cubic)⁻¹ ∈ Source.starImage H X ∧ (s cubic)⁻¹ ≠ 1 ∧
      rightConjugate ρ I (s cubic)⁻¹ ≠ I ∧
      I ≤ orbitSpan ρ ⊤ I ∧
      rightConjugate ρ I (s cubic)⁻¹ ≤ orbitSpan ρ ⊤ I ∧
      orbitSpan ρ ⊤ I = I ⊔ rightConjugate ρ I (s cubic)⁻¹ ∧
      Disjoint (I.map (fixedSpace ρ (Source.starImage H K)).mkQ)
        ((rightConjugate ρ I (s cubic)⁻¹).map (fixedSpace ρ (Source.starImage H K)).mkQ) ∧
      Nonempty ((centralQuotientRepresentation ρ (Source.starImage H K) I
          d.selected.isIrrPlus.choose).Equiv
        (sectionMultiplicityAction ρ (Source.starImage H K).subtype s d.commuting
          (selectedOrbitLower ρ (Source.starImage H K)) (selectedOrbitUpper ρ I))) := by
  have hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤ := by
    rw [d.mark]; exact d.cubic_generation
  have hactor := source_actor_generation_of_outer_abelian H K X L₁ T V₃ V₁ ρ P s I d
  rw [← d.mark] at hactor
  have hx : ((alternatingGroup (Fin 3)).map s).Normal := by
    rw [d.mark]; exact d.cubic_normal
  obtain ⟨ht,htne,hmoved,hIW,htW,horbit,hdis⟩ :=
    selected_cubic_orbit_of_generation ρ (Source.starImage H K) s d.commuting
      P I d.selected.isIrrPlus d.invariant hx hactor d.embedding hgen
  rw [d.mark] at ht
  exact ⟨ht,htne,hmoved,hIW,htW,horbit,hdis,
    ⟨selectedMultiplicityEquiv ρ (Source.starImage H K) s d.commuting
      I d.selected.isIrrPlus (s cubic)⁻¹ horbit hgen⟩⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

end
