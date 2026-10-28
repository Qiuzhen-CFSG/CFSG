module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.SourceOrbit
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Conclusions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.ClassifiedGroups
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.MarkedModels

/-!
# The marked FF factors on the source section

The full source classification is applied to the faithful offender actor,
not to the whole H-action. Once its two classified factors contain the
specified component images, the fixed-space and action-image comparisons
return disjoint canonical commutator spaces and cross-factor fixation on
the original section. The moving element acts by its actual linear operator.

The source actor comparison proves faithfulness on the maximal quotient and
containment of the entire original component orbit in the offender actor.
The complete classification selects two separate factors, and intrinsic
recognition identifies their marked commutator actions as natural modules
of the original field degree or orthogonal A₅ modules. Addition gives the
intertwining product equivalence. Restriction to K₀* supplies the canonical
subrepresentations needed by the projected-seed argument.

`source_section_marked_factors` proves this conditional case-(a) deduction
on the literal maximal source quotient. Its inputs retain the full universal
B.5 classification and the genuine FF-section condition from F.9.18. It
constructs the marked group product and both exchanges under the actual t.
Final specialization, the F.9.18 deduction and the projected subgroup-image
equality remain with their assembly owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.6(3),
printed p.105, and 13.8.16(1), p.952 (PDF p.969).
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- A normal component orbit removes the offender actor's fixed space on the
irreducible H-section as soon as that actor contains its actual image. -/
theorem image_offender_invariants_eq_bot [ρ.IsIrreducible]
    (K₀ : Subgroup D) [K₀.Normal]
    (hfull : subspaceCommutator ρ ⊤ K₀ = ⊤)
    (hK : actionSubgroup ρ K₀ ≤ offenderActor (imageRepresentation ρ)) :
    (offenderRepresentation (imageRepresentation ρ)).invariants = ⊥ := by
  apply le_bot_iff.mp
  rw [← fixedSpace_eq_bot_of_irreducible ρ K₀ hfull]
  intro v hv k
  exact hv ⟨actionHom ρ k, hK (mem_map_of_mem _ k.property)⟩

/-- Pull the classified cross-factor actions all the way back through the
offender inclusion and the actual action homomorphism. -/
theorem marked_cross_of_classified_factors
    (hfix : (offenderRepresentation (imageRepresentation ρ)).invariants = ⊥)
    (c : SourceTwoFactorCase (offenderRepresentation (imageRepresentation ρ)))
    (A B : Subgroup D)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ))
    (hB : actionSubgroup ρ B ≤ offenderActor (imageRepresentation ρ))
    (ha : (actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ)) ≤ c.first)
    (hb : (actionSubgroup ρ B).subgroupOf (offenderActor (imageRepresentation ρ)) ≤ c.second) :
    subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A ∧
      subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B ∧
      Disjoint (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B) := by
  have hc := classified_marked_cross_fixed _ hfix c _ _ ha hb
  have hd := classified_marked_disjoint _ hfix c _ _ ha hb
  rw [actionImage_marked_commutator ρ B hB, actionImage_marked_commutator ρ A hA,
    actionImage_marked_fixedSpace ρ A hA, actionImage_marked_fixedSpace ρ B hB] at hc
  rw [actionImage_marked_commutator ρ B hB, actionImage_marked_commutator ρ A hA] at hd
  exact ⟨hc.1, hc.2, hd⟩

/-- On the component-orbit actor, the canonical spaces form an actual direct
sum. These are precisely the cross-factor premises of the seed obstruction. -/
theorem marked_direct_sum_of_classified_factors
    (hfix : (offenderRepresentation (imageRepresentation ρ)).invariants = ⊥)
    (c : SourceTwoFactorCase (offenderRepresentation (imageRepresentation ρ)))
    (A B : Subgroup D) [A.Normal] [B.Normal]
    (hAB : A ⊔ B = ⊤) (hfull : subspaceCommutator ρ ⊤ ⊤ = ⊤)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ))
    (hB : actionSubgroup ρ B ≤ offenderActor (imageRepresentation ρ))
    (ha : (actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ)) ≤ c.first)
    (hb : (actionSubgroup ρ B).subgroupOf (offenderActor (imageRepresentation ρ)) ≤ c.second) :
    IsCompl (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B) ∧
      subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A ∧
      subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B := by
  obtain ⟨h₁, h₂, hd⟩ := marked_cross_of_classified_factors ρ hfix c A B hA hB ha hb
  exact ⟨⟨hd, codisjoint_iff.mpr (factor_spaces_sum ρ A B hAB hfull)⟩, h₁, h₂⟩

/-- The direct sum in the original overgroup, where the moving components
need not be individually normal. The product map retains both inclusions. -/
theorem marked_product_direct_sum_of_classified_factors
    (hfix : (offenderRepresentation (imageRepresentation ρ)).invariants = ⊥)
    (c : SourceTwoFactorCase (offenderRepresentation (imageRepresentation ρ)))
    (A B N : Subgroup D) (e : A × B ≃* N)
    (he : ∀ a b, (e (a, b) : D) = (a : D) * b)
    (hfull : subspaceCommutator ρ ⊤ N = ⊤)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ))
    (hB : actionSubgroup ρ B ≤ offenderActor (imageRepresentation ρ))
    (ha : (actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ)) ≤ c.first)
    (hb : (actionSubgroup ρ B).subgroupOf (offenderActor (imageRepresentation ρ)) ≤ c.second) :
    IsCompl (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B) ∧
      subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A ∧
      subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B := by
  obtain ⟨h₁, h₂, hd⟩ := marked_cross_of_classified_factors ρ hfix c A B hA hB ha hb
  exact ⟨⟨hd, codisjoint_iff.mpr (factor_spaces_sum_of_product ρ A B N e he hfull)⟩, h₁, h₂⟩

/-- Transport a recognized model back to the original component, retaining
the field parameter and the literal canonical commutator space. -/
theorem factorModule_of_offender_actor (hfaith : Function.Injective ρ)
    (A : Subgroup D) (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ))
    {n : ℕ} (h : FactorModule
      (factorRepresentation (offenderRepresentation (imageRepresentation ρ))
        ((actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ)))) n) :
    FactorModule (factorRepresentation ρ A) n :=
  h.transport (markedFactorActionEquiv ρ hfaith A hA)

/-- The exchange of canonical spaces is induced by the original moving
element, with no freely chosen linear isomorphism. -/
theorem moving_operator_exchanges (A B : Subgroup D) (t : D)
    (ht : B.map (MulAut.conj t).toMonoidHom = A) :
    (subspaceCommutator ρ ⊤ B).map (operator ρ t).toLinearMap =
      subspaceCommutator ρ ⊤ A := by
  rw [moved_map_automorphism ρ (MulAut.conj t) (operator ρ t) (by
    intro g v
    change ρ t (ρ g v) = ρ (t * g * t⁻¹) (ρ t v)
    simp only [map_mul, Module.End.mul_apply, inv_self_apply]), ht]

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open ComponentSieve.AlternatingAndLinear.FourStructure
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁))
    (hρ : ChiefFactors.IsSourceAction H V₃ V₁ ρ)

include hρ

/-- Apply the complete universal B.5.6 contract to the literal maximal source
quotient. The genuine FF condition from F.9.18 is explicit. All B.5.3
hypotheses, including the SQTK cover and offender generation, are proved.
This does not yet select its two-factor alternative. -/
theorem source_section_classification {𝒦 : GroupClass.{u}}
    (classification : CompleteClassificationInput.{u,u} 𝒦) (hSQTK : IsSQTK 𝒦 H)
    (K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T))
    (hL : L₁ ≤ conjugateSpanBy K T)
    (hLN : L₁ ≤ normalizer (V₃ : Set G)) (hline : V₁ ≤ V₃)
    (hseed : V₃ ≤ ⁅L₁, V₃⁆ ⊔ V₁)
    (W : Subrepresentation ρ)
    (hW : ¬ subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ W.toSubmodule)
    (hmax : ∀ Y : Subrepresentation ρ, W ≤ Y →
      ¬ subspaceCommutator ρ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ Y.toSubmodule → Y = W)
    (hff : IsFFModule (imageRepresentation W.quotientRepresentation)) :
    FFHypothesis 𝒦 (offenderRepresentation (imageRepresentation W.quotientRepresentation)) ∧
      SourceAlternative (offenderRepresentation (imageRepresentation W.quotientRepresentation)) ∧
      IsFFModule (offenderRepresentation (imageRepresentation W.quotientRepresentation)) := by
  have hfull := source_moved_eq_top H V₃ V₁ ρ hρ K L₁ T hH hL hLN hline hseed
  let : W.quotientRepresentation.IsIrreducible :=
    maximal_component_section_irreducible ρ W _ hfull hW hmax
  let : Module.Finite (ZMod 2) (ChiefFactors.SourceSpace H V₃ V₁) :=
    Module.Finite.of_finite
  have hyp := irreducible_offender_hypothesis W.quotientRepresentation
    (QuotientGroup.mk' (pCore 2 H)) (QuotientGroup.mk'_surjective _) hSQTK
  exact ⟨hyp, classification.general _ _ _ hyp,
    offender_isFFModule _ hff⟩

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison
open FFAlternatives
universe u
variable {D V : Type u} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The case-(a) conclusion on the original marked commutator spaces. -/
structure MarkedFactors (A B : Subgroup D) (n : ℕ) : Prop where
  direct : IsCompl (subspaceCommutator ρ ⊤ A) (subspaceCommutator ρ ⊤ B)
  first : FactorModule (factorRepresentation ρ A) n
  second : FactorModule (factorRepresentation ρ B) n
  first_fixed : subspaceCommutator ρ ⊤ B ≤ fixedSpace ρ A
  second_fixed : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B

/-- Assemble the full classification and intrinsic recognition on the
faithful offender actor, preserving the original marked subgroups. -/
theorem markedFactors_of_classification [Finite D] {𝒦 : GroupClass.{u}}
    (hyp : FFHypothesis 𝒦 (offenderRepresentation (imageRepresentation ρ)))
    (hc : SourceAlternative (offenderRepresentation (imageRepresentation ρ)))
    (hfaith : Function.Injective ρ)
    (hfix : (offenderRepresentation (imageRepresentation ρ)).invariants = ⊥)
    (A B N : Subgroup D) (hcompA : IsComponent D A) (hcompB : IsComponent D B)
    (hne : A ≠ B) (hjoin : A ⊔ B = N)
    (e : A × B ≃* N) (he : ∀ a b, (e (a, b) : D) = (a : D) * b)
    (hfull : subspaceCommutator ρ ⊤ N = ⊤)
    (hN : actionSubgroup ρ N ≤ offenderActor (imageRepresentation ρ))
    {n : ℕ} (hn : 2 ≤ n) (hmA : ClassicalGroup.IsPSL A 2 (2 ^ n))
    (hmB : ClassicalGroup.IsPSL B 2 (2 ^ n)) : MarkedFactors ρ A B n := by
  let J := offenderActor (imageRepresentation ρ)
  let σ := offenderRepresentation (imageRepresentation ρ)
  have hA : actionSubgroup ρ A ≤ J := (Subgroup.map_mono (hjoin ▸ le_sup_left)).trans hN
  have hB : actionSubgroup ρ B ≤ J := (Subgroup.map_mono (hjoin ▸ le_sup_right)).trans hN
  let A' := (actionSubgroup ρ A).subgroupOf J
  let B' := (actionSubgroup ρ B).subgroupOf J
  have hA' := marked_isComponent ρ hfaith A hcompA hA
  have hB' := marked_isComponent ρ hfaith B hcompB hB
  have hinj : Function.Injective (actionHom ρ) := by
    intro a b h
    exact hfaith (congrArg (imageRepresentation ρ) h)
  have hne' : A' ≠ B' := by
    intro hh
    have hh' := congrArg (Subgroup.map J.subtype) hh
    rw [map_subgroupOf_eq_of_le hA, map_subgroupOf_eq_of_le hB] at hh'
    exact hne (Subgroup.map_injective hinj hh')
  have hjoin' : A' ⊔ B' = (actionSubgroup ρ N).subgroupOf J := by
    rw [← hjoin]
    dsimp only [A', B', actionSubgroup]
    rw [Subgroup.map_sup]
    exact (subgroupOf_sup hA hB).symm
  have hfull' : subspaceCommutator σ ⊤ (A' ⊔ B') = ⊤ := by
    rw [hjoin', actionImage_marked_commutator ρ N hN, hfull]
  obtain ⟨c, ha, hb⟩ := ClassifiedGroups.exists_marked_twoFactorCase σ hyp hc hA' hB' hne' hfull'
  have hmA' := hmA.of_mulEquiv (markedActorEquiv ρ hfaith A hA).symm
  have hmB' := hmB.of_mulEquiv (markedActorEquiv ρ hfaith B hB).symm
  have recA := MarkedModels.sourceFactorCase_recognition σ hfix c.firstCase hA' ha hn hmA'
  have recB := MarkedModels.sourceFactorCase_recognition σ hfix c.secondCase hB' hb hn hmB'
  obtain ⟨hd, hx, hy⟩ := marked_product_direct_sum_of_classified_factors ρ hfix c
    A B N e he hfull hA hB ha hb
  exact ⟨hd, factorModule_of_offender_actor ρ hfaith A hA recA.2,
    factorModule_of_offender_actor ρ hfaith B hB recB.2, hx, hy⟩

/-- Addition is an intertwining equivalence for the marked product actor. -/
noncomputable def MarkedFactors.productActionEquiv {A B N : Subgroup D} {n : ℕ}
    (h : MarkedFactors ρ A B n) (e : A × B ≃* N)
    (he : ∀ a b, (e (a, b) : D) = (a : D) * b) :
    ActionEquiv
      (Representation.prod ((factorRepresentation ρ A).comp (MonoidHom.fst A B))
        ((factorRepresentation ρ B).comp (MonoidHom.snd A B)))
      (ρ.comp N.subtype) where
  groupEquiv := e
  linearEquiv := factorSumEquiv ρ A B h.direct
  intertwines g v := factorSumEquiv_intertwines ρ A B N e he h.direct
    h.first_fixed h.second_fixed g.1 g.2 v.1 v.2

/-- A factor moved space is invariant under the component product: the other
factor fixes it. No ambient normality of the individual factors is required. -/
def factorSpaceOnProduct (A B N : Subgroup D) (hjoin : A ⊔ B = N)
    (hcross : subspaceCommutator ρ ⊤ A ≤ fixedSpace ρ B) :
    Subrepresentation (ρ.comp N.subtype) :=
  invariantSubspace ρ N (subspaceCommutator ρ ⊤ A) (by
    rw [← hjoin]
    refine sup_le (subspaceCommutator_invariant ρ ⊤ A) ?_
    apply le_subspaceStabilizer
    intro b hb v hv
    have hf : ρ b v = v := hcross hv ⟨b, hb⟩
    rwa [hf])

/-- Restriction to an overgroup preserves the literal marked commutator. -/
theorem product_restriction_commutator (N A : Subgroup D) (hAN : A ≤ N)
    (X : Submodule (ZMod 2) V) :
    subspaceCommutator (ρ.comp N.subtype) X (A.subgroupOf N) =
      subspaceCommutator ρ X A := by
  unfold subspaceCommutator
  congr 1
  ext v
  constructor
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨a, ha, x, hx, rfl⟩
  · rintro ⟨a, ha, x, hx, rfl⟩
    exact ⟨⟨a, hAN ha⟩, ha, x, hx, rfl⟩

/-- All factor-space inputs of `not_sum_of_projected_markings` on K₀*.
The seed and the equality of projected marked subgroup images are external.
The returned subrepresentations are exactly the original commutator spaces. -/
theorem MarkedFactors.seedProjectionData {A B N : Subgroup D} {n : ℕ}
    (h : MarkedFactors ρ A B n) (hjoin : A ⊔ B = N)
    (t : D) (ht : B.map (MulAut.conj t).toMonoidHom = A) :
    ∃ U₁ U₂ : Subrepresentation (ρ.comp N.subtype),
      U₁.toSubmodule = subspaceCommutator ρ ⊤ A ∧
      U₂.toSubmodule = subspaceCommutator ρ ⊤ B ∧
      IsCompl U₁.toSubmodule U₂.toSubmodule ∧
      U₁.toSubmodule ⊔ U₂.toSubmodule = ⊤ ∧
      U₂.toSubmodule ≤ fixedSpace (ρ.comp N.subtype) (A.subgroupOf N) ∧
      U₁.toSubmodule ≤ fixedSpace (ρ.comp N.subtype) (B.subgroupOf N) ∧
      U₂.toSubmodule.map (operator ρ t).toLinearMap = U₁.toSubmodule := by
  have hjoin' : B ⊔ A = N := (sup_comm _ _).trans hjoin
  refine ⟨factorSpaceOnProduct ρ A B N hjoin h.second_fixed,
    factorSpaceOnProduct ρ B A N hjoin' h.first_fixed,
    rfl, rfl, h.direct, codisjoint_iff.mp h.direct.codisjoint, ?_, ?_, ?_⟩
  · intro v hv a
    exact h.first_fixed hv ⟨a, a.property⟩
  · intro v hv b
    exact h.second_fixed hv ⟨b, b.property⟩
  · exact moving_operator_exchanges ρ A B t ht

open ComponentSieve.AlternatingAndLinear.FourStructure
variable {G : Type u} [Group G] [Finite G]
    (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (σ : Representation (ZMod 2) (Source.Hstar H) (ChiefFactors.SourceSpace H V₃ V₁))
    (hσ : ChiefFactors.IsSourceAction H V₃ V₁ σ)

include hσ

/-- The conditional source case-(a) deduction on the literal maximal quotient.
The full universal classification and the FF-section condition remain inputs.
The product and exchange operators retain both actual component inclusions. -/
theorem source_section_marked_factors {𝒦 : GroupClass.{u}}
    (classification : CompleteClassificationInput.{u,u} 𝒦) (hSQTK : IsSQTK 𝒦 H)
    (K L₁ T : Subgroup G)
    (hH : H = conjugateSpanBy K T ⊔ (L₁ ⊔ T)) (hL : L₁ ≤ conjugateSpanBy K T)
    (hK : (K.subgroupOf H).IsCComponent)
    (hq : IsQuasisimple (Source.starImage H K)) (hT : IsPGroup 2 T)
    (hi : (normalizer (K.subgroupOf H : Set H)).index = 2)
    (t : H) (ht : (t : G) ∈ T) (hm : (t : G) ∉ normalizer (K : Set G))
    {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n))
    (hLN : L₁ ≤ normalizer (V₃ : Set G)) (hline : V₁ ≤ V₃)
    (hseed : V₃ ≤ ⁅L₁, V₃⁆ ⊔ V₁)
    (W : Subrepresentation σ)
    (hW : ¬ subspaceCommutator σ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ W.toSubmodule)
    (hmax : ∀ Y : Subrepresentation σ, W ≤ Y →
      ¬ subspaceCommutator σ ⊤ (Source.starImage H (conjugateSpanBy K T)) ≤ Y.toSubmodule → Y = W)
    (hff : IsFFModule (imageRepresentation W.quotientRepresentation)) :
    ∃ e : Source.starImage H K × Source.starImage H (K.conjBy (t : G)) ≃*
        Source.starImage H (conjugateSpanBy K T),
      (∀ a b, (e (a, b) : Source.Hstar H) = (a : Source.Hstar H) * b) ∧
      MarkedFactors W.quotientRepresentation
        (Source.starImage H K) (Source.starImage H (K.conjBy (t : G))) n ∧
      (subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H (K.conjBy (t : G)))).map
        (operator W.quotientRepresentation (QuotientGroup.mk' (pCore 2 H) t)).toLinearMap =
          subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H K) ∧
      (subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H K)).map
        (operator W.quotientRepresentation (QuotientGroup.mk' (pCore 2 H) t)).toLinearMap =
          subspaceCommutator W.quotientRepresentation ⊤ (Source.starImage H (K.conjBy (t : G))) := by
  have hKH : K ≤ H := (le_conjugateSpanBy K T).trans (by rw [hH]; exact le_sup_left)
  have hTH : T ≤ H := by rw [hH]; exact le_sup_right.trans le_sup_right
  have hspan := orbit_eq_two_conjugates H K T hKH hTH hi ht hm
  obtain ⟨hJH, hJ⟩ := conjugate_isCComponent H K hKH hK t.property
  let c := starConjugateEquiv H K hKH t.property
  let := hq
  have hqJ : IsQuasisimple (Source.starImage H (K.conjBy (t : G))) :=
    IsQuasisimple.of_mulEquiv c
  have hne : K ≠ K.conjBy (t : G) := fun hh => hm (mem_normalizer_iff_map_conj_eq.mpr hh.symm)
  have hneStar := starImages_ne H K (K.conjBy (t : G)) hKH hJH hK hJ hne
  have hjoin : Source.starImage H K ⊔ Source.starImage H (K.conjBy (t : G)) =
      Source.starImage H (conjugateSpanBy K T) := by
    rw [hspan, starImage_sup H K _ hKH hJH]
  obtain ⟨e₀, he₀⟩ := exists_star_product_coordinates H K (K.conjBy (t : G))
    hKH hJH hK hJ hne hq hqJ hmodel
  let e := e₀.trans (MulEquiv.subgroupCongr (congrArg (Source.starImage H) hspan.symm))
  have he : ∀ a b, (e (a, b) : Source.Hstar H) = (a : Source.Hstar H) * b := he₀
  let ee := (MulEquiv.prodCongr (MulEquiv.refl _) c).trans e
  obtain ⟨hfaith, hactor⟩ := source_section_actor_comparison H V₃ V₁ σ hσ K L₁ T
    hH hL hK hq hT hmodel ee hLN hline hseed W hW hmax hff
  have hfull := source_moved_eq_top H V₃ V₁ σ hσ K L₁ T hH hL hLN hline hseed
  let : W.quotientRepresentation.IsIrreducible :=
    maximal_component_section_irreducible σ W _ hfull hW hmax
  let := orbit_star_normal H K L₁ T hH hL
  have hqfull := quotient_full_commutator σ W _ hfull
  have hfix := image_offender_invariants_eq_bot W.quotientRepresentation _ hqfull hactor
  obtain ⟨hyp, hc, _⟩ := source_section_classification H V₃ V₁ σ hσ classification hSQTK
    K L₁ T hH hL hLN hline hseed W hW hmax hff
  have hfactors := markedFactors_of_classification W.quotientRepresentation hyp hc hfaith hfix
    _ _ _ (F918Sections.star_isComponent H K hK hq)
    (F918Sections.star_isComponent H _ hJ hqJ) hneStar hjoin e he hqfull hactor hn
    hmodel (hmodel.of_mulEquiv c.symm)
  refine ⟨e, he, hfactors, ?_, ?_⟩
  · apply moving_operator_exchanges
    have ht2 := (normalizer (K.subgroupOf H : Set H)).sq_mem_of_index_two hi t
    rw [← subgroupOf_normalizer_eq hKH] at ht2
    change (t : G) ^ 2 ∈ normalizer (K : Set G) at ht2
    rw [pow_two] at ht2
    have heq : (K.conjBy (t : G)).conjBy (t : G) = K := by
      rw [← conjBy_mul]
      exact mem_normalizer_iff_map_conj_eq.mp ht2
    rw [starImage_conjBy H _ hJH t.property, heq]
  · exact moving_operator_exchanges W.quotientRepresentation _ _ _
      (starImage_conjBy H K hKH t.property)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
