module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.NativeRecognition
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo

/-!
# Native odd PSL₃ cubic FF recognition and quotient layers

The corrected B.4.2 classifier recognizes each faithful irreducible section
under its original component marking. B.1.5 stabilizes the selected constituent;
natural cohomology removes its central kernel. Its odd dimension separates the
cubic conjugate, and the two codimensions exclude strong FF actions. In an FF
action equality makes this pair exactly the component moved space, preserving
an arbitrary component-central complement.

For a proper fully moved invariant submodule, the source ratio-two inequality
therefore makes the quotient FF. The actual quotient and multiplicity maps
lift its natural or dual-natural moved module to the second layer. A realized
first FF orbit gives the complete one-or-two-layer output. Neither a universal
B.4.2 premise nor a universal F.9.18 premise occurs in these results.
OriginalSource.LinearThreeLayers applies them to the original actor, original
Borel and literal U_H/V₁. Construction of the first invariant orbit and the
remaining field-source assembly stay with qt-d-138-fields-source.
Source: Aschbacher–Smith, B.1.5, B.4.2, F.9.18(6), I.1.5–6 and 13.8.20(a),
printed pp.69–70,86,325–326,408,954–955.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native
open LinearTwo.NoStrongMoved CubicFF
universe u v
variable {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F] {n : ℕ}
  {E : Type u} [Group E] [Finite E]
  {U : Type v} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
  (σ : Representation (ZMod 2) E U)
/-- A compatible component and multiplicity map transfers the recognized
constituent to the specified action. Both maps are retained literally. -/
theorem naturalOrDual_and_ratio
    (h : B4Hypotheses KnownSimple.IsKnownSimple σ) (hff : IsFFModule σ)
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n)
    {K M : Type*} [Group K] [AddCommGroup M] [Module (ZMod 2) M]
    (μ : Representation (ZMod 2) K M) (e : K ≃* PSL(3,F))
    (a : generalizedFitting E ≃* K) (b : U ≃ₗ[ZMod 2] M)
    (hb : ∀ (g : generalizedFitting E) v, b (σ g v) = μ (a g) (b v)) :
    IsProjectiveNaturalOrDual ho hF (μ.comp e.symm.toMonoidHom) ∧
      quadraticRatio σ = 1 / 2 := by
  obtain ⟨B,hB,_,⟨c⟩,hq⟩ := NativeRecognition.linearThree_natural σ h hff hn ho hF (a.trans e)
  let d : ActionEquiv μ (linearNatural B 3) := {
    groupEquiv := a.symm.trans c.groupEquiv
    linearEquiv := b.symm.trans c.linearEquiv
    intertwines := by
      intro k v
      change c.linearEquiv (b.symm (μ k v)) =
        linearNatural B 3 (c.groupEquiv (a.symm k)) (c.linearEquiv (b.symm v))
      rw [← c.intertwines]
      congr 1
      apply b.injective
      rw [b.apply_symm_apply]
      change μ k v = b (σ (a.symm k) (b.symm v))
      rw [hb, a.apply_symm_apply, b.apply_symm_apply] }
  exact ⟨MarkingRigidity.actionEquiv_naturalOrDual ho hF hn μ B hB d e, hq⟩

variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V) (K A : Subgroup D) [K.Normal]
local instance (I : Submodule (ZMod 2) V) : Finite (centralQuotient ρ K I) :=
  Finite.of_surjective _ (Submodule.mkQ_surjective _)

/-- Native B.4.2 recognizes the original marking and retains the exact ratio. -/
theorem centralizing_constituent_natural [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hbest : IsBestOffender ρ A)
    (X : Subgroup D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (hKX : K ≤ centralizer (X : Set D)) (hAX : A ≤ centralizer (X : Set D))
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hA : A ≤ subspaceStabilizer ρ I) :
    IsProjectiveNaturalOrDual ho hF
      ((centralQuotientRepresentation ρ K I hI.choose).comp e.symm.toMonoidHom) ∧
      quadraticRatio (constituentAction ρ K A I hI.choose hA) = 1 / 2 := by
  obtain ⟨hb,hff⟩ := centralizing_constituent_b4 ρ K A hS hbest X hx hc hKX hAX ho hF e I hI hA
  have hfit := generated_fitting K X hx hc hKX hbest.1 hAX
  let a : generalizedFitting (K ⊔ A : Subgroup D) ≃* K :=
    (MulEquiv.subgroupCongr hfit).trans (subgroupOfEquivOfLe le_sup_left)
  let σ := constituentAction ρ K A I hI.choose hA
  apply naturalOrDual_and_ratio σ hb hff hn ho hF
    (centralQuotientRepresentation ρ K I hI.choose) e a (LinearEquiv.refl _ _)
  intro g v
  induction v using Submodule.Quotient.induction_on with
  | _ v => rfl

/-- Select a stabilized natural central quotient and retain its exact dimension and codimension bound. -/
private theorem exists_recognized_constituent [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hf : Function.Injective ρ)
    (X : Subgroup D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (hKX : K ≤ centralizer (X : Set D)) (hAX : A ≤ centralizer (X : Set D))
    (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (hA : IsMinimalBestOffender ρ A) (hquad : IsQuadratic ρ A) :
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
      (hAI : A ≤ subspaceStabilizer ρ I),
      IsProjectiveNaturalOrDual ho hF
        ((centralQuotientRepresentation ρ K I hI.choose).comp e.symm.toMonoidHom) ∧
      quadraticRatio (constituentAction ρ K A I hI.choose hAI) = 1 / 2 ∧
      rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
        (A.subgroupOf (K ⊔ A)) ∧
      Module.finrank (ZMod 2) (centralQuotient ρ K I) = 3 * n := by
  have hK : K ≠ ⊥ := by
    intro he
    apply quasisimple_noncentral ρ K hf
    simp [he]
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_faithful ρ hf K hK
  have hAI := minimal_stabilizes ρ K A LinearTwo.NativeSource.irr_invariance hf X hx hc hAX hA I hI
  obtain ⟨hnat,hratio⟩ := centralizing_constituent_natural ρ K A hS hA.1 X hx hc
    hKX hAX hn ho hF e I hI hAI
  refine ⟨I,hI,hAI,hnat,hratio,
    constituent_half_bound ρ K A hA.1 hquad I hI.choose hAI hratio, ?_⟩
  exact naturalOrDual_finrank ho hF _ hnat

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native
open LinearTwo.NoStrongMoved CubicFF
universe u v
variable {D : Type u} [Group D] [Finite D]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) D V) (K : Subgroup D) [K.Normal] [IsQuasisimple K]
  (hS : IsSQTK KnownSimple.IsKnownSimple D) (hf : Function.Injective ρ)
  (X : Subgroup D) [X.Normal] (hx : Nat.card X = 3)
  (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
  (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
  (hmark : (alternatingGroup (Fin 3)).map s = X)
  (hg : subspaceCommutator ρ ⊤ X = ⊤)
  {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
  {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))

omit [Finite D] [X.Normal] in
include hmark in
private theorem centralizes_marked_cubic {A : Subgroup D}
    (hAX : A ≤ centralizer (X : Set D)) : ∀ a ∈ A, Commute a (s cubic) := by
  have hxmem : s cubic ∈ X := by
    rw [← hmark]
    exact mem_map_of_mem s (show cubic ∈ alternatingGroup (Fin 3) from by
      change Equiv.Perm.sign cubic = 1
      decide +kernel)
  intro a ha
  exact (hAX ha (s cubic) hxmem).symm

include hS hf hx hc hs hmark hg hn ho hF e in
/-- The recognized central quotient lifts to an actual odd-dimensional natural
constituent, with its original marking and the numerical half-codimension bound. -/
theorem quadratic_minimal_split_constituent (A : Subgroup D)
    (hA : IsMinimalBestOffender ρ A) (hquad : IsQuadratic ρ A) :
    A ≤ centralizer (X : Set D) ∧
    ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
      (hAI : A ≤ subspaceStabilizer ρ I),
      Disjoint I (fixedSpace ρ K) ∧
      IsProjectiveNaturalOrDual ho hF
        ((invariantSubspace ρ K I hI.choose).toRepresentation.comp e.symm.toMonoidHom) ∧
      Odd (Module.finrank (ZMod 2) I) ∧
      rank A ≤ 2 * fixedCodim (constituentAction ρ K A I hI.choose hAI)
        (A.subgroupOf (K ⊔ A)) := by
  have hAX := quadratic_offender_centralizes ρ K A X hx hf s hs hmark hg
    (quasisimple_noncentral ρ K hf) (hA.1.isOffender ρ) hquad
  obtain ⟨I, hI, hAI, hnat, _, hnum, _⟩ :=
    exists_recognized_constituent ρ K A hS hf X hx hc
      (marked_component_centralizes_cubic K X s hs hmark) hAX hn ho hF e hA hquad
  have hd := CentralSplitting.disjoint_fixedSpace hn ho hF ρ K e I hI hnat
  have hi := CentralSplitting.naturalOrDual hn ho hF ρ K e I hI hnat
  refine ⟨hAX, I, hI, hAI, hd, hi, ?_, hnum⟩
  have hdim : Module.finrank (ZMod 2) I = 3 * n := naturalOrDual_finrank ho hF _ hi
  rw [hdim]
  exact (by decide : Odd 3).mul ho

include hS hf hx hc hs hmark hg hn ho hF e in
/-- A quadratic minimal best offender pays its full rank on the cubic pair. -/
theorem quadratic_minimal_rank_bound (A : Subgroup D)
    (hA : IsMinimalBestOffender ρ A) (hquad : IsQuadratic ρ A) :
    rank A ≤ fixedCodim ρ A := by
  obtain ⟨hAX, I, hI, hAI, hd, _, hi, hnum⟩ :=
    quadratic_minimal_split_constituent ρ K hS hf X hx hc s hs hmark hg hn ho hF e A hA hquad
  exact PairSaturation.rank_le_fixedCodim ρ K A s hs
    (ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg))
    (centralizes_marked_cubic X s hmark hAX) I hI hAI hd hi hnum

include hS hf hx hc hs hmark hg hn ho hF e in
/-- A faithful binary cubic action with the marked odd PSL₃ component is never
strong FF. Quadratic replacement reduces to the doubled constituent bound. -/
theorem no_strong : ¬ IsStrongFFModule ρ := by
  rintro ⟨B, hB⟩
  obtain ⟨A, _, hA, hquad, hstrong⟩ := hB.exists_quadratic_minimalBestOffender ρ
  exact (not_lt_of_ge (quadratic_minimal_rank_bound ρ K hS hf X hx hc
    s hs hmark hg hn ho hF e A hA hquad)) hstrong.2

include hS hf hx hc hs hmark hg hn ho hF e in
/-- For an FF action the full K-moved space is a natural cubic tensor module:
the canonical inverter-fixed multiplicity of the literal W/0 section is natural
or binary dual-natural under the supplied component marking. -/
theorem moved_natural_of_ff (hff : IsFFModule ρ)
    (W : Subrepresentation ρ) (hW : W.toSubmodule = subspaceCommutator ρ ⊤ K) :
    IsProjectiveNaturalOrDual ho hF
      ((sectionMultiplicityAction ρ K.subtype s hs ⊥ W).comp e.symm.toMonoidHom) := by
  obtain ⟨B, hB⟩ := hff
  obtain ⟨A, _, hA, hquad, _⟩ := hB.exists_quadratic_minimalBestOffender ρ
  obtain ⟨hAX, I, hI, hAI, hd, hi, hodd, hnum⟩ :=
    quadratic_minimal_split_constituent ρ K hS hf X hx hc s hs hmark hg hn ho hF e A hA hquad
  obtain ⟨a, ha⟩ := PairSaturation.offender_multiplicity_coordinates ρ K A s hs
    (ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg))
    (centralizes_marked_cubic X s hmark hAX)
    (component_commutator_of_centralizes_cubic K X hx hc hA.1.1 hAX)
    I hI hAI hd hodd hnum (hA.1.isOffender ρ) W hW
  rcases hi with ⟨f, hf⟩ | ⟨f, hf⟩
  · exact Or.inl ⟨a.trans f, fun g v => by
      change f (a (sectionMultiplicityAction ρ K.subtype s hs ⊥ W (e.symm g) v)) = _
      rw [ha]
      exact hf g (a v)⟩
  · exact Or.inr ⟨a.trans f, fun g v => by
      change f (a (sectionMultiplicityAction ρ K.subtype s hs ⊥ W (e.symm g) v)) = _
      rw [ha]
      exact hf g (a v)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native
open LinearTwo.NoStrongMoved QuotientLayers
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K X : Subgroup D)
    [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))

include hS hx hc hs hmark hg hn ho hF e in
/-- Every proper nonzero fully moved submodule has a natural second layer up to
the full moved module. Faithfulness and exclusion of both strong-FF branches
are proved from the cubic structure and the original ratio-two actor. -/
theorem second_layer (W : Subrepresentation ρ)
    (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule)
    (hne : W.toSubmodule ≠ subspaceCommutator ρ ⊤ K)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    ∃ M : Subrepresentation ρ, W ≤ M ∧
      M.toSubmodule = subspaceCommutator ρ ⊤ K ∧
      IsProjectiveNaturalOrDual ho hF
        ((sectionMultiplicityAction ρ K.subtype s hs W M).comp e.symm.toMonoidHom) := by
  have hxmem : s cubic ∈ X := by
    rw [← hmark]
    exact mem_map_of_mem s (show cubic ∈ alternatingGroup (Fin 3) from by
      change Equiv.Perm.sign cubic = 1
      decide +kernel)
  have hfree := ambient_fixedFree_of_commutator ρ s (by rw [hmark]; exact hg)
  have hwfree := fixedFree_of_injective (ρ.comp s) (W.toRepresentation.comp s)
    W.toSubmodule.subtype W.toSubmodule.subtype_injective (fun _ => rfl) hfree
  have hwfull := full_of_fixedFree X W.toRepresentation (s cubic) hxmem hwfree
  have hfW := faithful_of_cubic K X hx hc W.toRepresentation
    (subrepresentation_action_nontrivial ρ W K hW hfull) (s cubic) hxmem hwfree
  have hqfree := fixedFree_of_surjective (ρ.comp s) (W.quotientRepresentation.comp s)
    W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective (fun _ => rfl) hfree
  let : Finite (V ⧸ W.toSubmodule) := Finite.of_surjective _ W.toSubmodule.mkQ_surjective
  have hqfull := full_of_fixedFree X W.quotientRepresentation (s cubic) hxmem hqfree
  have hfQ := faithful_of_cubic K X hx hc W.quotientRepresentation
    (quotient_action_nontrivial ρ W K hfull hne) (s cubic) hxmem hqfree
  have hqff : IsFFModule W.quotientRepresentation := by
    rcases ff_alternative_of_codim_bound ρ W hA hbound with hff | hwstrong | hqstrong
    · exact hff.2
    · exact (no_strong W.toRepresentation K hS hfW X hx hc
        s hs hmark hwfull hn ho hF e hwstrong).elim
    · exact (no_strong W.quotientRepresentation K hS hfQ X hx hc
        s hs hmark hqfull hn ho hF e hqstrong).elim
  let N := QuotientLayers.moved W.quotientRepresentation K
  have hnat := moved_natural_of_ff W.quotientRepresentation K hS hfQ
    X hx hc s hs hmark hqfull hn ho hF e hqff N (QuotientLayers.moved_toSubmodule _ _)
  refine ⟨upper ρ W N, le_upper ρ W N, upper_moved ρ K W hfull, ?_⟩
  let a := liftedMultiplicityEquiv ρ W N s
  have ha := liftedMultiplicityEquiv_equivariant ρ W N K.subtype s hs
  rcases hnat with ⟨b, hb⟩ | ⟨b, hb⟩
  · exact Or.inl ⟨a.trans b, fun g v => by
      change b (a (sectionMultiplicityAction ρ K.subtype s hs W (upper ρ W N) (e.symm g) v)) = _
      rw [ha]
      exact hb g (a v)⟩
  · exact Or.inr ⟨a.trans b, fun g v => by
      change b (a (sectionMultiplicityAction ρ K.subtype s hs W (upper ρ W N) (e.symm g) v)) = _
      rw [ha]
      exact hb g (a v)⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory InvertedCubicTensor
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native
open LinearTwo.NoStrongMoved
universe u v
variable {D : Type u} [Group D] [Finite D]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (K X : Subgroup D)
    [K.Normal] [X.Normal] [IsQuasisimple K]
    (hS : IsSQTK KnownSimple.IsKnownSimple D) (hx : Nat.card X = 3)
    (hc : centralizer (K : Set D) ⊓ centralizer (X : Set D) ≤ X)
    (s : S₃ →* D) (hs : ∀ (k : K) g, Commute (k : D) (s g))
    (hmark : (alternatingGroup (Fin 3)).map s = X)
    (hg : subspaceCommutator ρ ⊤ X = ⊤)
    {F : Type} [Field F] [Finite F] [Algebra (ZMod 2) F]
    {n : ℕ} (hn : 1 < n) (ho : Odd n) (hF : Nat.card F = 2 ^ n) (e : K ≃* PSL(3,F))
    (W : Subrepresentation ρ)

include hS hx hc hs hmark hg hn ho hF e in
/-- Complete the natural first layer by the literal moved quotient when
needed. Both layers retain the same projective marking and may have different
natural/dual orientations. -/
theorem oneOrTwo_of_first_layer
    (C : Subrepresentation ρ) (hCW : C ≤ W)
    (hC : C.toSubmodule ≤ Representation.invariants (ρ.comp K.subtype))
    (hnat : IsProjectiveNaturalOrDual ho hF (projectiveMultiplicity ρ K.subtype s hs e C W))
    (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    OneOrTwoNaturalSections ρ K.subtype s hs e ho hF := by
  by_cases he : W.toSubmodule = subspaceCommutator ρ ⊤ K
  · exact ⟨C,W,hCW,hC,hnat,Or.inl (LinearTwo.central_quotient_of_moved_eq ρ K W he)⟩
  obtain ⟨M,hWM,hM,hnat₂⟩ := second_layer ρ K X hS hx hc
    s hs hmark hg hn ho hF e W hW hfull he A hA hbound
  exact ⟨C,W,hCW,hC,hnat,Or.inr ⟨M,hWM,hnat₂,LinearTwo.central_quotient_of_moved_eq ρ K M hM⟩⟩

variable
    {E : Type u} [Group E] [Finite E]
    {U : Type v} [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
    (σ : Representation (ZMod 2) E U)
    (hσ : B4Hypotheses KnownSimple.IsKnownSimple σ) (hff : IsFFModule σ)
    (a : generalizedFitting E ≃* K)
    (b : U ≃ₗ[ZMod 2] SectionMultiplicity ρ s (LinearTwo.centralBottom ρ K W) W)
    (hb : ∀ (g : generalizedFitting E) v,
      b (σ g v) = sectionMultiplicityAction ρ K.subtype s hs
        (LinearTwo.centralBottom ρ K W) W (a g) (b v))

include hS hx hc hs hmark hg hn ho hF e hσ hff a b hb in
/-- The full F.9.18 section argument gives one or two natural tensor layers.
The first layer comes from the actual faithful FF constituent and its compatible
multiplicity map; the second is proved by cubic FF recognition and quotient lifting. -/
theorem oneOrTwo_of_ff_orbit
    (hW : W.toSubmodule ≠ ⊥)
    (hfull : subspaceCommutator ρ W.toSubmodule K = W.toSubmodule)
    (A : Subgroup D) (hA : IsElementaryTwo A)
    (hbound : fixedCodim ρ A ≤ 2 * rank A) :
    OneOrTwoNaturalSections ρ K.subtype s hs e ho hF := by
  have hnat : IsProjectiveNaturalOrDual ho hF
      (projectiveMultiplicity ρ K.subtype s hs e (LinearTwo.centralBottom ρ K W) W) :=
    (naturalOrDual_and_ratio σ hσ hff hn ho hF
      (sectionMultiplicityAction ρ K.subtype s hs (LinearTwo.centralBottom ρ K W) W)
      e a b hb).1
  exact oneOrTwo_of_first_layer ρ K X hS hx hc s hs hmark hg hn ho hF e W
    (LinearTwo.centralBottom ρ K W) (LinearTwo.centralBottom_le ρ K W)
    (LinearTwo.centralBottom_central ρ K W) hnat hW hfull A hA hbound

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.RankTwo.Native
