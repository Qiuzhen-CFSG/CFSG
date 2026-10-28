module

public import Theory.Representation.SymplecticConjugatePair.Ambient.Model
public import Theory.Representation.SymplecticConjugatePair.Ambient.Swapping
public import Theory.Representation.SymplecticConjugatePair.Ambient.Semilinear

/-!
# Generators and summand permutation in the standard symplectic enlargement

The separate scalars, full paired symplectic matrices and simultaneous field
maps preserve both coordinate summands. The graph operator interchanges them.
Closure under products and inverses therefore proves that the actual generated
subgroup permutes the summands, with a stabilizer of index two.

The generator homomorphisms land in the published `standardAmbient`, and its
evaluation action is faithful. No normalizer-coverage or descent premise is used.

Source: Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
namespace SymplecticConjugatePair.Ambient
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

private def BlockPermutation (e : Space F ≃ₗ[ZMod 2] Space F) : Prop :=
  ((∀ v, e v ∈ firstSummand ↔ v ∈ firstSummand) ∧
    (∀ v, e v ∈ secondSummand ↔ v ∈ secondSummand)) ∨
  ((∀ v, e v ∈ firstSummand ↔ v ∈ secondSummand) ∧
    (∀ v, e v ∈ secondSummand ↔ v ∈ firstSummand))

omit [Finite F] [CharP F 2] in
private lemma blockPermutation_mul {e f : Space F ≃ₗ[ZMod 2] Space F}
    (he : BlockPermutation e) (hf : BlockPermutation f) : BlockPermutation (e * f) := by
  rcases he with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩ <;>
    rcases hf with ⟨hf₁, hf₂⟩ | ⟨hf₁, hf₂⟩
  · exact Or.inl ⟨fun v => (he₁ (f v)).trans (hf₁ v),
      fun v => (he₂ (f v)).trans (hf₂ v)⟩
  · exact Or.inr ⟨fun v => (he₁ (f v)).trans (hf₁ v),
      fun v => (he₂ (f v)).trans (hf₂ v)⟩
  · exact Or.inr ⟨fun v => (he₁ (f v)).trans (hf₂ v),
      fun v => (he₂ (f v)).trans (hf₁ v)⟩
  · exact Or.inl ⟨fun v => (he₁ (f v)).trans (hf₂ v),
      fun v => (he₂ (f v)).trans (hf₁ v)⟩

omit [Finite F] [CharP F 2] in
private lemma blockPermutation_inv {e : Space F ≃ₗ[ZMod 2] Space F}
    (he : BlockPermutation e) : BlockPermutation e⁻¹ := by
  rcases he with ⟨he₁, he₂⟩ | ⟨he₁, he₂⟩
  · left
    constructor
    · intro v
      simpa only [show e (e⁻¹ v) = v from e.apply_symm_apply v] using (he₁ (e⁻¹ v)).symm
    · intro v
      simpa only [show e (e⁻¹ v) = v from e.apply_symm_apply v] using (he₂ (e⁻¹ v)).symm
  · right
    constructor
    · intro v
      simpa only [show e (e⁻¹ v) = v from e.apply_symm_apply v] using (he₂ (e⁻¹ v)).symm
    · intro v
      simpa only [show e (e⁻¹ v) = v from e.apply_symm_apply v] using (he₁ (e⁻¹ v)).symm

lemma scalarPair_mem_standardAmbient (a b : Fˣ) : scalarPair a b ∈ standardAmbient (F := F) :=
  Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨(a,b), rfl⟩)))
lemma fieldPair_mem_standardAmbient (σ : F ≃+* F) : fieldPair σ ∈ standardAmbient (F := F) :=
  Subgroup.subset_closure (Or.inl (Or.inr ⟨σ, rfl⟩))
lemma graphSwap_mem_standardAmbient : graphSwap ∈ standardAmbient (F := F) :=
  Subgroup.subset_closure (Or.inr rfl)

noncomputable def scalarHom : (Fˣ × Fˣ) →* standardAmbient (F := F) where
  toFun p := ⟨scalarPair p.1 p.2, scalarPair_mem_standardAmbient _ _⟩
  map_one' := by ext v i <;> simp [scalarPair, LinearEquiv.smulOfUnit]
  map_mul' p q := by ext v i <;> simp [scalarPair, LinearEquiv.smulOfUnit, mul_smul]

noncomputable def fieldHom : (F ≃+* F) →* standardAmbient (F := F) where
  toFun σ := ⟨fieldPair σ, fieldPair_mem_standardAmbient σ⟩
  map_one' := by ext v i <;> rfl
  map_mul' σ τ := by ext v i <;> rfl

noncomputable def graphActor : standardAmbient (F := F) :=
  ⟨graphSwap, graphSwap_mem_standardAmbient⟩

instance standardAmbient_finite : Finite (standardAmbient (F := F)) :=
  Finite.of_injective (fun g : standardAmbient (F := F) => (g.val : Space F → Space F))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

lemma standardAction_injective : Function.Injective (standardAction (F := F)) := by
  intro g h he
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  exact LinearMap.congr_fun he v

private lemma standard_blockPermutation (e : Space F ≃ₗ[ZMod 2] Space F)
    (hg : e ∈ standardAmbient (F := F)) : BlockPermutation e := by
  change e ∈ Subgroup.closure _ at hg
  induction hg using Subgroup.closure_induction with
  | mem e he =>
    rcases he with ((⟨⟨a,b⟩, rfl⟩ | ⟨x, rfl⟩) | ⟨σ, rfl⟩) | rfl
    · left
      constructor <;> intro v <;>
        simp only [mem_firstSummand, mem_secondSummand]
      · change ((LinearEquiv.smulOfUnit b : Vector F ≃ₗ[F] Vector F) v.2 = 0) ↔ _
        exact (LinearEquiv.smulOfUnit b).map_eq_zero_iff
      · change ((LinearEquiv.smulOfUnit a : Vector F ≃ₗ[F] Vector F) v.1 = 0) ↔ _
        exact (LinearEquiv.smulOfUnit a).map_eq_zero_iff
    · left
      constructor <;> intro v <;> simp only [mem_firstSummand, mem_secondSummand]
      · change symplecticNatural 2 (DiagramAutomorphisms.ExceptionalGraph.graphAut x) v.2 = 0 ↔ _
        exact ⟨fun h => ((symplecticNatural 2).apply_bijective _).1 (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
      · change symplecticNatural 2 x v.1 = 0 ↔ _
        exact ⟨fun h => ((symplecticNatural 2).apply_bijective _).1 (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩
    · left
      constructor <;> intro v <;>
        simp only [mem_firstSummand, mem_secondSummand]
      · exact (fieldVector σ).map_eq_zero_iff
      · exact (fieldVector σ).map_eq_zero_iff
    · right
      constructor <;> intro v <;>
        simp only [graphSwap_apply, mem_firstSummand, mem_secondSummand]
      · exact (fieldVector (frobeniusEquiv F 2)).map_eq_zero_iff
  | one => exact Or.inl ⟨fun _ => Iff.rfl, fun _ => Iff.rfl⟩
  | mul _ _ _ _ he hf => exact blockPermutation_mul he hf
  | inv _ _ he => exact blockPermutation_inv he

lemma standardAction_permutesSummands : PermutesSummands (standardAction (F := F)) := by
  intro g
  rcases standard_blockPermutation g.val g.property with h | h
  · exact Or.inl h
  · exact Or.inr ⟨fun v hv => (h.2 v).mpr hv, fun v hv => (h.1 v).mpr hv⟩

lemma graphActor_swapsSummands : SwapsSummands (standardAction (F := F)) graphActor := by
  constructor <;> intro v hv
  · change graphSwap v ∈ secondSummand
    simpa only [graphSwap_apply, mem_secondSummand] using (mem_firstSummand v).mp hv
  · change graphSwap v ∈ firstSummand
    rw [mem_firstSummand, graphSwap_apply]
    rw [(mem_secondSummand v).mp hv, map_zero]

lemma standard_stabilizer_index_two :
    (summandStabilizer (standardAction (F := F))).index = 2 :=
  summandStabilizer_index_two standardAction standardAction_permutesSummands
    ⟨graphActor, graphActor_swapsSummands⟩
/-- The actual subgroup preserving the first summand; all its elements also
preserve the second summand by `standardAction_permutesSummands`. -/
noncomputable abbrev standardPreserving := summandStabilizer (standardAction (F := F))

@[simp] lemma scalarHom_action (a b : Fˣ) (v : Space F) :
    standardAction (scalarHom (a,b)) v = (a • v.1, b • v.2) := rfl

@[simp] lemma fieldHom_action (σ : F ≃+* F) (v : Space F) :
    standardAction (fieldHom σ) v = (fieldVector σ v.1, fieldVector σ v.2) := rfl

lemma scalarHom_injective : Function.Injective (scalarHom (F := F)) := by
  intro p q he
  have h₁ := congrArg (fun g : standardAmbient (F := F) =>
    (standardAction g ((fun _ => 1), 0)).1 (Sum.inl 0)) he
  have h₂ := congrArg (fun g : standardAmbient (F := F) =>
    (standardAction g (0, (fun _ => 1))).2 (Sum.inl 0)) he
  apply Prod.ext <;> apply Units.ext
  · change (p.1 : F) * 1 = (q.1 : F) * 1 at h₁
    simpa only [mul_one] using h₁
  · change (p.2 : F) * 1 = (q.2 : F) * 1 at h₂
    simpa only [mul_one] using h₂

lemma fieldHom_injective : Function.Injective (fieldHom (F := F)) := by
  intro σ τ he
  ext c
  exact congrArg (fun g : standardAmbient (F := F) =>
    (standardAction g ((fun _ => c), 0)).1 (Sum.inl 0)) he

lemma graphActor_square : (graphActor (F := F))^2 = fieldHom (frobeniusEquiv F 2) :=
  Subtype.ext graphSwap_square

lemma fullHom_le_stabilizer : (fullHom (F := F)).range ≤ standardPreserving := by
  rintro _ ⟨x, rfl⟩ v
  rw [mem_firstSummand, mem_firstSummand]
  change symplecticNatural 2 (DiagramAutomorphisms.ExceptionalGraph.graphAut x) v.2 = 0 ↔ _
  exact ⟨fun h => ((symplecticNatural 2).apply_bijective _).1
    (h.trans (map_zero _).symm), fun h => by rw [h, map_zero]⟩

end SymplecticConjugatePair.Ambient
