module

public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Operators
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.Coefficients

/-!
# The coefficient homomorphism of the actual summand stabilizer

Every generator is either diagonal semilinear with the same coefficient map
on both summands, or swapping semilinear with a Frobenius difference between
the two coefficient maps. These two alternatives are closed under products.
Finiteness allows positive-word induction on the generated group, so every
summand-preserving element is genuinely semilinear over one coefficient map.

Uniqueness on the nonzero paired space constructs `standardCoefficient` as an
actual homomorphism. Its kernel is exactly the F-linear actors, contains the
full symplectic image, and has corank at most one in any elementary subgroup.
Identifying its square-one elements with the full image remains a separate
scalar-kernel calculation.

Source: Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`.
-/

@[expose] public section

open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
namespace SymplecticConjugatePair.Ambient
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

private def DiagonalCoefficient (e : Space F ≃ₗ[ZMod 2] Space F) : Prop :=
  ∃ σ : F ≃+* F, ∀ (c d : F) (v : Space F),
    e (c • v.1, d • v.2) = (σ c • (e v).1, σ d • (e v).2)

private def SwappingCoefficient (e : Space F ≃ₗ[ZMod 2] Space F) : Prop :=
  ∃ σ : F ≃+* F, ∀ (c d : F) (v : Space F),
    e (c • v.1, d • v.2) = (σ d • (e v).1, (σ c)^2 • (e v).2)

private def HasBlockCoefficient (e : Space F ≃ₗ[ZMod 2] Space F) : Prop :=
  DiagonalCoefficient e ∨ SwappingCoefficient e

private lemma hasBlockCoefficient_mul {e f : Space F ≃ₗ[ZMod 2] Space F}
    (he : HasBlockCoefficient e) (hf : HasBlockCoefficient f) : HasBlockCoefficient (e*f) := by
  rcases he with ⟨σ, he⟩ | ⟨σ, he⟩ <;> rcases hf with ⟨τ, hf⟩ | ⟨τ, hf⟩
  · refine Or.inl ⟨σ*τ, ?_⟩
    intro c d v
    change e (f (c • v.1, d • v.2)) = _
    rw [hf c d v, he (τ c) (τ d) (f v)]
    rfl
  · refine Or.inr ⟨σ*τ, ?_⟩
    intro c d v
    change e (f (c • v.1, d • v.2)) = _
    rw [hf c d v, he (τ d) ((τ c)^2) (f v), map_pow]
    rfl
  · refine Or.inr ⟨σ*τ, ?_⟩
    intro c d v
    change e (f (c • v.1, d • v.2)) = _
    rw [hf c d v, he (τ c) (τ d) (f v)]
    rfl
  · refine Or.inl ⟨frobeniusEquiv F 2 * (σ*τ), ?_⟩
    intro c d v
    change e (f (c • v.1, d • v.2)) = _
    rw [hf c d v, he (τ d) ((τ c)^2) (f v), map_pow]
    rfl

private lemma standard_hasBlockCoefficient (e : Space F ≃ₗ[ZMod 2] Space F)
    (he : e ∈ standardAmbient (F := F)) : HasBlockCoefficient e := by
  let _ : Finite (Space F ≃ₗ[ZMod 2] Space F) :=
    Finite.of_injective (fun e : Space F ≃ₗ[ZMod 2] Space F => (e : Space F → Space F))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  change e ∈ (Subgroup.closure _).toSubmonoid at he
  rw [Subgroup.closure_toSubmonoid_of_finite] at he
  induction he using Submonoid.closure_induction with
  | mem e he =>
    rcases he with ((⟨⟨a,b⟩, rfl⟩ | ⟨x, rfl⟩) | ⟨σ, rfl⟩) | rfl
    · refine Or.inl ⟨1, ?_⟩
      intro c d v
      apply Prod.ext <;> ext i
      · change (a : F) * (c * v.1 i) = c * ((a : F) * v.1 i)
        exact mul_left_comm _ _ _
      · change (b : F) * (d * v.2 i) = d * ((b : F) * v.2 i)
        exact mul_left_comm _ _ _
    · refine Or.inl ⟨1, ?_⟩
      intro c d v
      change (symplecticNatural 2 x (c • v.1),
        symplecticNatural 2 (DiagramAutomorphisms.ExceptionalGraph.graphAut x) (d • v.2)) = _
      simp only [map_smul]
      rfl
    · refine Or.inl ⟨σ, ?_⟩
      intro c d v
      apply Prod.ext <;> ext i
      · exact map_mul σ c (v.1 i)
      · exact map_mul σ d (v.2 i)
    · refine Or.inr ⟨1, ?_⟩
      intro c d v
      apply Prod.ext
      · rfl
      · ext i
        exact map_mul (frobeniusEquiv F 2) c (v.1 i)
  | one => exact Or.inl ⟨1, fun _ _ _ => rfl⟩
  | mul _ _ _ _ he hf => exact hasBlockCoefficient_mul he hf

private lemma swappingCoefficient_swaps (g : standardAmbient (F := F))
    (hg : SwappingCoefficient g.val) : SwapsSummands standardAction g := by
  obtain ⟨σ, hσ⟩ := hg
  constructor
  · intro v hv
    have he := congrArg Prod.fst (hσ 1 0 v)
    have hz : v.2 = 0 := (mem_firstSummand v).mp hv
    change (g.val (1 • v.1, 0 • v.2)).1 = σ 0 • (g.val v).1 at he
    simp only [one_smul, zero_smul, map_zero] at he
    rw [show (v.1, (0 : Vector F)) = v from Prod.ext rfl hz.symm] at he
    exact (mem_secondSummand _).mpr he
  · intro v hv
    have he := congrArg Prod.snd (hσ 0 1 v)
    have hz : v.1 = 0 := (mem_secondSummand v).mp hv
    change (g.val (0 • v.1, 1 • v.2)).2 = (σ 0)^2 • (g.val v).2 at he
    simp only [one_smul, zero_smul, map_zero, zero_pow (by decide : 2 ≠ 0)] at he
    rw [show ((0 : Vector F), v.2) = v from Prod.ext hz.symm rfl] at he
    exact (mem_firstSummand _).mpr he

lemma standard_preserving_semilinear (g : standardPreserving (F := F)) :
    ∃ σ : F ≃+* F, ∀ (c : F) (v : Space F),
      standardAction g.val (c • v) = σ c • standardAction g.val v := by
  rcases standard_hasBlockCoefficient g.val.val g.val.property with ⟨σ, hσ⟩ | hs
  · exact ⟨σ, fun c v => hσ c c v⟩
  · exact False.elim (swapping_not_mem_stabilizer standardAction
      (swappingCoefficient_swaps g.val hs) g.property)

noncomputable def standardCoefficient : standardPreserving (F := F) →* (F ≃+* F) :=
  SemilinearCoefficients.coefficientHom (standardAction.comp standardPreserving.subtype)
    standard_preserving_semilinear

lemma standardCoefficient_smul (g : standardPreserving (F := F)) (c : F) (v : Space F) :
    standardAction g.val (c • v) = standardCoefficient g c • standardAction g.val v :=
  SemilinearCoefficients.coefficientHom_smul
    (standardAction.comp standardPreserving.subtype) standard_preserving_semilinear g c v

lemma standardCoefficient_eq_one_iff (g : standardPreserving (F := F)) :
    standardCoefficient g = 1 ↔
      ∀ (c : F) (v : Space F), standardAction g.val (c • v) = c • standardAction g.val v :=
  SemilinearCoefficients.coefficient_eq_one_iff
    (standardAction.comp standardPreserving.subtype) standardCoefficient standardCoefficient_smul g

lemma standardCoefficient_kernel_relativeIndex_le_two
    {A : Subgroup (standardPreserving (F := F))} (hA : IsElementaryAbelian 2 A) :
    (A ⊓ standardCoefficient.ker).relIndex A ≤ 2 :=
  SemilinearCoefficients.kernel_relativeIndex_le_two standardCoefficient hA

noncomputable def fullPreservingHom : Sp F →* standardPreserving (F := F) :=
  fullHom.codRestrict _ (fun g => fullHom_le_stabilizer ⟨g, rfl⟩)

@[simp] lemma fullPreservingHom_coe (g : Sp F) :
    (fullPreservingHom g).val = fullHom g := rfl

@[simp] lemma standardCoefficient_fullPreservingHom (g : Sp F) :
    standardCoefficient (fullPreservingHom g) = 1 := by
  apply (standardCoefficient_eq_one_iff _).mpr
  intro c v
  change pair DiagramAutomorphisms.ExceptionalGraph.graphAut g (c • v) =
    c • pair DiagramAutomorphisms.ExceptionalGraph.graphAut g v
  exact map_smul _ _ _

end SymplecticConjugatePair.Ambient
