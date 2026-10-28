module
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.ScalarKernel.Conjugation
public import Theory.Representation.SymplecticConjugatePair.Ambient.TwoGeometry.StandardCoefficients

/-!
# Normal forms in the generated paired operator group

Moving each generator past the scalar and full symplectic factors gives a
scalar–symplectic–field form with at most one graph factor. The square of the
graph factor is simultaneous Frobenius. Positive-word induction suffices
because the actual binary operator group is finite.
Source: Aschbacher–Smith H.7, printed pp.388–389 of `refs/quasithin.pdf`.
-/
@[expose] public section
open Representation BinaryOffender Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
namespace SymplecticConjugatePair.Ambient
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] [Finite F] [CharP F 2]

lemma standardAmbient_generators :
    Subgroup.closure (Set.range (scalarHom (F := F)) ∪ (fullHom (F := F)).range ∪
      Set.range (fieldHom (F := F)) ∪ {graphActor}) = ⊤ := by
  let H := Subgroup.closure (Set.range (scalarHom (F := F)) ∪ (fullHom (F := F)).range ∪
      Set.range (fieldHom (F := F)) ∪ {graphActor})
  have h : standardAmbient (F := F) ≤ H.map standardAmbient.subtype := by
    apply (Subgroup.closure_le _).mpr
    intro e he
    rcases he with ((⟨p, rfl⟩ | ⟨x, rfl⟩) | ⟨σ, rfl⟩) | rfl
    · exact ⟨scalarHom p, Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨p,rfl⟩))), rfl⟩
    · exact ⟨fullHom x, Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨x,rfl⟩))), rfl⟩
    · exact ⟨fieldHom σ, Subgroup.subset_closure (Or.inl (Or.inr ⟨σ,rfl⟩)), rfl⟩
    · exact ⟨graphActor, Subgroup.subset_closure (Or.inr rfl), rfl⟩
  apply top_unique
  intro s _
  obtain ⟨t, ht, he⟩ := h s.property
  have : t = s := Subtype.ext he
  exact this ▸ ht

lemma standardAmbient_induction {P : standardAmbient (F := F) → Prop}
    (one : P 1)
    (scalar : ∀ p s, P s → P (scalarHom p * s))
    (full : ∀ x s, P s → P (fullHom x * s))
    (field : ∀ σ s, P s → P (fieldHom σ * s))
    (graph : ∀ s, P s → P (graphActor * s)) (s : standardAmbient (F := F)) : P s := by
  have hs : s ∈ (Subgroup.closure (Set.range (scalarHom (F := F)) ∪
      (fullHom (F := F)).range ∪ Set.range (fieldHom (F := F)) ∪ {graphActor})).toSubmonoid := by
    rw [standardAmbient_generators]
    trivial
  rw [Subgroup.closure_toSubmonoid_of_finite] at hs
  induction hs using Submonoid.closure_induction_left with
  | one => exact one
  | mul_left e he s _ ih =>
    rcases he with ((⟨p, rfl⟩ | ⟨x, rfl⟩) | ⟨σ, rfl⟩) | rfl
    · exact scalar p s ih
    · exact full x s ih
    · exact field σ s ih
    · exact graph s ih

lemma fieldHom_mul_scalarHom (σ : F ≃+* F) (p : Fˣ × Fˣ) :
    fieldHom σ * scalarHom p =
      scalarHom (Units.map σ.toMonoidHom p.1, Units.map σ.toMonoidHom p.2) * fieldHom σ := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply Prod.ext <;> ext i
  · exact map_mul σ _ _
  · exact map_mul σ _ _

lemma graphActor_mul_scalarHom (p : Fˣ × Fˣ) :
    graphActor * scalarHom p = scalarHom (p.2, p.1^2) * graphActor := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · rfl
  · ext i
    exact map_mul (frobeniusEquiv F 2) _ _

lemma graphActor_commute_fieldHom (σ : F ≃+* F) :
    Commute (graphActor (F := F)) (fieldHom σ) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply Prod.ext
  · rfl
  · ext i
    exact (map_pow σ _ 2).symm

private lemma field_mul_diagonal (τ : F ≃+* F) (p : Fˣ × Fˣ) (x : Sp F) (σ : F ≃+* F) :
    fieldHom τ * (scalarHom p * fullHom x * fieldHom σ) =
      scalarHom (Units.map τ.toMonoidHom p.1, Units.map τ.toMonoidHom p.2) *
        fullHom (fieldAutomorphism τ x) * fieldHom (τ*σ) := by
  rw [← mul_assoc, ← mul_assoc, fieldHom_mul_scalarHom, mul_assoc _ (fieldHom τ),
    actor_mul_fullHom, standardConjugation_fieldHom, ← mul_assoc, mul_assoc,
    ← map_mul]

private lemma graph_mul_diagonal (p : Fˣ × Fˣ) (x : Sp F) (σ : F ≃+* F) :
    graphActor * (scalarHom p * fullHom x * fieldHom σ) =
      scalarHom (p.2,p.1^2) * fullHom (graphAut x) * fieldHom σ * graphActor := by
  rw [← mul_assoc, ← mul_assoc, graphActor_mul_scalarHom,
    mul_assoc _ graphActor, actor_mul_fullHom, standardConjugation_graphActor,
    ← mul_assoc, mul_assoc, (graphActor_commute_fieldHom σ).eq]
  simp only [mul_assoc]

/-- Every actual generated operator has at most one final graph factor. -/
theorem standard_normalForm (s : standardAmbient (F := F)) :
    ∃ (p : Fˣ × Fˣ) (x : Sp F) (σ : F ≃+* F),
      s = scalarHom p * fullHom x * fieldHom σ ∨
      s = scalarHom p * fullHom x * fieldHom σ * graphActor := by
  induction s using standardAmbient_induction with
  | one => exact ⟨1,1,1,Or.inl (by simp)⟩
  | scalar q s ih =>
    obtain ⟨p,x,σ,h | h⟩ := ih
    · refine ⟨q*p,x,σ,Or.inl ?_⟩
      rw [h, map_mul]
      simp only [mul_assoc]
    · refine ⟨q*p,x,σ,Or.inr ?_⟩
      rw [h, map_mul]
      simp only [mul_assoc]
  | full y s ih =>
    obtain ⟨p,x,σ,h | h⟩ := ih
    · refine ⟨p,y*x,σ,Or.inl ?_⟩
      rw [h, map_mul, ← mul_assoc, ← mul_assoc,
        (scalarHom_commute_fullHom p y).symm.eq]
      simp only [mul_assoc]
    · refine ⟨p,y*x,σ,Or.inr ?_⟩
      rw [h, map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        (scalarHom_commute_fullHom p y).symm.eq]
      simp only [mul_assoc]
  | field τ s ih =>
    obtain ⟨p,x,σ,h | h⟩ := ih
    · exact ⟨_,_,_, Or.inl (by rw [h, field_mul_diagonal])⟩
    · exact ⟨_,_,_, Or.inr (by rw [h, ← mul_assoc, field_mul_diagonal])⟩
  | graph s ih =>
    obtain ⟨p,x,σ,h | h⟩ := ih
    · exact ⟨_,_,_,Or.inr (by rw [h, graph_mul_diagonal])⟩
    · refine ⟨(p.2,p.1^2),graphAut x,σ * frobeniusEquiv F 2,Or.inl ?_⟩
      rw [h, ← mul_assoc, graph_mul_diagonal, mul_assoc _ graphActor,
        ← pow_two, graphActor_square, map_mul]
      simp only [mul_assoc]

lemma scalarHom_le_stabilizer : (scalarHom (F := F)).range ≤ standardPreserving := by
  rintro _ ⟨p,rfl⟩ v
  rw [mem_firstSummand, mem_firstSummand]
  change (LinearEquiv.smulOfUnit p.2 : Vector F ≃ₗ[F] Vector F) v.2 = 0 ↔ _
  exact (LinearEquiv.smulOfUnit p.2).map_eq_zero_iff

lemma fieldHom_le_stabilizer : (fieldHom (F := F)).range ≤ standardPreserving := by
  rintro _ ⟨σ,rfl⟩ v
  rw [mem_firstSummand, mem_firstSummand]
  exact (fieldVector σ).map_eq_zero_iff

lemma standard_diagonal_mem (p : Fˣ × Fˣ) (x : Sp F) (σ : F ≃+* F) :
    scalarHom p * fullHom x * fieldHom σ ∈ standardPreserving :=
  standardPreserving.mul_mem (standardPreserving.mul_mem
    (scalarHom_le_stabilizer ⟨p,rfl⟩) (fullHom_le_stabilizer ⟨x,rfl⟩))
    (fieldHom_le_stabilizer ⟨σ,rfl⟩)

lemma standard_preserving_normalForm (g : standardPreserving (F := F)) :
    ∃ (p : Fˣ × Fˣ) (x : Sp F) (σ : F ≃+* F),
      g.val = scalarHom p * fullHom x * fieldHom σ := by
  obtain ⟨p,x,σ,h | h⟩ := standard_normalForm g.val
  · exact ⟨p,x,σ,h⟩
  · have hm := g.property
    rw [h, standardPreserving.mul_mem_cancel_left (standard_diagonal_mem p x σ)] at hm
    exact False.elim (swapping_not_mem_stabilizer standardAction graphActor_swapsSummands hm)

noncomputable def scalarPreservingHom : (Fˣ × Fˣ) →* standardPreserving (F := F) :=
  scalarHom.codRestrict _ (fun p => scalarHom_le_stabilizer ⟨p,rfl⟩)

noncomputable def fieldPreservingHom : (F ≃+* F) →* standardPreserving (F := F) :=
  fieldHom.codRestrict _ (fun σ => fieldHom_le_stabilizer ⟨σ,rfl⟩)

@[simp] lemma scalarPreservingHom_coe (p : Fˣ × Fˣ) :
    (scalarPreservingHom p).val = scalarHom p := rfl

@[simp] lemma fieldPreservingHom_coe (σ : F ≃+* F) :
    (fieldPreservingHom σ).val = fieldHom σ := rfl

@[simp] lemma standardCoefficient_scalarPreservingHom (p : Fˣ × Fˣ) :
    standardCoefficient (scalarPreservingHom p) = 1 := by
  apply (standardCoefficient_eq_one_iff _).mpr
  intro c v
  apply Prod.ext <;> ext i
  · exact mul_left_comm (p.1 : F) c (v.1 i)
  · exact mul_left_comm (p.2 : F) c (v.2 i)

@[simp] lemma standardCoefficient_fieldPreservingHom (σ : F ≃+* F) :
    standardCoefficient (fieldPreservingHom σ) = σ := by
  apply SemilinearCoefficients.coefficient_unique
    (standardAction.comp standardPreserving.subtype) (fieldPreservingHom σ)
    (standardCoefficient_smul _)
  intro c v
  apply Prod.ext <;> ext i
  · exact map_mul σ c (v.1 i)
  · exact map_mul σ c (v.2 i)

/-- The field factor in the preserving normal form is the actual coefficient map. -/
lemma standard_coefficient_normalForm (g : standardPreserving (F := F)) :
    ∃ (p : Fˣ × Fˣ) (x : Sp F),
      g.val = scalarHom p * fullHom x * fieldHom (standardCoefficient g) := by
  obtain ⟨p,x,σ,h⟩ := standard_preserving_normalForm g
  have hg : g = scalarPreservingHom p * fullPreservingHom x * fieldPreservingHom σ :=
    Subtype.ext h
  have hc : standardCoefficient g = σ := by
    rw [hg, map_mul, map_mul, standardCoefficient_scalarPreservingHom,
      standardCoefficient_fullPreservingHom, standardCoefficient_fieldPreservingHom,
      one_mul, one_mul]
  exact ⟨p,x,by rw [hc]; exact h⟩

lemma standard_coefficient_kernel_normalForm (g : standardPreserving (F := F))
    (hg : standardCoefficient g = 1) :
    ∃ (p : Fˣ × Fˣ) (x : Sp F), g.val = scalarHom p * fullHom x := by
  obtain ⟨p,x,h⟩ := standard_coefficient_normalForm g
  exact ⟨p,x,by simpa only [hg, map_one, mul_one] using h⟩

end SymplecticConjugatePair.Ambient
