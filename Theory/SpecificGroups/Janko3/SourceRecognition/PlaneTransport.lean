module
public import Theory.SpecificGroups.Janko3.SourceRecognition.SingerField

/-!
# The actual Singer and field subgroup in a marked plane normalizer

A natural GL₂(4) complement acts on the original elementary plane.
Its literal action equation extends the two coordinate maps to an
isomorphism of the whole normalizer with the affine group. Pulling back
the faithful field-affine subgroup constructs 16:(15:2) in the original G,
fixing every translation and retaining fourth-power Frobenius.

This is the local field-subgroup step following Aschbacher, *Sporadic
Groups* (1994), 46.14(5a), pp.257–258, toward the ambient recognition in
Aschbacher–Smith I.4.7(2), p.418. It makes no ambient Weyl or generation
assertion.
-/

public noncomputable section
open Subgroup
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition.SingerField hiding normalizer
namespace Sporadic.Janko3.SourceRecognition.PlaneTransport
variable {G : Type*} [Group G]

/-- Extend the given complement marking, including its literal action, to the whole normalizer. -/
theorem affine_equiv_of_complement
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (f : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (f c) (a x)) :
    ∃ e : normalizer (A : Set G) ≃* Plane ⋊[naturalAction] LinearGroup,
      (∀ x : A, e (inclusion le_normalizer x) = SemidirectProduct.inl (a x)) ∧
      (∀ c : C, e c = SemidirectProduct.inr (f c)) := by
  let Q := A.subgroupOf (normalizer (A : Set G))
  let q : Q ≃* Plane := (subgroupOfEquivOfLe le_normalizer).trans a
  let γ := Q.normalizerMonoidHom.comp (inclusion (Q.normalizer_eq_top ▸ le_top :
    C ≤ normalizer (Q : Set (normalizer (A : Set G)))))
  have hc (c : C) : (γ c).trans q = q.trans (naturalAction (f c)) := by
    apply MulEquiv.ext
    intro x
    exact ha c ((subgroupOfEquivOfLe le_normalizer) x)
  let m := SemidirectProduct.mulEquivSubgroup hC
  let e := m.symm.trans (SemidirectProduct.congr q f hc)
  refine ⟨e,?_,?_⟩
  · intro x
    have hm : m.symm (inclusion le_normalizer x) =
        SemidirectProduct.inl ((subgroupOfEquivOfLe le_normalizer).symm x) := by
      apply m.injective
      rw [m.apply_symm_apply]
      apply Subtype.ext
      simp [m]
    change SemidirectProduct.congr q f hc (m.symm _) = _
    rw [hm]
    apply SemidirectProduct.ext <;> simp [q]
  · intro c
    have hm : m.symm (c : normalizer (A : Set G)) = SemidirectProduct.inr c := by
      apply m.injective
      rw [m.apply_symm_apply]
      simp [m]
    change SemidirectProduct.congr q f hc (m.symm _) = _
    rw [hm]
    apply SemidirectProduct.ext <;> simp

/-- The full literal data of a field-affine subgroup in the original plane normalizer.
This is constructed from a natural complement below; it is not an ambient
recognition assumption. The named conclusion avoids re-elaborating the finite
field implementation in large source contexts. -/
@[expose] def FieldEmbedding
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : Model →* G) : Prop :=
      Function.Injective j ∧ j.range ≤ normalizer (A : Set G) ∧
      Nat.card j.range = 480 ∧
      (∀ x : Multiplicative K, j (root x) = (a.symm (rootCoordinates x) : G)) ∧
      (∀ u : Kˣ, j (scalar u) ∈ C.map (normalizer (A : Set G)).subtype) ∧
      j fieldElement ∈ C.map (normalizer (A : Set G)).subtype ∧
      orderOf (j fieldElement) = 2 ∧
      (∀ x : Multiplicative K,
        j fieldElement * (a.symm (rootCoordinates x) : G) * (j fieldElement)⁻¹ =
          (a.symm (rootCoordinates (Multiplicative.ofAdd (x.toAdd ^ 4))) : G)) ∧
      (∀ u : Kˣ, j fieldElement * j (scalar u) * (j fieldElement)⁻¹ = j (scalar (u ^ 4)))

private theorem map_field_scalar (j : Model →* G) (u : Kˣ) :
    j fieldElement * j (scalar u) * (j fieldElement)⁻¹ = j (scalar (u ^ 4)) := by
  have h := congrArg j (fieldElement_scalar u)
  rw [j.map_mul (fieldElement * scalar u) fieldElement⁻¹,
    j.map_mul fieldElement (scalar u),j.map_inv fieldElement] at h
  exact h

/-- A faithful field-affine embedding into the original normalizer, with the original plane fixed. -/
theorem field_embedding_of_complement
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (f : C ≃* LinearGroup) (a : A ≃* Plane)
    (hC : (A.subgroupOf (normalizer (A : Set G))).IsComplement' C)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (f c) (a x)) :
    ∃ j : Model →* G, FieldEmbedding A C a j := by
  obtain ⟨e,he,hc⟩ := affine_equiv_of_complement A C f a hC ha
  let j := (normalizer (A : Set G)).subtype.comp (e.symm.toMonoidHom.comp affineEmbedding)
  have hjr (b : LinearGroup) :
      ((e.symm (SemidirectProduct.inr b) : normalizer (A : Set G)) : G) ∈
        C.map (normalizer (A : Set G)).subtype := by
    have hh := hc (f.symm b)
    rw [f.apply_symm_apply] at hh
    rw [← hh,e.symm_apply_apply]
    exact ⟨f.symm b,(f.symm b).property,rfl⟩
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (e.symm.injective.comp affineEmbedding_injective)
  have hroot (x : Multiplicative K) : j (root x) = (a.symm (rootCoordinates x) : G) := by
    change ((e.symm (affineEmbedding (root x)) : normalizer (A : Set G)) : G) = _
    have hh := he (a.symm (rootCoordinates x))
    rw [a.apply_symm_apply] at hh
    rw [affineEmbedding_root,← hh,e.symm_apply_apply]
    rfl
  refine ⟨j,hj,?_,?_,hroot,?_,?_,?_,?_,?_⟩
  · rintro _ ⟨x,rfl⟩
    exact (e.symm (affineEmbedding x)).property
  · exact (Nat.card_congr (MonoidHom.ofInjective hj).toEquiv).symm.trans model_card
  · intro u
    change ((e.symm (affineEmbedding (scalar u)) : normalizer (A : Set G)) : G) ∈ _
    rw [scalar,MonoidHom.comp_apply,affineEmbedding,SemidirectProduct.map_inr]
    exact hjr _
  · change ((e.symm (affineEmbedding fieldElement) : normalizer (A : Set G)) : G) ∈ _
    rw [fieldElement,affineEmbedding,SemidirectProduct.map_inr]
    exact hjr _
  · exact (orderOf_injective j hj fieldElement).trans fieldElement_order
  · intro x
    rw [← hroot,← hroot]
    simpa only [map_mul,map_inv] using congrArg j (fieldElement_conjugation x)
  · exact map_field_scalar j

end Sporadic.Janko3.SourceRecognition.PlaneTransport
