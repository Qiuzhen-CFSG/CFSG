module
public import Theory.Representation.SL2OrthogonalCover.FixedField.Alignment
public import Theory.Representation.SL2NaturalOffenders.FixedField.Alignment
public import Theory.Representation.SL2NaturalOffenders.FixedField.Extraction

/-!
# The fixed orthogonal cover of an outer involution

The simultaneous natural-module alignment lifts uniquely through the full
orthogonal cover. Restricting this lifted alignment and the same actor marking
to their literal fixed subgroups identifies the fixed cover with the cover over
the actual fixed field. The descent preserves both the coordinate action and
the projection to the natural module.

The unconditional endpoint supplies the full-cover descent in
Aschbacher–Smith, Lemma 2.4.12(2), printed p.532. It uses the given involution
and its original intertwining action throughout.
-/

public section
noncomputable section
namespace Representation.SL2OrthogonalCover.FixedField
open Matrix SL2NaturalOffenders.FixedField
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The original outer actor and its full cover have a coherent entrywise
field marking, over the literal natural projection. -/
theorem outer_involution_full_alignment
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hinv : Function.Involutive E)
    (he : ∀ g u, E (action g u) = action (a g) (E u))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g, a = MulAut.conj g) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧ Function.Involutive σ ∧
      ∃ (β : MulAut (SL F)) (A : Space F ≃ₗ[ZMod 2] Space F)
        (e B : Plane F ≃ₗ[ZMod 2] Plane F),
      (∀ g u, A (action g u) = action (β g) (A u)) ∧
      (∀ g, β (a g) = Theory.PSL2.sl2FieldAut σ (β g)) ∧
      (∀ u, A (E u) = fun i => σ (A u i)) ∧
      (∀ g v, e (natural g v) = natural (a g) (e v)) ∧
      (∀ u, projection (E u) = e (projection u)) ∧
      (∀ g v, B (natural g v) = natural (β g) (B v)) ∧
      (∀ v, B (e v) = fun i => σ (B v i)) ∧
      ∀ u, projection (A u) = B (projection u) := by
  obtain ⟨e, he', hp⟩ := intertwiner_descends a E he
  have hinve : Function.Involutive e := by
    intro v
    obtain ⟨u, rfl⟩ := projection_surjective v
    rw [← hp, ← hp, hinv]
  obtain ⟨σ, hσne, hσ, c, B₀, hB₀, hβ, hBE⟩ :=
    outer_involution_natural_alignment a e hinve he' ha houter
  let β := MulAut.conj c⁻¹
  let B := B₀.restrictScalars (ZMod 2)
  obtain ⟨A, hA, hAp, hAE⟩ := exists_alignment_lift n hn hF a E he e hp σ β B
    hB₀ hβ (fun v i => congrFun (hBE v) i)
  have hAE' : ∀ u, A (E u) = fun i => σ (A u i) := by
    intro u
    rw [hAE]
    exact funext (coefficientEquiv_apply σ (A u))
  exact ⟨σ, hσne, hσ, β, A, e, B, hA, hβ, hAE', he', hp, hB₀, hBE, hAp⟩

/-- Full orthogonal fixed-field descent retains the specified actor and vector
markings; the action is the literal orthogonal formula over the fixed field. -/
theorem fixed_cover_equivariance
    (a : MulAut (SL F)) (σ : F ≃+* F) (β : MulAut (SL F))
    (E A : Space F ≃ₗ[ZMod 2] Space F)
    (hβ : ∀ g, β (a g) = Theory.PSL2.sl2FieldAut σ (β g))
    (hA : ∀ u, A (E u) = fun i => σ (A u i))
    (hact : ∀ g u, A (action g u) = action (β g) (A u))
    (g : a.fixedSubgroup) (v w : fixedVectors E)
    (hw : (w : Space F) = action (g : SL F) (v : Space F)) :
    fixedVectorEquiv σ E A hA w =
      action (fixedActorEquiv a σ β hβ g) (fixedVectorEquiv σ E A hA v) := by
  have hg : Matrix.SpecialLinearGroup.map (FixedBy.subfield F σ).subtype
      (fixedActorEquiv a σ β hβ g) = β g := by
    ext i j
    exact fixedActorEquiv_apply_coe a σ β hβ g i j
  have hv (i : Fin 3) :
      (FixedBy.subfield F σ).subtype (fixedVectorEquiv σ E A hA v i) = A v i :=
    fixedVectorEquiv_apply_coe σ E A hA v i
  have heq := action_map (FixedBy.subfield F σ).subtype
    (fixedActorEquiv a σ β hβ g) (fixedVectorEquiv σ E A hA v)
  rw [hg] at heq
  have hv' : (fun i => (FixedBy.subfield F σ).subtype (fixedVectorEquiv σ E A hA v i)) = A v :=
    funext hv
  rw [hv'] at heq
  ext i
  rw [fixedVectorEquiv_apply_coe, hw, hact]
  exact (congrFun heq i).symm

/-- The full-cover descent and the natural descent commute with their literal
coordinate projection; both use the same coefficient field and marking. -/
theorem fixed_cover_projection
    (σ : F ≃+* F) (E A : Space F ≃ₗ[ZMod 2] Space F)
    (e B : Plane F ≃ₗ[ZMod 2] Plane F)
    (hA : ∀ u, A (E u) = fun i => σ (A u i))
    (hB : ∀ v, B (e v) = fun i => σ (B v i))
    (hp : ∀ u, projection (A u) = B (projection u))
    (u : fixedVectors E) (v : fixedVectors e)
    (hv : (v : Plane F) = projection (u : Space F)) :
    projection (F := FixedBy.subfield F σ) (fixedVectorEquiv σ E A hA u) = fixedVectorEquiv σ e B hB v := by
  ext i
  have hi := congrFun (hp u) i
  rw [fixedVectorEquiv_apply_coe, hv]
  fin_cases i <;> simpa [projection_apply, fixedVectorEquiv_apply_coe] using hi
/-- Literal fixed actors preserve the literal fixed full cover. -/
theorem fixed_action_mem_of_intertwines
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (he : ∀ g u, E (action g u) = action (a g) (E u))
    (g : a.fixedSubgroup) (v : fixedVectors E) :
    action (g : SL F) (v : Space F) ∈ fixedVectors E := by
  change E (action (g : SL F) (v : Space F)) = action (g : SL F) (v : Space F)
  rw [he, (show E (v : Space F) = v from v.property),
    (MulAut.mem_fixedSubgroup _ _).mp g.property]

/-- The fixed full cover of the original outer involution is the full
orthogonal cover over its fixed field, equivariantly for the same fixed actors. -/
theorem outer_involution_fixed_cover
    (n : ℕ) (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (a : MulAut (SL F)) (E : Space F ≃ₗ[ZMod 2] Space F)
    (hinv : Function.Involutive E)
    (he : ∀ g u, E (action g u) = action (a g) (E u))
    (ha : a ^ 2 = 1) (houter : ¬ ∃ g, a = MulAut.conj g) :
    ∃ σ : F ≃+* F, σ ≠ RingEquiv.refl F ∧ Function.Involutive σ ∧
      ∃ eActor : a.fixedSubgroup ≃* SL (FixedBy.subfield F σ),
      ∃ eV : fixedVectors E ≃+ Space (FixedBy.subfield F σ),
        ∀ (g : a.fixedSubgroup) (v : fixedVectors E),
          eV ⟨action (g : SL F) (v : Space F),
            fixed_action_mem_of_intertwines a E he g v⟩ = action (eActor g) (eV v) := by
  obtain ⟨σ, hne, hs, β, A, e, B, hact, hβ, hAE, _, _, _, _, _⟩ :=
    outer_involution_full_alignment n hn hF a E hinv he ha houter
  refine ⟨σ, hne, hs, fixedActorEquiv a σ β hβ,
    fixedVectorEquiv σ E A hAE, ?_⟩
  intro g v
  exact fixed_cover_equivariance a σ β E A hβ hAE hact g v
    ⟨action (g : SL F) (v : Space F), fixed_action_mem_of_intertwines a E he g v⟩ rfl

end Representation.SL2OrthogonalCover.FixedField
