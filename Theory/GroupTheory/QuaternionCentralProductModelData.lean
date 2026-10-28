module

public import Theory.GroupTheory.QuaternionCentralProductQuotient
public import Theory.GroupTheory.QuaternionCentralProductTransport

/-!
# The canonical factors of the quaternion central-product model

The two coordinate embeddings of Q₈ survive the diagonal quotient
(Q₈ × Q₈)/⟨(-1,-1)⟩. Their images commute, generate the quotient and
intersect in order two. This constructs intrinsic factor data from an
isomorphism with the literal model, preserving the meaning of Q₈² used
in Aschbacher–Smith, G.2.4(8) and13.5.15(5), pp.334–335,920.
-/

public section
namespace QuaternionCentralProduct
open Subgroup

private instance : DecidablePred (fun x : Pair => x ∈ diagonalCenter) :=
  fun x => inferInstanceAs (Decidable (x = 1 ∨ x = diagonalInvolution))

private def leftEmbedding : QuaternionGroup 2 →* Model :=
  (QuotientGroup.mk' diagonalCenter).comp (MonoidHom.inl _ _)

private def rightEmbedding : QuaternionGroup 2 →* Model :=
  (QuotientGroup.mk' diagonalCenter).comp (MonoidHom.inr _ _)

private theorem left_injective : Function.Injective leftEmbedding := by
  apply (injective_iff_map_eq_one leftEmbedding).mpr
  intro x hx
  have h : (x, (1 : QuaternionGroup 2)) ∈ diagonalCenter :=
    (QuotientGroup.eq_one_iff _).mp hx
  exact (by decide +kernel : ∀ x : QuaternionGroup 2,
    (x, 1) ∈ diagonalCenter → x = 1) x h

private theorem right_injective : Function.Injective rightEmbedding := by
  apply (injective_iff_map_eq_one rightEmbedding).mpr
  intro x hx
  have h : ((1 : QuaternionGroup 2), x) ∈ diagonalCenter :=
    (QuotientGroup.eq_one_iff _).mp hx
  exact (by decide +kernel : ∀ x : QuaternionGroup 2,
    (1, x) ∈ diagonalCenter → x = 1) x h

private theorem factors_commute : ∀ x ∈ leftEmbedding.range,
    ∀ y ∈ rightEmbedding.range, x * y = y * x := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  change QuotientGroup.mk' diagonalCenter (x, 1) * QuotientGroup.mk' diagonalCenter (1, y) =
    QuotientGroup.mk' diagonalCenter (1, y) * QuotientGroup.mk' diagonalCenter (x, 1)
  rw [← map_mul, ← map_mul]
  simp only [Prod.mk_mul_mk, mul_one, one_mul]

private theorem factors_span : leftEmbedding.range ⊔ rightEmbedding.range = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨⟨a, b⟩, rfl⟩ := QuotientGroup.mk'_surjective diagonalCenter x
  have he : QuotientGroup.mk' diagonalCenter (a,b) = leftEmbedding a * rightEmbedding b := by
    change _ = QuotientGroup.mk' diagonalCenter (a,1) * QuotientGroup.mk' diagonalCenter (1,b)
    rw [← map_mul]
    simp
  rw [he]
  exact mul_mem (mem_sup_left ⟨a,rfl⟩) (mem_sup_right ⟨b,rfl⟩)

/-- The literal diagonal quotient has order32. -/
theorem card_model : Nat.card Model = 32 := by
  have hdiag : Nat.card diagonalCenter = 2 := by
    rw [diagonalCenter_eq_zpowers, Nat.card_zpowers]
    apply (orderOf_eq_prime_iff).mpr
    constructor
    · decide +kernel
    · decide +kernel
  have hpair : Nat.card Pair = 64 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have h := diagonalCenter.index_mul_card
  rw [index_eq_card, hdiag, hpair] at h
  change Nat.card Model * 2 = 64 at h
  omega

/-- The two concrete factor images give an intrinsic quaternion presentation. -/
noncomputable def modelData : QuaternionCentralProductData Model where
  left := leftEmbedding.range
  right := rightEmbedding.range
  left_model := ⟨(MonoidHom.ofInjective left_injective).symm⟩
  right_model := ⟨(MonoidHom.ofInjective right_injective).symm⟩
  intersection_card := by
    have hc : Nat.card leftEmbedding.range = 8 := by
      rw [Nat.card_congr (MonoidHom.ofInjective left_injective).symm.toEquiv,
        Nat.card_eq_fintype_card, QuaternionGroup.card]
    have hd : Nat.card rightEmbedding.range = 8 := by
      rw [Nat.card_congr (MonoidHom.ofInjective right_injective).symm.toEquiv,
        Nat.card_eq_fintype_card, QuaternionGroup.card]
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes
      leftEmbedding.range rightEmbedding.range
      ((show rightEmbedding.range ≤ centralizer (leftEmbedding.range : Set Model) from
        fun b hb a ha => factors_commute a ha b hb).trans (centralizer_le_normalizer _))
    rw [hc, hd, factors_span, Nat.card_congr topEquiv.toEquiv, card_model] at h
    omega
  commute := factors_commute
  span := factors_span

/-- An isomorphism with Q₈∘Q₈ supplies both actual embedded quaternion factors. -/
noncomputable def dataOfEquiv {Q : Type*} [Group Q] (e : Q ≃* Model) :
    QuaternionCentralProductData Q := modelData.map e.symm

end QuaternionCentralProduct
end
