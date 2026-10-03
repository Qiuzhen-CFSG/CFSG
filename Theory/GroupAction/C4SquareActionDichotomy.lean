module

public import Theory.GroupAction.C4SquareActionDichotomySetup
public import Theory.GroupAction.C4SquareActionTransport
public import Theory.GroupAction.C4SquareActionDichotomyCertificate
public import Theory.GroupAction.C4SquareActionDichotomyEncoding

/-!
# The C₄-square action dichotomy

Nested automorphism subgroups of orders four and eight, whose order-four
subgroup fixes all involutions and whose nonidentity elements each invert
an element of order four, admit either a Hall–Janko or a split-inversion
action frame. Encode the subgroups on the explicit C₄-square, apply the
kernel-checked finite coordinate certificate, and reconstruct the frame.
Conjugating by an isomorphism preserves the subgroup orders, the pointwise
involution-fixing kernel, and the existence of an inverted element of order
four. Thus the dichotomy on the coordinate model applies to every
isomorphic group, with the original subgroups and public action interfaces.

Source: Janko–Thompson, Math. Z. 113 (1970), Theorem 1.3(a), printed p.386;
MacWilliams, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

namespace C4SquareExtension

/-- The finite coordinate calculation gives one of the two action frames. -/
public theorem action_dichotomy_model (H K : Subgroup (MulAut Model))
    (hHK : H ≤ K) (hH : Nat.card H = 4) (hK : Nat.card K = 8)
    (hfix : ∀ α ∈ K, α ∈ H ↔ ∀ a : Model, a ^ 2 = 1 → α a = a)
    (hinv : ∀ α ∈ H, α ≠ 1 → ∃ a : Model, α a = a⁻¹ ∧ a ^ 2 ≠ 1) :
    Nonempty (HallJankoAutActions H K) ∨ Nonempty (SplitInversionAutActions H K) := by
  obtain ⟨d⟩ := ActionDichotomy.exists_encodedActionPair H K hHK hH hK hfix hinv
  exact ActionDichotomy.actions_of_witness hHK d
    (ActionDichotomy.certificate d.m d.n (d.t ActionDichotomy.e₁, d.t ActionDichotomy.e₂)
      d.valid)

/-- Transport the finite-model action dichotomy to an arbitrary C₄-square. -/
public theorem action_dichotomy_of_model
    (hmodel_case : ∀ H K : Subgroup (MulAut Model), H ≤ K →
      Nat.card H = 4 → Nat.card K = 8 →
      (∀ α ∈ K, α ∈ H ↔ ∀ a : Model, a ^ 2 = 1 → α a = a) →
      (∀ α ∈ H, α ≠ 1 → ∃ a : Model, α a = a⁻¹ ∧ a ^ 2 ≠ 1) →
      Nonempty (HallJankoAutActions H K) ∨ Nonempty (SplitInversionAutActions H K))
    {A : Type*} [Group A] (hmodel : Nonempty (A ≃* Model))
    (H K : Subgroup (MulAut A)) (hHK : H ≤ K)
    (hH : Nat.card H = 4) (hK : Nat.card K = 8)
    (hfix : ∀ α ∈ K, α ∈ H ↔ ∀ a : A, a ^ 2 = 1 → α a = a)
    (hinv : ∀ α ∈ H, α ≠ 1 → ∃ a : A, α a = a⁻¹ ∧ a ^ 2 ≠ 1) :
    Nonempty (HallJankoAutActions H K) ∨ Nonempty (SplitInversionAutActions H K) := by
  obtain ⟨e⟩ := hmodel
  let F := MulAut.congr e
  let H' := H.map F.toMonoidHom
  let K' := K.map F.toMonoidHom
  have hHK' : H' ≤ K' := Subgroup.map_mono hHK
  have hH' : Nat.card H' = 4 := by
    rw [Subgroup.card_map_of_injective F.injective]
    exact hH
  have hK' : Nat.card K' = 8 := by
    rw [Subgroup.card_map_of_injective F.injective]
    exact hK
  have happ (f : MulAut A) (a : A) : F f (e a) = e (f a) := by
    simp [F, MulAut.congr]
  have hfix' : ∀ α ∈ K', α ∈ H' ↔ ∀ a : Model, a ^ 2 = 1 → α a = a := by
    rintro α ⟨β,hβ,rfl⟩
    change F β ∈ H.map F.toMonoidHom ↔ _
    rw [Subgroup.mem_map_equiv, F.symm_apply_apply, hfix β hβ]
    constructor
    · intro h a ha
      obtain ⟨b,rfl⟩ := e.surjective a
      change F β (e b) = e b
      rw [happ, h b]
      apply e.injective
      simpa only [map_pow, map_one] using ha
    · intro h a ha
      apply e.injective
      rw [← happ]
      apply h
      rw [← map_pow, ha, map_one]
  have hinv' : ∀ α ∈ H', α ≠ 1 → ∃ a : Model, α a = a⁻¹ ∧ a ^ 2 ≠ 1 := by
    rintro α ⟨β,hβ,rfl⟩ hne
    have hβne : β ≠ 1 := by
      intro heq
      apply hne
      change F β = 1
      rw [heq, map_one]
    obtain ⟨a,ha,ha2⟩ := hinv β hβ hβne
    refine ⟨e a, ?_, ?_⟩
    · change F β (e a) = _
      rw [happ, ha, map_inv]
    · intro heq
      apply ha2
      apply e.injective
      simpa only [map_pow, map_one] using heq
  rcases hmodel_case H' K' hHK' hH' hK' hfix' hinv' with hs | hs
  · obtain ⟨s⟩ := hs
    exact Or.inl ⟨HallJankoAutActions.of_map e H K s⟩
  · obtain ⟨s⟩ := hs
    exact Or.inr ⟨SplitInversionAutActions.of_map e H K s⟩

/-- Every C₄-square with the specified nested automorphism subgroups admits
either a Hall–Janko action frame or a split-inversion action frame. -/
public theorem action_dichotomy {A : Type*} [Group A]
    (hmodel : Nonempty (A ≃* Model)) (H K : Subgroup (MulAut A))
    (hHK : H ≤ K) (hH : Nat.card H = 4) (hK : Nat.card K = 8)
    (hfix : ∀ α ∈ K, α ∈ H ↔ ∀ a : A, a ^ 2 = 1 → α a = a)
    (hinv : ∀ α ∈ H, α ≠ 1 → ∃ a : A, α a = a⁻¹ ∧ a ^ 2 ≠ 1) :
    Nonempty (HallJankoAutActions H K) ∨ Nonempty (SplitInversionAutActions H K) :=
  action_dichotomy_of_model action_dichotomy_model hmodel H K hHK hH hK hfix hinv

end C4SquareExtension
