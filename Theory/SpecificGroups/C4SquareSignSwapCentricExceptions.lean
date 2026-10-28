module

public import Theory.SpecificGroups.C4SquareSignSwapCentricData
public import Theory.ElementaryAbelian.Basic

/-!
# Exceptional candidates in the sign-and-swap group

Five candidate subgroups are elementary abelian of order eight. Three are
central products of actual cyclic-four and quaternion-eight subgroups, and
two are the distinguished index-two cores. The central products are witnessed
by explicit embeddings, with intersection and commutation checked in the
coordinate model. This module establishes the positive cases only; it does
not assert that the candidate list is complete or exclude automorphisms of
other candidates.

Source: the intrinsic order-64 model for Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

namespace C4SquareSignSwap

/-- The candidate indices covered by the four exceptional alternatives. -/
@[expose] public def centricExceptionalIndex (i : Fin 32) : Prop :=
  i = 11 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 26 ∨ i = 28 ∨
    i = 29 ∨ i = 30 ∨ i = 31

public instance (i : Fin 32) : Decidable (centricExceptionalIndex i) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- The elementary-abelian entries have their asserted intrinsic structure. -/
public theorem centricCandidate_elementary (i : Fin 32)
    (hi : i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 29 ∨ i = 30) :
    IsElementaryAbelian 2 (centricCandidate i) ∧ Nat.card (centricCandidate i) = 8 := by
  have hcomm : ∀ i : Fin 32, (i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 29 ∨ i = 30) →
      ∀ a b : Model, a ∈ centricCandidate i → b ∈ centricCandidate i → a * b = b * a := by
    decide +kernel
  have hpow : ∀ i : Fin 32, (i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 29 ∨ i = 30) →
      ∀ a : Model, a ∈ centricCandidate i → a ^ 2 = 1 := by decide +kernel
  have hcard : ∀ i : Fin 32, (i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 29 ∨ i = 30) →
      Fintype.card (centricCandidate i) = 8 := by decide +kernel
  refine ⟨{ toIsMulCommutative := IsMulCommutative.of_comm
              (fun a b => Subtype.ext (hcomm i hi a b a.property b.property))
            exponent_dvd_p := ?_ }, ?_⟩
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    exact Subtype.ext (hpow i hi a a.property)
  · rw [Nat.card_eq_fintype_card]
    exact hcard i hi

public theorem centricCandidate_eleven : centricCandidate 11 = inverterCore := by
  ext g
  exact (by decide +kernel : ∀ g : Model, g ∈ centricCandidate 11 ↔ g ∈ inverterCore) g

public theorem centricCandidate_thirty_one : centricCandidate 31 = extraspecialCore := by
  ext g
  exact (by decide +kernel : ∀ g : Model, g ∈ centricCandidate 31 ↔ g ∈ extraspecialCore) g

private def centralProductIndex : Fin 3 → Fin 32 := ![17, 26, 28]
private def centralCode : Fin 3 → ℕ := ![7, 34, 50]
private def quaternionCodeA : Fin 3 → ℕ := ![5, 5, 7]
private def quaternionCodeX : Fin 3 → ℕ := ![50, 50, 34]

private def cyclicEmbedding (j : Fin 3) : C4 →* Model where
  toFun x := coordinateElement (centralCode j) ^ x.toAdd.val
  map_one' := rfl
  map_mul' := by
    exact (by decide +kernel : ∀ j : Fin 3, ∀ x y : C4,
      coordinateElement (centralCode j) ^ (x * y).toAdd.val =
      coordinateElement (centralCode j) ^ x.toAdd.val *
        coordinateElement (centralCode j) ^ y.toAdd.val) j

private def quaternionEmbedding (j : Fin 3) : QuaternionGroup 2 →* Model where
  toFun q := match q with
    | .a k => coordinateElement (quaternionCodeA j) ^ k.val
    | .xa k => coordinateElement (quaternionCodeX j) *
        coordinateElement (quaternionCodeA j) ^ k.val
  map_one' := rfl
  map_mul' := by
    revert j
    decide +kernel

private instance (j : Fin 3) : DecidablePred (· ∈ (cyclicEmbedding j).range) :=
  fun g => inferInstanceAs (Decidable (∃ x, cyclicEmbedding j x = g))
private instance (j : Fin 3) : DecidablePred (· ∈ (quaternionEmbedding j).range) :=
  fun g => inferInstanceAs (Decidable (∃ x, quaternionEmbedding j x = g))
private instance (j : Fin 3) :
    DecidablePred (· ∈ (cyclicEmbedding j).range ⊓ (quaternionEmbedding j).range) :=
  fun g => inferInstanceAs (Decidable
    (g ∈ (cyclicEmbedding j).range ∧ g ∈ (quaternionEmbedding j).range))

set_option maxRecDepth 10000 in
private theorem centralProduct_join (j : Fin 3) :
    centricCandidate (centralProductIndex j) =
      (cyclicEmbedding j).range ⊔ (quaternionEmbedding j).range := by
  apply le_antisymm
  · have h : ∀ j : Fin 3, ∀ g : Model, g ∈ centricCandidate (centralProductIndex j) →
        ∃ a : C4, ∃ b : QuaternionGroup 2, cyclicEmbedding j a * quaternionEmbedding j b = g := by
      decide +kernel
    intro g hg
    obtain ⟨a, b, rfl⟩ := h j g hg
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨a, rfl⟩)
      (Subgroup.mem_sup_right ⟨b, rfl⟩)
  · apply sup_le
    · rintro g ⟨a, rfl⟩
      exact (by decide +kernel : ∀ j : Fin 3, ∀ a : C4,
        cyclicEmbedding j a ∈ centricCandidate (centralProductIndex j)) j a
    · rintro g ⟨a, rfl⟩
      exact (by decide +kernel : ∀ j : Fin 3, ∀ a : QuaternionGroup 2,
        quaternionEmbedding j a ∈ centricCandidate (centralProductIndex j)) j a

set_option maxRecDepth 10000 in
private theorem centralProduct_data (j : Fin 3) :
    ∃ B C : Subgroup Model,
      Nonempty (B ≃* Multiplicative (ZMod 4)) ∧ Nonempty (C ≃* QuaternionGroup 2) ∧
      centricCandidate (centralProductIndex j) = B ⊔ C ∧ Nat.card (B ⊓ C : Subgroup Model) = 2 ∧
      (∀ b : Model, b ∈ B → ∀ c : Model, c ∈ C → b * c = c * b) ∧
      B ⊓ C ≤ (Subgroup.center (centricCandidate (centralProductIndex j))).map
        (centricCandidate (centralProductIndex j)).subtype := by
  have hc : ∀ j : Fin 3, Function.Injective (cyclicEmbedding j) := by decide +kernel
  have hq : ∀ j : Fin 3, Function.Injective (quaternionEmbedding j) := by decide +kernel
  refine ⟨(cyclicEmbedding j).range, (quaternionEmbedding j).range,
    ⟨(MonoidHom.ofInjective (hc j)).symm⟩, ⟨(MonoidHom.ofInjective (hq j)).symm⟩,
    centralProduct_join j, ?_, ?_, ?_⟩
  · have h : ∀ j : Fin 3,
        Fintype.card ((cyclicEmbedding j).range ⊓ (quaternionEmbedding j).range : Subgroup Model) = 2 := by
      decide +kernel
    rw [Nat.card_eq_fintype_card]
    exact h j
  · rintro b ⟨x, rfl⟩ c ⟨y, rfl⟩
    exact (by decide +kernel : ∀ j : Fin 3, ∀ x : C4, ∀ y : QuaternionGroup 2,
      cyclicEmbedding j x * quaternionEmbedding j y =
        quaternionEmbedding j y * cyclicEmbedding j x) j x y
  · intro z hz
    have hzX : z ∈ centricCandidate (centralProductIndex j) := by
      rw [centralProduct_join]
      exact Subgroup.mem_sup_left hz.1
    refine ⟨⟨z, hzX⟩, Subgroup.mem_center_iff.mpr ?_, rfl⟩
    intro g
    apply Subtype.ext
    exact (by decide +kernel : ∀ j : Fin 3, ∀ z : Model,
      z ∈ (cyclicEmbedding j).range → z ∈ (quaternionEmbedding j).range →
      ∀ g : Model, g ∈ centricCandidate (centralProductIndex j) → g * z = z * g)
        j z hz.1 hz.2 g g.property

/-- Each central-product entry retains its two actual factors in the model. -/
public theorem centricCandidate_centralProduct (i : Fin 32)
    (hi : i = 17 ∨ i = 26 ∨ i = 28) :
    ∃ B C : Subgroup Model,
      Nonempty (B ≃* Multiplicative (ZMod 4)) ∧ Nonempty (C ≃* QuaternionGroup 2) ∧
      centricCandidate i = B ⊔ C ∧ Nat.card (B ⊓ C : Subgroup Model) = 2 ∧
      (∀ b : Model, b ∈ B → ∀ c : Model, c ∈ C → b * c = c * b) ∧
      B ⊓ C ≤ (Subgroup.center (centricCandidate i)).map (centricCandidate i).subtype := by
  rcases hi with rfl | rfl | rfl
  · exact centralProduct_data 0
  · exact centralProduct_data 1
  · exact centralProduct_data 2

/-- All designated exceptional candidates satisfy the intrinsic alternatives. -/
public theorem centricCandidate_exceptional_cases (i : Fin 32)
    (hi : centricExceptionalIndex i) :
    (IsElementaryAbelian 2 (centricCandidate i) ∧ Nat.card (centricCandidate i) = 8) ∨
    (∃ B C : Subgroup Model,
      Nonempty (B ≃* Multiplicative (ZMod 4)) ∧ Nonempty (C ≃* QuaternionGroup 2) ∧
      centricCandidate i = B ⊔ C ∧ Nat.card (B ⊓ C : Subgroup Model) = 2 ∧
      (∀ b : Model, b ∈ B → ∀ c : Model, c ∈ C → b * c = c * b) ∧
      B ⊓ C ≤ (Subgroup.center (centricCandidate i)).map (centricCandidate i).subtype) ∨
    centricCandidate i = inverterCore ∨ centricCandidate i = extraspecialCore := by
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl centricCandidate_eleven))
  · exact Or.inr (Or.inl (centricCandidate_centralProduct 17 (by simp)))
  · exact Or.inl (centricCandidate_elementary 18 (by simp))
  · exact Or.inl (centricCandidate_elementary 19 (by simp))
  · exact Or.inl (centricCandidate_elementary 20 (by simp))
  · exact Or.inr (Or.inl (centricCandidate_centralProduct 26 (by simp)))
  · exact Or.inr (Or.inl (centricCandidate_centralProduct 28 (by simp)))
  · exact Or.inl (centricCandidate_elementary 29 (by simp))
  · exact Or.inl (centricCandidate_elementary 30 (by simp))
  · exact Or.inr (Or.inr (Or.inr centricCandidate_thirty_one))

end C4SquareSignSwap
