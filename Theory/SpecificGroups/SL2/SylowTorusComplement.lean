module
public import Theory.SpecificGroups.SL2.SylowTorusKernel
public import Theory.GroupAction.Quotient
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Simultaneous diagonal straightening of a coprime field complement

In a diagonal-plus-field action, uniqueness of the diagonal factor turns
those factors into a multiplicative cocycle in the pair of unit groups.
Coprime averaging makes the cocycle a coboundary. Thus one diagonal change
of coordinates turns every actor into its actual coefficient action.
The theorem uses a whole acting group, not unrelated choices for its elements.

The original Hall application is `HallGeometry.PureField`, following the
proved coprime complement construction. Source: the field-complement step
of Aschbacher--Smith 10.2.3, printed p.745.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
open BenderSuzuki.ZD.Linear
namespace Matrix.SpecialLinearGroup

private theorem coprime_straightening {A U X : Type*}
    [Group A] [Finite A] [CommGroup U] [Finite U] [Group X]
    (β : A →* MulAut U) (j : U →* X) (hj : Function.Injective j)
    (s ρ : A →* X)
    (hcompat : ∀ a u, s a * j u = j (β a u) * s a)
    (hd : ∀ a, ∃ u, ρ a = j u * s a)
    (hc : Nat.Coprime (Nat.card A) (Nat.card U)) :
    ∃ u : U, ∀ a, ρ a = j u * s a * (j u)⁻¹ := by
  classical
  let δ : A → U := fun a => (hd a).choose
  have hδ (a : A) : ρ a = j (δ a) * s a := (hd a).choose_spec
  let : MulDistribMulAction A U := MulDistribMulAction.compHom U β
  have hco : IsCocycle₁ δ := by
    intro a b
    apply hj
    apply mul_right_cancel (b := s (a*b))
    calc
      j (δ (a*b)) * s (a*b) = ρ (a*b) := (hδ _).symm
      _ = (j (δ a) * s a) * (j (δ b) * s b) := by rw [map_mul,hδ,hδ]
      _ = j (δ a) * (s a * j (δ b)) * s b := by group
      _ = j (δ a) * (j (β a (δ b)) * s a) * s b := by rw [hcompat]
      _ = j (δ a * a • δ b) * s (a*b) := by
        rw [map_mul,map_mul]
        change j (δ a) * (j (β a (δ b)) * s a) * s b =
          j (δ a) * j (β a (δ b)) * (s a * s b)
        group
  obtain ⟨u,hu⟩ := exists_coboundary_of_cocycle_of_coprime_card δ hco hc
  refine ⟨u,fun a => ?_⟩
  have hh := hcompat a u
  rw [hδ,hu,mul_comm ((a • u)⁻¹),map_mul,map_inv]
  change j u * (j (β a u))⁻¹ * s a = j u * s a * (j u)⁻¹
  have he : (j (β a u))⁻¹ * s a = s a * (j u)⁻¹ := by
    apply (eq_mul_inv_iff_mul_eq).mpr
    rw [mul_assoc,hh,inv_mul_cancel_left]
  rw [mul_assoc,he,mul_assoc]

variable {F : Type*} [Field F] [CharP F 2]

/-- Entrywise field automorphisms on the two component factors. -/
def pairFieldAction : ((F ≃+* F) × (F ≃+* F)) →* MulAut (SL(2,F) × SL(2,F)) where
  toFun σ := (sl2FieldAut σ.1).prodCongr (sl2FieldAut σ.2)
  map_one' := by ext x <;> rfl
  map_mul' σ τ := by ext x <;> rfl

omit [CharP F 2] in
/-- Evaluation on the literal pair of component matrices. -/
theorem pairFieldAction_apply (σ : (F ≃+* F) × (F ≃+* F))
    (x : SL(2,F) × SL(2,F)) :
    pairFieldAction σ x = (sl2FieldAut σ.1 x.1,sl2FieldAut σ.2 x.2) := by rfl

private def pairUnitAction : ((F ≃+* F) × (F ≃+* F)) →* MulAut (Fˣ × Fˣ) where
  toFun σ := (Units.mapEquiv σ.1.toMulEquiv).prodCongr (Units.mapEquiv σ.2.toMulEquiv)
  map_one' := by ext x <;> rfl
  map_mul' σ τ := by ext x <;> rfl

omit [CharP F 2] in
private theorem field_diagonal_commutes (σ : (F ≃+* F) × (F ≃+* F))
    (u : Fˣ × Fˣ) :
    pairFieldAction σ * splitDiagonalPairAction u =
      splitDiagonalPairAction (pairUnitAction σ u) * pairFieldAction σ := by
  apply MulEquiv.ext
  intro x
  change pairFieldAction σ (splitDiagonalPairAction u x) =
    splitDiagonalPairAction (pairUnitAction σ u) (pairFieldAction σ x)
  rw [splitDiagonalPairAction_apply,splitDiagonalPairAction_apply,map_mul,map_mul,map_inv]
  have he : pairFieldAction σ (splitDiagonalHom u.1,splitDiagonalHom u.2) =
      (splitDiagonalHom ((pairUnitAction σ u).1),splitDiagonalHom ((pairUnitAction σ u).2)) := by
    apply Prod.ext
    · change sl2FieldAut σ.1 (splitDiagonalHom u.1) =
        splitDiagonalHom (Units.mapEquiv σ.1.toMulEquiv u.1)
      rw [splitDiagonalHom_apply,splitDiagonalHom_apply,sl2FieldAut_diagonal]
      rfl
    · change sl2FieldAut σ.2 (splitDiagonalHom u.2) =
        splitDiagonalHom (Units.mapEquiv σ.2.toMulEquiv u.2)
      rw [splitDiagonalHom_apply,splitDiagonalHom_apply,sl2FieldAut_diagonal]
      rfl
  rw [he]


/-- Coprime order removes all diagonal twists on a coefficient complement
by a single common diagonal change of coordinates. -/
theorem exists_pair_diagonal_field_straightening [Finite F]
    {A : Type*} [Group A] [Finite A]
    (ρ : A →* MulAut (SL(2,F) × SL(2,F)))
    (φ : A →* ((F ≃+* F) × (F ≃+* F)))
    (hd : ∀ b, ∃ d : Fˣ × Fˣ, ρ b =
      (MulAut.conj (splitDiagonalHom d.1) * sl2FieldAut (φ b).1).prodCongr
        (MulAut.conj (splitDiagonalHom d.2) * sl2FieldAut (φ b).2))
    (hc : Nat.Coprime (Nat.card A) (Nat.card Fˣ)) :
    ∃ u : Fˣ × Fˣ, ∀ a,
      ρ a = splitDiagonalPairAction u * pairFieldAction (φ a) *
        (splitDiagonalPairAction u)⁻¹ := by
  apply coprime_straightening (pairUnitAction.comp φ)
    splitDiagonalPairAction splitDiagonalPairAction_injective
    (pairFieldAction.comp φ) ρ (fun a u => field_diagonal_commutes (φ a) u)
  · intro a
    obtain ⟨d,hd⟩ := hd a
    refine ⟨d,hd.trans ?_⟩
    apply MulEquiv.ext
    intro x
    change _ = splitDiagonalPairAction d (pairFieldAction (φ a) x)
    rw [splitDiagonalPairAction_apply]
    rfl
  · rw [Nat.card_prod]
    exact hc.mul_right hc
end Matrix.SpecialLinearGroup
