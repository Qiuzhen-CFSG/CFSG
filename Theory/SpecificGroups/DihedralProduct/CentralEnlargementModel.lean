module
public import Theory.SpecificGroups.DihedralProduct.CanonicalFactors
public import Theory.ElementaryAbelian.Basic
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Models and transport for the four dihedral central enlargements

Each canonical enlargement has one unrestricted dihedral coordinate and
three central coordinates. Projection therefore identifies it with D₈ times
an elementary abelian group of order eight. Transport through a prescribed
isomorphism preserves this literal subgroup family and its automorphism action.

Source: Aschbacher–Smith, 10.2.1, printed p.743, the family Γ.
-/

@[expose] public noncomputable section
open Subgroup
namespace DihedralProductCanonical
abbrev Remainder (i : Fin 4) := {j : Fin 4 // j ≠ i} → center D

def gammaEquivDihedralRemainder (i : Fin 4) : gamma i ≃* D × Remainder i where
  toFun x := (x.val i, fun j => ⟨x.val j, x.property j j.property⟩)
  invFun p := ⟨fun j => if h : j = i then p.1 else (p.2 ⟨j,h⟩).val, by
    intro j hji
    simp only [dif_neg hji]
    exact (p.2 ⟨j,hji⟩).property⟩
  left_inv x := by
    apply Subtype.ext
    funext j
    by_cases hji : j = i <;> simp [hji]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j
      apply Subtype.ext
      simp [j.property]
  map_mul' x y := rfl

theorem center_card : Nat.card (center D) = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

instance center_elementary : IsElementaryAbelian 2 (center D) where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Subtype.ext
    exact (by decide +kernel : ∀ x : D, x ∈ center D → x^2=1) x.val x.property)

theorem remainder_card (i : Fin 4) : Nat.card (Remainder i) = 8 := by
  rw [Nat.card_fun,center_card]
  have hi : Nat.card {j : Fin 4 // j ≠ i} = 3 := by
    rw [Nat.card_eq_fintype_card]
    simp
  rw [hi]
  norm_num

instance remainder_elementary (i : Fin 4) : IsElementaryAbelian 2 (Remainder i) where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    funext j
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center D)) (x j))

variable {H : Type*} [Group H]

/-- The canonical family in the original group, through the supplied marking. -/
def transportedGamma (e : H ≃* (Fin 4 → D)) (i : Fin 4) : Subgroup H :=
  (gamma i).map e.symm.toMonoidHom

/-- The literal central enlargement is dihedral times an elementary group of order eight. -/
def transportedGammaEquiv (e : H ≃* (Fin 4 → D)) (i : Fin 4) :
    transportedGamma e i ≃* D × Remainder i :=
  ((gamma i).equivMapOfInjective e.symm.toMonoidHom e.symm.injective).symm.trans
    (gammaEquivDihedralRemainder i)

theorem transportedGamma_injective (e : H ≃* (Fin 4 → D)) :
    Function.Injective (transportedGamma e) := by
  intro i j h
  exact gamma_injective (map_injective e.symm.injective h)

/-- Automorphisms of the original group act on its four prescribed enlargements. -/
def transportedFactorAction (e : H ≃* (Fin 4 → D)) : MulAut H →* Equiv.Perm (Fin 4) :=
  factorAction.comp (MulAut.congr e).toMonoidHom

theorem map_transportedGamma (e : H ≃* (Fin 4 → D)) (f : MulAut H) (i : Fin 4) :
    (transportedGamma e i).map f.toMonoidHom =
      transportedGamma e (transportedFactorAction e f i) := by
  change ((gamma i).map e.symm.toMonoidHom).map f.toMonoidHom = _
  rw [map_map]
  have hcomp : f.toMonoidHom.comp e.symm.toMonoidHom =
      e.symm.toMonoidHom.comp ((MulAut.congr e) f).toMonoidHom := by
    ext x
    change f (e.symm x) = e.symm (e (f (e.symm x)))
    rw [e.symm_apply_apply]
  rw [hcomp, ←map_map, map_gamma_factorAction]
  rfl

/-- Coordinates connecting the assembled product with the canonical four-factor model. -/
def fourProductEquiv : ((D × D) × (D × D)) ≃* (Fin 4 → D) where
  toFun x := ![x.1.1, x.1.2, x.2.1, x.2.2]
  invFun x := ((x 0, x 1), (x 2, x 3))
  left_inv _ := rfl
  right_inv x := by
    funext i
    fin_cases i <;> rfl
  map_mul' x y := by
    funext i
    fin_cases i <;> rfl

end DihedralProductCanonical
