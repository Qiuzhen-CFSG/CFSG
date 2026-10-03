module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Tactic.Choose

/-!
# Fourth roots in involutory cosets of an abelian subgroup

Let `D` be normal, abelian and self-centralizing, and let `C = D ⊔ B`, where
`B` is elementary abelian of exponent two. If `A` is the conjugation image of
`B` on `D`, fourth roots in `C` correspond to the fibers of
`(a, d) ↦ (d * a d) ^ 2` on `A × D`.

Choose one representative in `B` of each `a : A`. Conjugation has kernel `D`,
so multiplication by these representatives gives unique coset coordinates.
Their squares are one, giving `(d * b) ^ 4 = (d * a d) ^ 2`. The choices are
only a transversal; no splitting of the extension is assumed.

Source: the elementary coset-counting argument for the abelian-base reduction
in Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386.
-/

namespace Subgroup

/-- Fourth roots in an elementary abelian supplement correspond to squared
norm fibers for its conjugation action on the self-centralizing abelian base.
The equivalence is noncanonical because it chooses coset representatives. -/
public noncomputable def fourthRootEquivNormFiber
    {P : Type*} [Group P]
    (D B C : Subgroup P) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hself : centralizer (D : Set P) ≤ D) (hDC : D ≤ C) (hcover : C = D ⊔ B)
    (x : D) :
    {t : C // t ^ 4 = (⟨(x : P), hDC x.property⟩ : C)} ≃
      {t : ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range × D //
        (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = x} := by
  classical
  let f : P →* MulAut D := MulAut.conjNormal
  let A := (f.comp B.subtype).range
  have hd (d : P) (hd : d ∈ D) : f d = 1 := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change d * (z : P) * d⁻¹ = z
    rw [(D.le_centralizer hd z z.property).symm, mul_inv_cancel_right]
  have hk (g : P) (hg : f g = 1) : g ∈ D := by
    apply hself
    intro d hd
    have hh := congrArg (fun a : MulAut D => (a ⟨d, hd⟩ : P)) hg
    change g * d * g⁻¹ = d at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hex (a : A) : ∃ b : B, f (b : P) = (a : MulAut D) := a.property
  choose r hr using hex
  have hBC : B ≤ C := hcover ▸ le_sup_right
  let F : A × D → C := fun t =>
    ⟨(t.2 : P) * (r t.1 : P), C.mul_mem (hDC t.2.property) (hBC (r t.1).property)⟩
  have hF (t : A × D) : f (F t : P) = (t.1 : MulAut D) := by
    change f ((t.2 : P) * (r t.1 : P)) = _
    rw [map_mul, hd _ t.2.property, one_mul, hr]
  have hbij : Function.Bijective F := by
    constructor
    · intro t u heq
      have ha : t.1 = u.1 := Subtype.ext (by
        simpa only [hF] using congrArg (fun c : C => f (c : P)) heq)
      apply Prod.ext ha
      apply Subtype.ext
      have heq' := congrArg (fun c : C => (c : P)) heq
      change (t.2 : P) * (r t.1 : P) = (u.2 : P) * (r u.1 : P) at heq'
      rw [ha] at heq'
      exact mul_right_cancel heq'
    · intro c
      have hc : (c : P) ∈ D ⊔ B := hcover ▸ c.property
      obtain ⟨d, hd', b, hb, hdb⟩ := mem_sup_of_normal_left.mp hc
      let a : A := ⟨f b, ⟨⟨b, hb⟩, rfl⟩⟩
      have hca : f (c : P) = (a : MulAut D) := by
        rw [← hdb, map_mul, hd _ hd', one_mul]
      have hz : (c : P) * (r a : P)⁻¹ ∈ D := hk _ (by
        rw [map_mul, map_inv, hca, hr, mul_inv_cancel])
      refine ⟨(a, ⟨(c : P) * (r a : P)⁻¹, hz⟩), ?_⟩
      apply Subtype.ext
      exact inv_mul_cancel_right (c : P) (r a : P)
  have hpow (t : A × D) :
      (F t : P) ^ 4 = (((t.2 * ((t.1 : MulAut D) t.2)) ^ 2 : D) : P) := by
    have hr2 : (r t.1 : P) ^ 2 = 1 :=
      elemPow_eq_one_of_isElementaryAbelian _ (r t.1).property
    have hri : (r t.1 : P)⁻¹ = (r t.1 : P) :=
      inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hr2)
    have hact : (((t.1 : MulAut D) t.2 : D) : P) =
        (r t.1 : P) * (t.2 : P) * (r t.1 : P) := by
      rw [← hr t.1]
      change (r t.1 : P) * (t.2 : P) * (r t.1 : P)⁻¹ = _
      rw [hri]
    have hsq : (F t : P) ^ 2 = ((t.2 * ((t.1 : MulAut D) t.2) : D) : P) := by
      change ((t.2 : P) * (r t.1 : P)) ^ 2 = (t.2 : P) * _
      rw [hact, pow_two]
      simp only [mul_assoc]
    calc
      (F t : P) ^ 4 = ((F t : P) ^ 2) ^ 2 := by rw [← pow_mul]
      _ = _ := by rw [hsq]; rfl
  let e : A × D ≃ C := Equiv.ofBijective F hbij
  exact (e.subtypeEquiv (p := fun t => (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = x)
    (q := fun c => c ^ 4 = (⟨(x : P), hDC x.property⟩ : C)) (fun t => by
      change _ ↔ F t ^ 4 = _
      rw [Subtype.ext_iff, Subtype.ext_iff]
      change _ ↔ (F t : P) ^ 4 = (x : P)
      rw [hpow])).symm

/-- Count fourth roots using the squared norm fibers of the conjugation image.
No restriction on the structure of the abelian base or the image order is needed. -/
public theorem card_fourth_roots_eq_norm_fibers
    {P : Type*} [Group P] [Finite P]
    (D B C : Subgroup P) [D.Normal] [IsMulCommutative D] [IsElementaryAbelian 2 B]
    (hself : centralizer (D : Set P) ≤ D) (hDC : D ≤ C) (hcover : C = D ⊔ B)
    (x : D) :
    Nat.card {t : C // t ^ 4 = (⟨(x : P), hDC x.property⟩ : C)} =
      Nat.card {t : ((MulAut.conjNormal : P →* MulAut D).comp B.subtype).range × D //
        (t.2 * ((t.1 : MulAut D) t.2)) ^ 2 = x} :=
  Nat.card_congr (fourthRootEquivNormFiber D B C hself hDC hcover x)

end Subgroup
