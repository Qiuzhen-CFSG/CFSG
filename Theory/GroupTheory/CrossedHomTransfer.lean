module

public import Mathlib.GroupTheory.Index

/-!
# Transfer of crossed homomorphisms

For an action `ρ : G →* MulAut A` on an abelian group and a map `f : H → A`
satisfying `f (xy) = f x * ρ x (f y)`, take the product over the left cosets
of `H` of the values of `f` on the coset factors, conjugated by the chosen
representatives. Reindexing the product proves the same crossed law on `G`.

When `A` is an abelian normal subgroup of `G` contained in `H` and `f`
restricts to the identity on `A`, this product restricts to the power map
with exponent `[G : H]`. This is the averaging step in Gaschütz's splitting
theorem; no triviality of the action is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma A.1.39, printed p.31, citing Aschbacher (1986), 10.4 and 12.8.
-/

open MulAction
open scoped IsMulCommutative

namespace GroupTheory.CrossedHomTransfer
variable {G A : Type*} [Group G] [CommGroup A] (H : Subgroup G)

/-- The factor in `H` obtained by comparing chosen representatives of `q`
and `g⁻¹ • q`. -/
@[expose] public noncomputable def cosetFactor (g : G) (q : G ⧸ H) : H :=
  ⟨q.out⁻¹ * (g * (g⁻¹ • q).out), by
    apply QuotientGroup.leftRel_apply.mp
    apply Quotient.exact'
    rw [Quotient.out_eq']
    exact ((MulAction.Quotient.mk_smul_out H g (g⁻¹ • q)).trans
      (smul_inv_smul g q)).symm⟩

/-- The factors multiply after reindexing the second factor by `g⁻¹`. -/
public theorem cosetFactor_mul (g k : G) (q : G ⧸ H) :
    cosetFactor H (g * k) q = cosetFactor H g q * cosetFactor H k (g⁻¹ • q) := by
  apply Subtype.ext
  simp only [cosetFactor, Subgroup.coe_mul, mul_inv_rev, mul_smul]
  simp only [mul_assoc, mul_inv_cancel_left]

variable [Finite G] (ρ : G →* MulAut A) (f : H → A)

/-- The coset product transferring a crossed homomorphism from `H` to `G`. -/
@[expose] public noncomputable def transfer (g : G) : A :=
  letI := Fintype.ofFinite (G ⧸ H)
  ∏ q : G ⧸ H, ρ q.out (f (cosetFactor H g q))

/-- Transfer preserves the crossed multiplication law for the given action. -/
public theorem transfer_mul
    (hf : ∀ x y : H, f (x * y) = f x * ρ x (f y)) (g k : G) :
    transfer H ρ f (g * k) = transfer H ρ f g * ρ g (transfer H ρ f k) := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  have hc (q : G ⧸ H) :
      ρ q.out (ρ (cosetFactor H g q : G) (f (cosetFactor H k (g⁻¹ • q)))) =
      ρ g (ρ (g⁻¹ • q).out (f (cosetFactor H k (g⁻¹ • q)))) := by
    simp only [← MulAut.mul_apply, ← map_mul]
    congr 2
    simp [cosetFactor]
  unfold transfer
  simp_rw [cosetFactor_mul, hf, map_mul, hc]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← map_prod]
  congr 1
  exact (Fintype.prod_equiv (MulAction.toPerm g⁻¹) _ _ (fun _ => rfl))

end GroupTheory.CrossedHomTransfer

namespace GroupTheory.CrossedHomTransfer
variable {G : Type*} [Group G] (V H : Subgroup G) [V.Normal]

private theorem normal_smul_coset_eq (hVH : V ≤ H) (v : V) (q : G ⧸ H) :
    (v : G) • q = q := by
  refine Quotient.inductionOn' q (fun x => ?_)
  change ((↑v * x : G) : G ⧸ H) = (x : G ⧸ H)
  apply QuotientGroup.eq.mpr
  apply hVH
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using
    ((inferInstance : V.Normal).conj_mem (v : G)⁻¹ (V.inv_mem v.property) x⁻¹)

end GroupTheory.CrossedHomTransfer

namespace GroupTheory.CrossedHomTransfer
open MulAction
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
  (V H : Subgroup G) [V.Normal] [IsMulCommutative V]

/-- On an abelian normal subgroup contained in `H`, transferring a local
retraction gives the power map with exponent `[G : H]`. -/
public theorem transfer_on_normal (hVH : V ≤ H) (f : H → V)
    (hfV : ∀ v : V, f (Subgroup.inclusion hVH v) = v) (v : V) :
    transfer H MulAut.conjNormal f v = v ^ H.index := by
  classical
  let := Fintype.ofFinite (G ⧸ H)
  have hc (q : G ⧸ H) : cosetFactor H (v : G) q =
      Subgroup.inclusion hVH (MulAut.conjNormal q.out⁻¹ v) := by
    apply Subtype.ext
    change q.out⁻¹ * ((v : G) * ((v : G)⁻¹ • q).out) = _
    rw [show (v : G)⁻¹ • q = q from normal_smul_coset_eq V H hVH v⁻¹ q]
    simp [mul_assoc]
  unfold transfer
  simp_rw [hc, hfV]
  have he (q : G ⧸ H) :
      MulAut.conjNormal q.out (MulAut.conjNormal q.out⁻¹ v) = v := by
    apply Subtype.ext
    simp
  simp_rw [he]
  rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card]

end GroupTheory.CrossedHomTransfer
