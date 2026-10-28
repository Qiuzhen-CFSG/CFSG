module

public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.Group

/-!
# Automorphisms detected by local displacement

Suppose that `E` is an elementary abelian two-subgroup with `C_G(E) ≤ E`.
An automorphism fixing `E` pointwise displaces each element `x` of `N_G(E)`
by `x⁻¹ β(x) ∈ C_G(E)`. It fixes this displacement, whose square is one,
so its square fixes `N_G(E)` pointwise. If it also fixes a subgroup `C`
and `C` together with a subgroup of `N_G(E)` generates `G`, its square is one.

Consequently, a locally inner square, with its conjugator in `C`, gives an
inner fourth power globally. If squares of arbitrary automorphisms take a
chosen element to a conjugate, and automorphisms fixing that element satisfy
the local condition, the actual outer quotient has exponent dividing eight.

This is the elementary group-theoretic reduction for the outer two-group
condition used in Aschbacher--Smith, *The Classification of Quasithin Groups*,
Volume I, Chapter 1, Section 3 (the J₄ entry, with the source return on p. 510).
No particular finite group, order, representation, or automorphism-class
assertion is assumed here. In particular, `E` need not be characteristic or
normal in `G`.
-/

public section

namespace MulAut

open Subgroup

variable {G : Type*} [Group G]

/-- Pointwise fixation of a self-centralizing elementary abelian two-subgroup
forces the square to fix its normalizer pointwise. -/
theorem square_apply_eq_on_normalizer
    (E : Subgroup G) [IsElementaryAbelian 2 E]
    (hself : centralizer (E : Set G) ≤ E)
    (β : MulAut G) (hfix : ∀ e ∈ E, β e = e)
    {x : G} (hx : x ∈ normalizer (E : Set G)) : (β ^ 2) x = x := by
  have hdisp : x⁻¹ * β x ∈ centralizer (E : Set G) := by
    intro e he
    have h := hfix (x * e * x⁻¹) ((mem_normalizer_iff.mp hx e).mp he)
    simp only [map_mul, map_inv, hfix e he] at h
    have hh := congrArg (fun t : G => x⁻¹ * t * β x) h
    group at hh
    simpa only [mul_assoc, zpow_neg_one] using hh.symm
  have hd := hfix (x⁻¹ * β x) (hself hdisp)
  have hpow : (x⁻¹ * β x) ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian _ (hself hdisp)
  change β (β x) = x
  calc
    β (β x) = β (x * (x⁻¹ * β x)) := by rw [mul_inv_cancel_left]
    _ = β x * (x⁻¹ * β x) := by rw [map_mul, hd]
    _ = x * ((x⁻¹ * β x) ^ 2) := by simp only [pow_two]; group
    _ = x := by rw [hpow, mul_one]

/-- A pointwise fixed subgroup and a subgroup of the normalizer of `E`
detect the square of an automorphism when they generate the whole group. -/
theorem square_eq_one_of_fixed_sup
    (E C M : Subgroup G) [IsElementaryAbelian 2 E]
    (hself : centralizer (E : Set G) ≤ E)
    (hEC : E ≤ C) (hMN : M ≤ normalizer (E : Set G))
    (hgen : C ⊔ M = ⊤)
    (β : MulAut G) (hfix : ∀ x ∈ C, β x = x) : β ^ 2 = 1 := by
  let F : Subgroup G := (β ^ 2).toMonoidHom.eqLocus (MonoidHom.id G)
  have hC : C ≤ F := by
    intro x hx
    change β (β x) = x
    rw [hfix x hx, hfix x hx]
  have hM : M ≤ F := by
    intro x hx
    exact square_apply_eq_on_normalizer E hself β (fun e he => hfix e (hEC he))
      (hMN hx)
  have hgenfix : C ⊔ M ≤ F := sup_le hC hM
  rw [hgen] at hgenfix
  apply MulEquiv.ext
  intro x
  change (β ^ 2) x = x
  exact hgenfix (mem_top x)

/-- If the square restricts to conjugation by an element of `C`, local
displacement makes the fourth power conjugation by that element's square. -/
theorem fourth_pow_eq_conj_of_local_square
    (E C M : Subgroup G) [IsElementaryAbelian 2 E]
    (hself : centralizer (E : Set G) ≤ E)
    (hEC : E ≤ C) (hMN : M ≤ normalizer (E : Set G))
    (hgen : C ⊔ M = ⊤)
    (α : MulAut G) (c : C)
    (hsquare : ∀ x ∈ C, (α ^ 2) x = (c : G) * x * (c : G)⁻¹) :
    α ^ 4 = MulAut.conj ((c : G) ^ 2) := by
  let β : MulAut G := MulAut.conj (c : G)⁻¹ * α ^ 2
  have hβfix : ∀ x ∈ C, β x = x := by
    intro x hx
    change (c : G)⁻¹ * ((α ^ 2) x) * ((c : G)⁻¹)⁻¹ = x
    rw [hsquare x hx]
    group
  have hβ2 := square_eq_one_of_fixed_sup E C M hself hEC hMN hgen β hβfix
  have hcfix : β (c : G) = c := hβfix c c.property
  have he : α ^ 2 = MulAut.conj (c : G) * β := by
    dsimp only [β]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  calc
    α ^ 4 = (α ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (MulAut.conj (c : G) * β) ^ 2 := by rw [he]
    _ = MulAut.conj ((c : G) ^ 2) := by
      apply MulEquiv.ext
      intro x
      have hx := DFunLike.congr_fun hβ2 x
      change β (β x) = x at hx
      change (c : G) * β ((c : G) * β x * (c : G)⁻¹) * (c : G)⁻¹ =
        (c : G) ^ 2 * x * ((c : G) ^ 2)⁻¹
      simp only [map_mul, map_inv, hcfix, hx, pow_two, mul_inv_rev, mul_assoc]

/-- First-element square conjugacy and inner local squares bound every actual
outer automorphism by exponent eight. -/
theorem outer_pow_eight_eq_one_of_local_squares
    (a : G) (E C M : Subgroup G) [IsElementaryAbelian 2 E]
    (hself : centralizer (E : Set G) ≤ E)
    (hEC : E ≤ C) (hMN : M ≤ normalizer (E : Set G))
    (hgen : C ⊔ M = ⊤)
    (hfirst : ∀ α : MulAut G, ∃ g : G, (α ^ 2) a = g * a * g⁻¹)
    (hlocal : ∀ α : MulAut G, α a = a → ∃ c : C,
      ∀ x ∈ C, (α ^ 2) x = (c : G) * x * (c : G)⁻¹)
    (z : Outer G) : z ^ 8 = 1 := by
  obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective (innerSubgroup G) z
  obtain ⟨g, hg⟩ := hfirst α
  let δ : MulAut G := MulAut.conj g⁻¹ * α ^ 2
  have hδa : δ a = a := by
    change g⁻¹ * ((α ^ 2) a) * (g⁻¹)⁻¹ = a
    rw [hg]
    group
  obtain ⟨c, hc⟩ := hlocal δ hδa
  have hδ4 := fourth_pow_eq_conj_of_local_square E C M hself hEC hMN hgen δ c hc
  let q := QuotientGroup.mk' (innerSubgroup G)
  have hqg : q (MulAut.conj g⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff (MulAut.conj g⁻¹)).mpr ⟨g⁻¹, rfl⟩
  have hqδ : q δ = (q α) ^ 2 := by
    simp only [δ, map_mul, map_pow, hqg, one_mul]
  change (q α) ^ 8 = 1
  calc
    (q α) ^ 8 = ((q α) ^ 2) ^ 4 := by rw [← pow_mul]
    _ = (q δ) ^ 4 := by rw [hqδ]
    _ = q (δ ^ 4) := (map_pow q δ 4).symm
    _ = q (MulAut.conj ((c : G) ^ 2)) := by rw [hδ4]
    _ = 1 := (QuotientGroup.eq_one_iff (MulAut.conj ((c : G) ^ 2))).mpr
      ⟨(c : G) ^ 2, rfl⟩

/-- The local square route proves the full outer quotient is a two-group;
neither finiteness nor simplicity is needed for this implication. -/
theorem outer_isPGroup_two_of_local_squares
    (a : G) (E C M : Subgroup G) [IsElementaryAbelian 2 E]
    (hself : centralizer (E : Set G) ≤ E)
    (hEC : E ≤ C) (hMN : M ≤ normalizer (E : Set G))
    (hgen : C ⊔ M = ⊤)
    (hfirst : ∀ α : MulAut G, ∃ g : G, (α ^ 2) a = g * a * g⁻¹)
    (hlocal : ∀ α : MulAut G, α a = a → ∃ c : C,
      ∀ x ∈ C, (α ^ 2) x = (c : G) * x * (c : G)⁻¹) :
    IsPGroup 2 (Outer G) := by
  intro z
  refine ⟨3, ?_⟩
  exact outer_pow_eight_eq_one_of_local_squares a E C M hself hEC hMN hgen hfirst hlocal z

end MulAut
