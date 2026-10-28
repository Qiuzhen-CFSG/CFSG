module

public import Theory.Representation.BinaryOffender.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# A limitation of the rank reduction for 15.3.49(h)

This diagnostic isolates the missing inference after Geometry.Selection.
Let E₁₆ act on F₂⁶, with coordinates (x₀,x₁,x₂,y₀,y₁,y₂), by adding
(a₀x₀+a₃x₁, a₁x₀+a₃x₂, a₂x₀) to the last three coordinates.
The action is faithful and quadratic. Let A be a₂ = 0 and B = E₁₆.
Both have the same three-dimensional fixed space D. Thus
codim D = rank A = 3 < rank B = 4: A is an ordinary offender and B is strong.
Nevertheless neither is best. The subgroup a₂ = a₃ = 0 has weight 7 > 6
for A, and a₃ = 0 has weight 8 > 7 for B.

All finite calculations use kernel-checked decision procedures. The example
satisfies the representation-level conclusions of the selected-rank argument,
even with equality of the full fixed spaces. It does not provide the actual
conjugate spans, local two-cores, or SectionActions of 15.3.49. Consequently it
does not refute that source assertion; a proof still needs further geometry.

Source of the inference being tested: Aschbacher–Smith, combined manuscript
(1 March 2004), 15.3.49(h), printed p.1143, and B.1.2–3, printed p.68.
-/

open Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.BestWeights
private abbrev Actor := Multiplicative (Fin 4 → ZMod 2)
private abbrev Space := Fin 6 → ZMod 2

private def actionMap (a : Actor) : Space →ₗ[ZMod 2] Space where
  toFun v := ![v 0, v 1, v 2,
    v 3 + a.toAdd 0 * v 0 + a.toAdd 3 * v 1,
    v 4 + a.toAdd 1 * v 0 + a.toAdd 3 * v 2,
    v 5 + a.toAdd 2 * v 0]
  map_add' v w := by ext i; fin_cases i <;> simp [mul_add] <;> ring
  map_smul' c v := by ext i; fin_cases i <;> simp <;> ring

private def rho : Representation (ZMod 2) Actor Space where
  toFun := actionMap
  map_one' := by ext v i; fin_cases i <;> simp [actionMap]
  map_mul' a b := by
    ext v i
    fin_cases i <;> simp [actionMap, Module.End.mul_apply, add_mul] <;> ring

private def small : Subgroup Actor where
  carrier := {a | a.toAdd 2 = 0}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.toAdd 2 + b.toAdd 2 = 0; rw [ha, hb, add_zero]
  inv_mem' := by intro a ha; change -a.toAdd 2 = 0; rw [ha, neg_zero]

private def bad : Subgroup Actor where
  carrier := {a | a.toAdd 3 = 0}
  one_mem' := rfl
  mul_mem' := by intro a b ha hb; change a.toAdd 3 + b.toAdd 3 = 0; rw [ha, hb, add_zero]
  inv_mem' := by intro a ha; change -a.toAdd 3 = 0; rw [ha, neg_zero]

private instance : IsElementaryAbelian 2 Actor where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    decide +kernel

private instance : DecidablePred (fun a : Actor => a ∈ small) :=
  fun a => inferInstanceAs (Decidable (a.toAdd 2 = 0))
private instance : DecidablePred (fun a : Actor => a ∈ bad) :=
  fun a => inferInstanceAs (Decidable (a.toAdd 3 = 0))
private instance : DecidablePred (fun a : Actor => a ∈ (⊤ : Subgroup Actor)) :=
  fun a => isTrue (Subgroup.mem_top a)
private instance : DecidablePred (fun a : Actor => a ∈ (small ⊓ bad : Subgroup Actor)) :=
  fun a => inferInstanceAs (Decidable (a.toAdd 2 = 0 ∧ a.toAdd 3 = 0))

private theorem actor_card : Nat.card Actor = 16 := by simp [Actor]
private theorem small_card : Nat.card small = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem bad_card : Nat.card bad = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel
private theorem badSmall_card : Nat.card (small ⊓ bad : Subgroup Actor) = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private theorem fixed_top : ∀ v : Space, v ∈ fixedSpace rho ⊤ ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  change ∀ v : Space, (∀ a : (⊤ : Subgroup Actor), actionMap a.val v = v) ↔ _
  decide +kernel

private theorem faithful : Function.Injective rho := by
  intro a b hab
  have h : actionMap a = actionMap b := hab
  have h0 := congrArg (fun f : Space →ₗ[ZMod 2] Space => f ![1,0,0,0,0,0]) h
  have h1 := congrArg (fun f : Space →ₗ[ZMod 2] Space => f ![0,1,0,0,0,0]) h
  apply Multiplicative.toAdd.injective
  funext i
  fin_cases i
  · simpa [actionMap] using congrFun h0 3
  · simpa [actionMap] using congrFun h0 4
  · simpa [actionMap] using congrFun h0 5
  · simpa [actionMap] using congrFun h1 3

private theorem quadratic : IsQuadratic rho ⊤ := by
  intro a _ b _ v
  change actionMap a (actionMap b v - v) = actionMap b v - v
  ext i
  fin_cases i <;> simp [actionMap, Matrix.vecHead, Matrix.vecTail]

private theorem fixed_small : ∀ v : Space, v ∈ fixedSpace rho small ↔ v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0 := by
  change ∀ v : Space, (∀ a : small, actionMap a.val v = v) ↔ _
  decide +kernel

private theorem fixed_bad : ∀ v : Space, v ∈ fixedSpace rho bad ↔ v 0 = 0 := by
  change ∀ v : Space, (∀ a : bad, actionMap a.val v = v) ↔ _
  decide +kernel

private theorem fixed_badSmall : ∀ v : Space, v ∈ fixedSpace rho (small ⊓ bad) ↔ v 0 = 0 := by
  change ∀ v : Space, (∀ a : (small ⊓ bad : Subgroup Actor), actionMap a.val v = v) ↔ _
  decide +kernel

private def fixedThree : Submodule (ZMod 2) Space where
  carrier := {v | v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨h0, h1, h2⟩ ⟨k0, k1, k2⟩; simp_all
  smul_mem' := by rintro c v ⟨h0, h1, h2⟩; simp_all

private def fixedFive : Submodule (ZMod 2) Space where
  carrier := {v | v 0 = 0}
  zero_mem' := rfl
  add_mem' := by intro v w hv hw; change v 0 + w 0 = 0; rw [hv, hw, add_zero]
  smul_mem' := by intro c v hv; change c * v 0 = 0; rw [hv, mul_zero]

private instance : DecidablePred (fun v : Space => v ∈ fixedThree) :=
  fun v => inferInstanceAs (Decidable (v 0 = 0 ∧ v 1 = 0 ∧ v 2 = 0))
private instance : DecidablePred (fun v : Space => v ∈ fixedFive) :=
  fun v => inferInstanceAs (Decidable (v 0 = 0))

private theorem fixedThree_card : Nat.card fixedThree = 8 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private theorem fixedFive_card : Nat.card fixedFive = 32 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private theorem space_finrank : Module.finrank (ZMod 2) Space = 6 := by simp [Space]


private theorem elementary (A : Subgroup Actor) : IsElementaryAbelian 2 A where
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro a
    apply Subtype.ext
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 Actor) a)

private theorem fixedThree_finrank : Module.finrank (ZMod 2) fixedThree = 3 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedThree)
  rw [fixedThree_card, Nat.card_zmod] at hc
  have he := congrArg (Nat.log 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2), show Nat.log 2 8 = 3 by decide] using he.symm

private theorem fixedFive_finrank : Module.finrank (ZMod 2) fixedFive = 5 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedFive)
  rw [fixedFive_card, Nat.card_zmod] at hc
  have he := congrArg (Nat.log 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2), show Nat.log 2 32 = 5 by decide] using he.symm

private theorem fixed_top_eq : fixedSpace rho ⊤ = fixedThree := by ext v; exact fixed_top v

private theorem fixed_small_eq : fixedSpace rho small = fixedThree := by ext v; exact fixed_small v

private theorem fixed_bad_eq : fixedSpace rho bad = fixedFive := by ext v; exact fixed_bad v

private theorem fixed_badSmall_eq : fixedSpace rho (small ⊓ bad) = fixedFive := by
  ext v; exact fixed_badSmall v

private theorem ranks : rank small = 3 ∧ rank (⊤ : Subgroup Actor) = 4 ∧
    rank bad = 3 ∧ rank (small ⊓ bad) = 2 := by
  have ht : Nat.card (⊤ : Subgroup Actor) = 16 := by simp [Actor]
  unfold rank
  rw [small_card, ht, bad_card, badSmall_card]
  decide

private theorem weights : weight rho small = 6 ∧ weight rho ⊤ = 7 ∧
    weight rho bad = 8 ∧ weight rho (small ⊓ bad) = 7 := by
  unfold weight
  rw [ranks.1, ranks.2.1, ranks.2.2.1, ranks.2.2.2,
    fixed_top_eq, fixed_small_eq, fixed_bad_eq, fixed_badSmall_eq,
    fixedThree_finrank, fixedFive_finrank]
  decide

private theorem codims : fixedCodim rho small = 3 ∧ fixedCodim rho ⊤ = 3 := by
  have hs := fixedCodim_add_finrank rho small
  have ht := fixedCodim_add_finrank rho ⊤
  rw [fixed_small_eq, fixedThree_finrank, space_finrank] at hs
  rw [fixed_top_eq, fixedThree_finrank, space_finrank] at ht
  omega

/-- The representation-level consequences of the selected rank inequality do not
imply best offending, even when D is the full fixed space for both actors and
the larger actor is a strong offender. This does not realize the source's
endpoint spans or refute its full local group hypotheses. -/
public theorem selected_rank_obstruction :
    ∃ (ρ : Representation (ZMod 2) (Multiplicative (Fin 4 → ZMod 2)) (Fin 6 → ZMod 2))
      (D : Submodule (ZMod 2) (Fin 6 → ZMod 2))
      (A B : Subgroup (Multiplicative (Fin 4 → ZMod 2))),
      Function.Injective ρ ∧ A < B ∧
      D = fixedSpace ρ A ∧ D = fixedSpace ρ B ∧
      Module.finrank (ZMod 2) ((Fin 6 → ZMod 2) ⧸ D) = rank A ∧
      IsOffender ρ A ∧ IsStrongOffender ρ B ∧
      IsQuadratic ρ A ∧ IsQuadratic ρ B ∧
      ¬ IsBestOffender ρ A ∧ ¬ IsBestOffender ρ B := by
  have hsmall : IsElementaryTwo small := by
    refine ⟨?_, elementary small⟩
    intro he
    have hc := small_card
    rw [he] at hc
    simp at hc
  have htop : IsElementaryTwo (⊤ : Subgroup Actor) := ⟨top_ne_bot, elementary ⊤⟩
  have hlt : small < (⊤ : Subgroup Actor) := by
    apply lt_top_iff_ne_top.mpr
    intro he
    have h := ranks.1
    rw [he, ranks.2.1] at h
    omega
  refine ⟨rho, fixedThree, small, ⊤, faithful, hlt,
    fixed_small_eq.symm, fixed_top_eq.symm, ?_,
    ⟨hsmall, by rw [codims.1, ranks.1]⟩,
    ⟨htop, by rw [codims.2, ranks.2.1]; decide⟩,
    (fun a _ b _ v => quadratic a (Subgroup.mem_top a) b (Subgroup.mem_top b) v),
    quadratic, ?_, ?_⟩
  · have h := fixedThree.finrank_quotient_add_finrank
    rw [fixedThree_finrank, space_finrank] at h
    have hd : Module.finrank (ZMod 2) (Space ⧸ fixedThree) = 3 := by omega
    simpa only [ranks.1] using hd
  · intro h
    have hw := h.2 (small ⊓ bad) inf_le_left
    rw [weights.1, weights.2.2.2] at hw
    omega
  · intro h
    have hw := h.2 bad le_top
    rw [weights.2.1, weights.2.2.1] at hw
    omega
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Geometry.BestWeights
