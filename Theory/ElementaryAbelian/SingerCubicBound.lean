module
public import Theory.ElementaryAbelian.SingerNormalizer
public import Theory.Representation.BinaryOffender.CubicEndField

/-!
# Cubic bounds in a binary Singer normalizer

An elementary abelian group with a regular cyclic automorphism group has
order at most sixteen if an automorphism subgroup in that normalizer has
cubic ratio at most two. The elementary actor attaining the ratio is cyclic,
so has order two. The Singer involution formula then bounds the whole group
by four times the square root of its order.

This is the numerical step used in Aschbacher--Smith 5.1.6(4), printed p.633
(`refs/quasithin.pdf`). The representation is marked by its actual action
on the given elementary abelian group.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 2 E]

theorem regular_cyclic_normalizer_cubic_card_le
    (C P : Subgroup (MulAut E)) [IsCyclic C]
    (hreg : ∀ v w : E, v ≠ 1 → w ≠ 1 → ∃! c : C, c.val v = w)
    (hn : P ≤ normalizer (C : Set (MulAut E)))
    (ρ : Representation (ZMod 2) P (Additive E))
    (hρ : ∀ a v, (ρ a (Additive.ofMul v)).toMul = a.val v)
    (hc : cubicRatio ρ ≤ 2) : Nat.card E ≤ 16 := by
  obtain ⟨A,hA,_,hbound⟩ := (cubicRatio_le_nat_iff_card_pow ρ 2).mp hc
  let := hA.2
  let Q := A.map P.subtype
  let : IsCyclic Q := regular_cyclic_automorphism_normalizer_two_subgroup C Q hreg
    ((IsElementaryAbelian.isPGroup 2 A).map P.subtype)
    (by rintro q ⟨a,ha,rfl⟩; exact hn a.property)
  let : IsCyclic A := isCyclic_of_injective (P.subtype.subgroupMap A)
    (by
      intro a b he
      have he' : (a.val : MulAut E) = (b.val : MulAut E) :=
        congrArg (fun z : Q => z.val) he
      exact Subtype.ext (Subtype.ext he'))
  have hac : Nat.card A ≤ 2 := by
    have hd := IsElementaryAbelian.exponent_dvd_p 2 A
    rw [IsCyclic.exponent_eq_card] at hd
    exact Nat.le_of_dvd (by decide) hd
  obtain ⟨t,ht,ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have htne : t.val ≠ 1 := fun he => ht1 (Subtype.ext he)
  have ht2 : t.val ^ 2 = 1 := congrArg P.subtype
    (elemPow_eq_one_of_isElementaryAbelian (p:=2) t ht)
  let F := t.val.toMonoidHom.eqLocus (MonoidHom.id E)
  have hf : Nat.card F ^ 2 = Nat.card E :=
    regular_cyclic_automorphism_normalizer_involution_fixed_card C hreg t.val htne ht2
      (hn t.property)
  let j : fixedSpace ρ A → F := fun v =>
    ⟨v.val.toMul, (hρ t v.val.toMul).symm.trans
      (congrArg Additive.toMul (v.property ⟨t,ht⟩))⟩
  have hj : Function.Injective j := by
    intro a b he
    apply Subtype.ext
    have he' : a.val.toMul = b.val.toMul := congrArg (fun z : F => z.val) he
    exact Additive.toMul.injective he'
  have hjc := Nat.card_le_card_of_injective j hj
  have hcard : Nat.card (Additive E) = Nat.card E := Nat.card_congr Additive.toMul
  rw [hcard] at hbound
  have hb : Nat.card E ≤ 4 * Nat.card F := hbound.trans
    (Nat.mul_le_mul (by nlinarith : Nat.card A ^ 2 ≤ 4) hjc)
  have hfc : Nat.card F ≤ 4 := by nlinarith
  nlinarith
end Theory.GroupTheory
