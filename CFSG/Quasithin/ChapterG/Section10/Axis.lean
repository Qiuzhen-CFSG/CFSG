module
public import CFSG.Quasithin.ChapterG.Section10.InvariantGeometry
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.GeneratorRank

/-!
# The full common-axis action in the reducible branch of G.10.4

The point form restricts nontrivially to a nonzero proper invariant U.
Evaluation of the displacements at a vector of pairing one embeds X/C_X(U)
in its hyperplane. The exact source rank equation and U∩W=0 make the order
bound an equality. Thus every hyperplane vector occurs and W complements U.

Source: Aschbacher--Smith, G.10.4, printed p.358.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- Full common-axis action and the actual complementary isotropic space,
for the proper G-submodule used by G.10.5. -/
theorem full_axis_on_submodule (U : Subrepresentation ρ)
    (hU0 : U.toSubmodule ≠ ⊥) (hUt : U.toSubmodule ≠ ⊤) :
    let f := (B v).comp U.toSubmodule.subtype
    IsCompl U.toSubmodule W ∧
      finrank (ZMod 2) U.toSubmodule = Group.rank (X ⧸ X₀) + 1 ∧
      ∀ a : f.ker, ∃ x : X, ∀ u : U.toSubmodule,
        U.toRepresentation x u = u + f u • (a : U.toSubmodule) := by
  let f := (B v).comp U.toSubmodule.subtype
  let : Finite f.ker := Module.finite_of_finite (ZMod 2)
  have hf : f ≠ 0 := h.axis_form_ne_zero U hU0
  obtain ⟨b, hb⟩ := LinearMap.range_eq_top.mp (Module.Dual.range_eq_top_of_ne_zero hf) 1
  have hfix (x : X) (u : U.toSubmodule) (hu : f u = 0) : U.toRepresentation x u = u := by
    apply Subtype.ext
    exact h.fixes_axis U.toSubmodule (fun x _ hu => U.apply_mem_toSubmodule x hu)
      (h.point_not_mem U hUt) x u u.property hu
  have hform (x : X) (u : U.toSubmodule) : f (U.toRepresentation x u) = f u := by
    have he := h.preserves (x : G) v u
    rw [show ρ (x : G) v = v from h.fixes_point x.property] at he
    exact he
  let d : X →* Multiplicative f.ker := {
    toFun x := Multiplicative.ofAdd ⟨U.toRepresentation x b - b, by
      change f (U.toRepresentation x b - b) = 0
      rw [map_sub, hform, sub_self]⟩
    map_one' := by
      apply congrArg Multiplicative.ofAdd
      apply Subtype.ext
      simp
    map_mul' x y := by
      apply congrArg Multiplicative.ofAdd
      apply Subtype.ext
      change U.toRepresentation ((x : G) * y) b - b =
        (U.toRepresentation x b - b) + (U.toRepresentation y b - b)
      have he := hfix x (U.toRepresentation y b - b) (by rw [map_sub, hform, sub_self])
      rw [map_sub] at he
      rw [map_mul, Module.End.mul_apply]
      rw [show U.toRepresentation x (U.toRepresentation y b) =
        (U.toRepresentation y b - b) + U.toRepresentation x b from sub_eq_iff_eq_add.mp he]
      abel }
  have hk : d.ker ≤ X₀ := by
    intro x hx
    by_contra hx0
    have he : U.toRepresentation x b = b := by
      apply sub_eq_zero.mp
      exact congrArg (fun a : Multiplicative f.ker => (a.toAdd : U.toSubmodule)) hx
    have hz := h.fixed_bound x hx0 b (congrArg Subtype.val he)
    have hh : f b = 0 := hz
    rw [hb] at hh
    exact one_ne_zero hh
  have hcard : Nat.card (X ⧸ X₀) ≤ 2 ^ finrank (ZMod 2) f.ker := by
    calc
      Nat.card (X ⧸ X₀) = X₀.index := rfl
      _ ≤ d.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero d.ker.index_ne_zero_of_finite) (index_dvd_of_le hk)
      _ = Nat.card d.range := index_ker d
      _ ≤ Nat.card (Multiplicative f.ker) := d.range.card_le_card_group
      _ = 2 ^ finrank (ZMod 2) f.ker := by
        rw [Nat.card_congr Multiplicative.toAdd]
        simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := f.ker)
  have hr := IsElementaryAbelian.rank_le_of_card_le (X ⧸ X₀) hcard
  have hker : finrank (ZMod 2) f.ker + 1 = finrank (ZMod 2) U.toSubmodule := by
    have he := f.finrank_range_add_finrank_ker
    rw [Module.Dual.range_eq_top_of_ne_zero hf, finrank_top, Module.finrank_self] at he
    omega
  have hdis := h.submodule_disjoint_W U hUt
  have hsum : finrank (ZMod 2) U.toSubmodule + finrank (ZMod 2) W ≤ finrank (ZMod 2) V := by
    have he := Submodule.finrank_sup_add_finrank_inf_eq U.toSubmodule W
    rw [hdis.eq_bot, finrank_bot, add_zero] at he
    rw [← he]
    exact Submodule.finrank_le _
  have hp : 0 < finrank (ZMod 2) V := by
    let : Nontrivial V := ⟨⟨v, 0, h.point_ne_zero⟩⟩
    exact Module.finrank_pos
  have heqdim : finrank (ZMod 2) U.toSubmodule = Group.rank (X ⧸ X₀) + 1 := by
    have hs := h.dimension
    omega
  have hcompl : IsCompl U.toSubmodule W := by
    refine ⟨hdis, codisjoint_iff.mpr ?_⟩
    apply Submodule.eq_top_of_finrank_eq
    have he := Submodule.finrank_sup_add_finrank_inf_eq U.toSubmodule W
    rw [hdis.eq_bot, finrank_bot, add_zero] at he
    have hs := h.dimension
    omega
  have hsur : Function.Surjective d := by
    have hpow : 2 ^ Group.rank (X ⧸ X₀) ≤ Nat.card (X ⧸ X₀) := by
      have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (X ⧸ X₀))
      have hr := IsElementaryAbelian.rank_le_finrank (p := 2) (X ⧸ X₀)
      rw [← Nat.card_congr Additive.ofMul, Nat.card_zmod] at hc
      rw [hc]
      exact Nat.pow_le_pow_right (by decide) hr
    have hsize : Nat.card (Multiplicative f.ker) ≤ Nat.card d.range := by
      calc
        _ = 2 ^ finrank (ZMod 2) f.ker := by
          rw [Nat.card_congr Multiplicative.toAdd]
          simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := f.ker)
        _ = 2 ^ Group.rank (X ⧸ X₀) := by congr 1; omega
        _ ≤ Nat.card (X ⧸ X₀) := hpow
        _ ≤ d.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero d.ker.index_ne_zero_of_finite) (index_dvd_of_le hk)
        _ = Nat.card d.range := index_ker d
    have ht : d.range = ⊤ := Subgroup.eq_top_of_card_eq d.range (le_antisymm d.range.card_le_card_group hsize)
    exact MonoidHom.range_eq_top.mp ht
  refine ⟨hcompl, heqdim, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := hsur (Multiplicative.ofAdd a)
  refine ⟨x, fun u => ?_⟩
  have he := hfix x (u - f u • b) (by simp [map_sub, map_smul, hb])
  have hd : U.toRepresentation x b - b = (a : U.toSubmodule) :=
    congrArg (fun a : Multiplicative f.ker => (a.toAdd : U.toSubmodule)) hx
  rw [map_sub, map_smul] at he
  rw [sub_eq_iff_eq_add] at he
  rw [show U.toRepresentation x b = (a : U.toSubmodule) + b from sub_eq_iff_eq_add.mp hd,
    smul_add] at he
  rw [he]
  abel

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
