module

public import Theory.Representation.HexacodeAction.Field
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Quadraticity on the actual six-dimensional triple-cover module

A nonzero product of commuting square-zero operators produces four linearly
independent vectors v, xv, yv, xyv. Thus the product vanishes in dimension at
most three. In characteristic two this applies to displacements of commuting
involutions. The actual even hexacode cover acts linearly on F₄³, so every
one of its elementary abelian two-subgroups acts quadratically.

This checks a proposed terminal route for Aschbacher–Smith 13.8.21(2),
printed p.956. A nonquadratic four-group on this six-dimensional quotient
cannot supply that route when the actor lies in the even cover. Moreover the two-core of every
subgroup containing the cubic scalar lies in the even cover, so an
elementary two-core of such a subgroup is quadratic on this module. The source
invokes the action on U_H; its complete local hypotheses, any lift from the
quotient, and the actual parabolic marking must still be used. This is not
a counterexample to the source theorem under its standing hypotheses.
The hexacode action and its genuine perfect central cover are from the
existing attributed ATLAS port, via `Representation.Hexacode`.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers
open scoped BigOperators
private theorem square_zero_product_eq_zero {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (x y : Module.End F V)
    (hx : ∀ v, x (x v) = 0) (hy : ∀ v, y (y v) = 0)
    (hc : ∀ v, x (y v) = y (x v))
    (hd : Module.finrank F V ≤ 3) : ∀ v, x (y v) = 0 := by
  intro v
  by_contra hn
  have hxyx : x (y (x v)) = 0 := by rw [hc (x v), hx, map_zero]
  have hxyy : x (y (y v)) = 0 := by rw [hy, map_zero]
  have hyxy : y (x (y v)) = 0 := by rw [← hc (y v), hy, map_zero]
  have hli : LinearIndependent F ![v, x v, y v, x (y v)] := by
    rw [Fintype.linearIndependent_iff]
    intro a ha i
    have he : a 0 • v + a 1 • x v + a 2 • y v + a 3 • x (y v) = 0 := by
      simpa [Fin.sum_univ_four] using ha
    have h0 : a 0 = 0 := by
      have h := congrArg (fun w => x (y w)) he
      simp only [map_add, map_smul, map_zero, hxyx, hxyy, hyxy, smul_zero,
        add_zero] at h
      exact (smul_eq_zero.mp h).resolve_right hn
    have h1 : a 1 = 0 := by
      have h := congrArg y he
      simp only [map_add, map_smul, map_zero, h0, zero_smul, zero_add, hy, hyxy,
        smul_zero, add_zero, ← hc] at h
      exact (smul_eq_zero.mp h).resolve_right hn
    have h2 : a 2 = 0 := by
      have h := congrArg x he
      simp only [map_add, map_smul, map_zero, h0, h1, zero_smul, zero_add, hx,
        smul_zero, add_zero] at h
      exact (smul_eq_zero.mp h).resolve_right hn
    have h3 : a 3 = 0 := by
      simp only [h0, h1, h2, zero_smul, zero_add] at he
      exact (smul_eq_zero.mp he).resolve_right hn
    fin_cases i <;> assumption
  have h := hli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at h
  omega


private theorem involutions_quadratic_three
    {F V : Type*} [Field F] [CharP F 2] [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (f g : Module.End F V)
    (hf : ∀ v, f (f v) = v) (hg : ∀ v, g (g v) = v)
    (hc : ∀ v, f (g v) = g (f v)) (hd : Module.finrank F V ≤ 3) :
    ∀ v, f (g v - v) = g v - v := by
  have hadd (v : V) : v + v = 0 := by
    rw [← two_smul F, show (2 : F) = 0 from CharP.cast_eq_zero F 2, zero_smul]
  have hneg (v : V) : -v = v := (neg_eq_iff_add_eq_zero).mpr (hadd v)
  let x : Module.End F V := f + 1
  let y : Module.End F V := g + 1
  have hx (v : V) : x (x v) = 0 := by
    change f (f v + v) + (f v + v) = 0
    rw [map_add, hf]
    calc
      v + f v + (f v + v) = (v + v) + (f v + f v) := by abel
      _ = 0 := by rw [hadd, hadd, zero_add]
  have hy (v : V) : y (y v) = 0 := by
    change g (g v + v) + (g v + v) = 0
    rw [map_add, hg]
    calc
      v + g v + (g v + v) = (v + v) + (g v + g v) := by abel
      _ = 0 := by rw [hadd, hadd, zero_add]
  have hxy (v : V) : x (y v) = y (x v) := by
    change f (g v + v) + (g v + v) = g (f v + v) + (f v + v)
    rw [map_add, map_add, hc]
    abel
  intro v
  have he := square_zero_product_eq_zero x y hx hy hxy hd v
  change f (g v + v) + (g v + v) = 0 at he
  rw [sub_eq_add_neg, hneg]
  exact (eq_neg_iff_add_eq_zero.mpr he).trans (hneg _)

open Atlas.Codes Representation.Hexacode Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement

/-- Every elementary two-subgroup of the genuine even hexacode cover is
quadratic on its binary six-dimensional module. In particular this holds
for any marked E₄ lying in that cover. -/
theorem even_hexacode_elementary_quadratic (A : Subgroup HexEvenAutomorphisms) [IsElementaryAbelian 2 A] :
    IsQuadratic (action.comp hexSign.ker.subtype) A := by
  intro a ha b hb v
  have haa : a * a = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha
  have hbb : b * b = 1 := by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) b hb
  have hab : a * b = b * a :=
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  apply involutions_quadratic_three
    (evenFieldAction a).toLinearMap (evenFieldAction b).toLinearMap
  · intro w
    change (evenFieldAction a * evenFieldAction a) w = w
    rw [← map_mul, haa, map_one]
    rfl
  · intro w
    change (evenFieldAction b * evenFieldAction b) w = w
    rw [← map_mul, hbb, map_one]
    rfl
  · intro w
    change (evenFieldAction a * evenFieldAction b) w =
      (evenFieldAction b * evenFieldAction a) w
    rw [← map_mul, ← map_mul, hab]
  · exact field_finrank.le

open Subgroup

/-- The two-core of a subgroup containing the cubic scalar lies in the
even cover. An odd element would put its nontrivial order-three commutator
with that scalar into the two-core. -/
theorem twoCore_le_even_of_scalar_mem (P : Subgroup HexAutomorphisms) (hz : hexZ ∈ P) :
    P.pCoreIn 2 ≤ hexSign.ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro a ⟨a, ha, rfl⟩
  rcases Int.units_eq_one_or (hexSign a.val) with he | he
  · exact he
  · let z : P := ⟨hexZ, hz⟩
    have hc : ⁅a, z⁆ ∈ pCore 2 P :=
      commutator_le_left (pCore 2 P) ⊤
        (commutator_mem_commutator ha (mem_top z))
    have hzinv : hexZ⁻¹ * hexZ⁻¹ = hexZ := by
      rw [← mul_inv_rev]
      apply inv_eq_iff_mul_eq_one.mpr
      simpa [pow_succ] using hexZ_cube
    have heq : ⁅a, z⁆ = z := by
      apply Subtype.ext
      change a.val * hexZ * a.val⁻¹ * hexZ⁻¹ = hexZ
      rw [hex_conjugation_odd a.val he, hzinv]
    rw [heq] at hc
    have hn : (⟨z, hc⟩ : pCore 2 P) ≠ 1 := by
      intro h
      exact hexZ_ne_one (congrArg (fun x : pCore 2 P => x.val.val) h)
    have hd := (pCore_isPGroup (p := 2) (G := P)).dvd_orderOf hn
    have ho : orderOf (⟨z, hc⟩ : pCore 2 P) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hexZ_order]
    rw [ho] at hd
    norm_num at hd

/-- Transfer quadraticity from the even subgroup to its ambient image. -/
theorem hexacode_elementary_quadratic_of_le_even (A : Subgroup HexAutomorphisms) [IsElementaryAbelian 2 A]
    (hA : A ≤ hexSign.ker) : IsQuadratic action A := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 (A.subgroupOf hexSign.ker) :=
    IsElementaryAbelian.subgroupOf hA
  intro a ha b hb v
  exact even_hexacode_elementary_quadratic (A.subgroupOf hexSign.ker)
    ⟨a, hA ha⟩ ha ⟨b, hA hb⟩ hb v

/-- In particular, an elementary two-core of a scalar-containing point
stabilizer is quadratic on the actual hexacode module. The terminal source
contradiction cannot be obtained by asserting its nonquadraticity here. -/
theorem hexacode_twoCore_quadratic (P : Subgroup HexAutomorphisms)
    (hz : hexZ ∈ P) [IsElementaryAbelian 2 (P.pCoreIn 2)] :
    IsQuadratic action (P.pCoreIn 2) :=
  hexacode_elementary_quadratic_of_le_even (P.pCoreIn 2)
    (twoCore_le_even_of_scalar_mem P hz)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers
