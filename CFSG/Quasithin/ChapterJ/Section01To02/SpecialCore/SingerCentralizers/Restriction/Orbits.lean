module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Restriction
public import Theory.Representation.PSL3Two.SingerRestriction.Orbits

/-!
# The source cubic orbit and the fixed-core commutator

The Singer and cubic images use the same Ru1 quotient map. The exact
Steinberg stabilizer makes the cubic image transitive on the three nonzero
Singer-fixed vectors. The literal fixed-core coordinate equivalence transports
this to conjugation on the nonidentity elements of S₀ = C_S(B₇).

A nonidentity commutator lies in S₀. Its cubic conjugates cover S₀ minus the
identity and remain in [S₀,B], proving S₀ = [S₀,B]. Together with the published
fixed-four-group equivalence, this supplies the cubic part of J.2.3(1).
The order-three hypothesis on the source cubic subgroup is retained explicitly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3(1), printed pp.433–434 (PDF pp.444–445).
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The actual cubic subgroup is transitive on the nonidentity elements of
S₀ = C_S(B₇), through the original Ru1 coordinates. -/
theorem SingerChoice.transitive_fixedCore (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (hB : Nat.card (cubicSubgroup d B) = 3)
    (u v : G) (hu : u ∈ fixedCore d c.B7) (hv : v ∈ fixedCore d c.B7)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    ∃ b ∈ cubicSubgroup d B, b * u * b⁻¹ = v := by
  let e := c.fixedCoreEquiv d B
  let u' := (e ⟨u, hu⟩).toAdd
  let v' := (e ⟨v, hv⟩).toAdd
  have hu0 : (u' : BinaryLinearThree.Steinberg) ≠ 0 := by
    intro h
    have he : e ⟨u, hu⟩ = e 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h
    exact hu1 (congrArg Subtype.val (e.injective he))
  have hv0 : (v' : BinaryLinearThree.Steinberg) ≠ 0 := by
    intro h
    have he : e ⟨v, hv⟩ = e 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      exact Subtype.ext h
    exact hv1 (congrArg Subtype.val (e.injective he))
  obtain ⟨g, hg, he⟩ := BinaryLinearThree.SingerRestriction.transitive_order_three
    (singerImage d B c) (cubicImage d B) (singerImage_card d B c)
    (cubicImage_card d B hB) (cubicImage_normalizes_singerImage d B c)
    u' v' u'.property v'.property hu0 hv0
  obtain ⟨b, hb⟩ := hg
  have hbu : (b : G) * u * (b : G)⁻¹ ∈ fixedCore d c.B7 :=
    (mem_normalizer_iff.mp (c.normalizes_fixedCore d B b.property) u).mp hu
  refine ⟨b, b.property, ?_⟩
  have heq : e ⟨(b : G) * u * (b : G)⁻¹, hbu⟩ = e ⟨v, hv⟩ := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    change ((c.fixedCoreEquiv d B _).toAdd : BinaryLinearThree.Steinberg) =
      ((c.fixedCoreEquiv d B _).toAdd : BinaryLinearThree.Steinberg)
    rw [c.fixedCoreEquiv_apply d B]
    have hequiv := d.ru1.steinberg.equivariant
      (inclusion (cubicSubgroup_le_L d B) b) ⟨u, hu.1⟩
    change _ = BinaryLinearThree.S (modelMap d (cubicSubgroup d B)
      (cubicSubgroup_le_L d B) b) _ at hequiv
    rw [hb] at hequiv
    exact hequiv.trans ((congrArg (BinaryLinearThree.S g)
      (c.fixedCoreEquiv_apply d B ⟨u, hu⟩).symm).trans he)
  exact congrArg Subtype.val (e.injective heq)

/-- The commutator assertion in J.2.3(1), with the source cubic order explicit. -/
theorem SingerChoice.fixedCore_commutator_cubic (d : TypeRuSetup G) (B : Sylow 3 d.L₁)
    (c : SingerChoice d B) (hB : Nat.card (cubicSubgroup d B) = 3) :
    ⁅fixedCore d c.B7, cubicSubgroup d B⁆ = fixedCore d c.B7 := by
  have hle : ⁅fixedCore d c.B7, cubicSubgroup d B⁆ ≤ fixedCore d c.B7 :=
    le_normalizer_iff_commutator_le_left.mp (c.normalizes_fixedCore d B)
  let e := c.fixedCoreEquivFour d B
  let x := e.symm (Multiplicative.ofAdd (1, 0))
  let y := e.symm (Multiplicative.ofAdd (0, 1))
  have hx : (x : G) ≠ 1 := by
    intro h
    have he := congrArg e (show x = 1 from Subtype.ext h)
    have hf : (Multiplicative.ofAdd (1, 0) : Multiplicative (ZMod 2 × ZMod 2)) = 1 := by
      simpa only [x, e.apply_symm_apply, map_one] using he
    exact (by decide : (Multiplicative.ofAdd (1, 0) : Multiplicative (ZMod 2 × ZMod 2)) ≠ 1) hf
  have hy : (y : G) ≠ 1 := by
    intro h
    have he := congrArg e (show y = 1 from Subtype.ext h)
    have hf : (Multiplicative.ofAdd (0, 1) : Multiplicative (ZMod 2 × ZMod 2)) = 1 := by
      simpa only [y, e.apply_symm_apply, map_one] using he
    exact (by decide : (Multiplicative.ofAdd (0, 1) : Multiplicative (ZMod 2 × ZMod 2)) ≠ 1) hf
  have hxy : (y : G) ≠ x := by
    intro h
    have he := congrArg e (show y = x from Subtype.ext h)
    have hf : (Multiplicative.ofAdd (0, 1) : Multiplicative (ZMod 2 × ZMod 2)) =
        Multiplicative.ofAdd (1, 0) := by
      simpa only [x, y, e.apply_symm_apply] using he
    exact (by decide : (Multiplicative.ofAdd (0, 1) : Multiplicative (ZMod 2 × ZMod 2)) ≠
      Multiplicative.ofAdd (1, 0)) hf
  obtain ⟨b, hb, he⟩ := c.transitive_fixedCore d B hB x y x.property y.property hx hy
  have hw : ⁅b, (x : G)⁆ ∈ ⁅fixedCore d c.B7, cubicSubgroup d B⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hb x.property
  have hw1 : ⁅b, (x : G)⁆ ≠ 1 := by
    rw [commutatorElement_def, he]
    exact fun h => hxy (mul_inv_eq_one.mp h)
  apply le_antisymm hle
  intro z hz
  by_cases hz1 : z = 1
  · exact hz1 ▸ (⁅fixedCore d c.B7, cubicSubgroup d B⁆ : Subgroup G).one_mem
  obtain ⟨a, ha, heq⟩ := c.transitive_fixedCore d B hB _ z (hle hw) hz hw1 hz1
  rw [← heq]
  exact (mem_normalizer_iff.mp (normalizer_commutator_ge_right
    (fixedCore d c.B7) (cubicSubgroup d B) ha) _).mp hw

end CFSG.Quasithin.ChapterJ.SpecialCore
