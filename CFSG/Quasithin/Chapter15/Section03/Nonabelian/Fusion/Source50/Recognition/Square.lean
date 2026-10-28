module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.Recognition.Consumer
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.Extraspecial.MarkedGeometry.Transport
public import Theory.GroupTheory.PGroup.ExtraspecialInvolution

/-!
# The actual source power form in the fusion coordinates

The zero set of the source quadratic form is exactly the square-one lifts.
Since the extraspecial center is the actual subgroup Z of order two, this
already determines every square, for either nonidentity choice of generator.
Transport gives the literal `SquareForm` and the singular natural preimage
needed by 15.3.61.
Source: Aschbacher–Smith 15.3.56(1) and 15.3.58, printed pp.1147–1149.
-/

@[expose] public section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
open NormalReduction
universe u
variable {G : Type u} [Group G] [Finite G] {Z ZS V M : Subgroup G}
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)] [IsElementaryAbelian 2 V]
  {C : GroupClass.{u}} {v : ActorQuotient Z} {s : ℕ}
  {d : EarlierSourceInputs Z ZS V M C v s} {a : EarlierActionInputs d}

namespace EarlierPowerInputs
omit [Finite G] in
/-- The two-element center upgrades the zero-set description to every square. -/
theorem square_formula (b : EarlierPowerInputs d a) (z : G) (hz : z ∈ Z) (hz1 : z ≠ 1) (x : closureU Z ZS) :
    (x : G) ^ 2 =
      z ^ (a.quadratic (Additive.ofMul (QuotientGroup.mk' _ x))).val := by
  let := b.extraspecial
  have hbit : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hbit (a.quadratic (Additive.ofMul (QuotientGroup.mk' _ x))) with hq | hq
  · rw [hq]
    simpa only [ZMod.val_zero, pow_zero, Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val ((b.power_zero x).mp hq)
  · rw [hq, ZMod.val_one, pow_one]
    have hxsq : (x : G) ^ 2 ∈ Z := by
      have h := b.center_eq ▸ IsExtraspecial.square_mem_center x
      exact h
    have hxne : (x : G) ^ 2 ≠ 1 := by
      intro he
      have hq0 := (b.power_zero x).mpr (Subtype.ext he)
      rw [hq] at hq0
      exact one_ne_zero hq0
    obtain ⟨r, _, hr⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp d.Z_card
    exact congrArg Subtype.val ((hr ⟨_, hxsq⟩ (by exact fun h => hxne (congrArg Subtype.val h))).trans
      (hr ⟨z, hz⟩ (by exact fun h => hz1 (congrArg Subtype.val h))).symm)

end EarlierPowerInputs

namespace NaturalPair
variable (p : NaturalPair d a)
variable {T : Subgroup G} {t : G}
  {ht : t ∈ T} {hH : t ∈ centralizerH Z}
  {hout : t ∉ closureU Z ZS ⊔ (T ⊓ centralizer (V : Set G))}
  {houter : QuotientGroup.mk' (pCore 2 (centralizerH Z)) ⟨t, hH⟩ ∉ p.K}

/-- The chosen natural subspace has square-one preimage in the actual U. -/
theorem natural_preimage_squares (b : EarlierPowerInputs d a) :
    ∀ x ∈ Fusion.ResidualOrbits.Extraspecial.naturalPreimage
      (p.recognizedAction t ht hH hout houter), x ^ 2 = 1 := by
  intro x hx
  have hxU : x ∈ closureU Z ZS :=
    Fusion.ResidualOrbits.Extraspecial.naturalPreimage_le
      (p.recognizedAction t ht hH hout houter) hx
  let u : closureU Z ZS := ⟨x, hxU⟩
  have hz : (p.coordinates (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u)).toAdd.2 = 0 :=
    (Fusion.ResidualOrbits.Extraspecial.mem_naturalPreimage
      (p.recognizedAction t ht hH hout houter) u).mp hx
  have hm : Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf (closureU Z ZS)) u) ∈
      p.pair.first.toSubmodule := (p.mem_first_iff _).mpr hz
  exact congrArg Subtype.val ((b.power_zero u).mp (p.first_singular _ hm))

/-- The square-form field of the final fusion consumer is supplied by the
earlier source power form, on its actual quotient map. -/
noncomputable def squareForm (b : EarlierPowerInputs d a) (z : G)
    (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Fusion.ResidualOrbits.Extraspecial.SquareForm
      (p.recognizedAction t ht hH hout houter) z := by
  let e : VectorQuotient Z ZS ≃* Multiplicative (Space Z ZS) := {
    toFun := fun w => Multiplicative.ofAdd (Additive.ofMul w)
    invFun := fun w => w.toAdd.toMul
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  exact Fusion.ResidualOrbits.Extraspecial.SquareForm.of_orthogonalSpace
    (p.recognizedAction t ht hH hout houter) e a.quadratic a.nondegenerate
    (b.square_formula z hz hz1)

end NaturalPair
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition
