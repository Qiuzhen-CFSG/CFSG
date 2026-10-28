module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.LocalStructure.PairedModule.MarkedAction

/-!
# The original cubic actor and its norm

The marked image of `Y_E` is `A₃ × 1`, so a generator lifts to an element
of the original `Y_E`. On the actual binary section, `1+y+y²` kills every
`Y_E`-displacement: the action factors through the marked core quotient,
and the first image is cyclic of order three. The equality `U=[U,Y_E]`
then makes the norm vanish on the entire section. The proof uses ambient
commutators and the original projection, without assuming a module splitting.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1153, PDF p.1170, before the temporary replacement.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
open Descent.QuotientIdentification
variable {G : Type*} [Group G] {V Y T E : Subgroup G}

private def cycle : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

private theorem cycle_order : orderOf cycle = 3 := by
  apply orderOf_eq_prime_iff.mpr
  constructor <;> decide +kernel

private theorem cycle_even : cycle ∈ alternatingGroup (Fin 3) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide +kernel

private theorem alternating_three_cases : ∀ a b : Equiv.Perm (Fin 3),
    a ^ 3 = 1 → a ≠ 1 → Equiv.Perm.sign b = 1 → b = 1 ∨ b = a ∨ b = a * a := by
  decide +kernel

/-- A cubic generator lifts to the original residual subgroup. -/
theorem exists_original_cubic (d : MarkedDecomposition Y T E)
    (hY : ((lineY Y E).subgroupOf (lineNormalizer E)).map
      (d.equiv.toMonoidHom.comp (quotientMap E)) =
      (alternatingGroup (Fin 3)).prod ⊥) :
    ∃ y : lineNormalizer E, (y : G) ∈ lineY Y E ∧
      orderOf (d.equiv (quotientMap E y)).1 = 3 ∧
      (d.equiv (quotientMap E y)).2 = 1 := by
  have hm : (cycle, (1 : centralizerImage E)) ∈
      ((lineY Y E).subgroupOf (lineNormalizer E)).map
        (d.equiv.toMonoidHom.comp (quotientMap E)) := by
    rw [hY]
    exact ⟨cycle_even, rfl⟩
  obtain ⟨y, hy, he⟩ := hm
  refine ⟨y, hy, ?_, ?_⟩
  · change orderOf ((d.equiv.toMonoidHom.comp (quotientMap E)) y).1 = 3
    rw [he]
    exact cycle_order
  · exact congrArg Prod.snd he

variable [IsElementaryAbelian 2 (lineV V E)]

/-- Commutator generation and the marked cyclic image kill the cubic norm. -/
theorem cubic_norm_eq_zero (d : MarkedDecomposition Y T E)
    (hcomm : ⁅lineV V E, lineQ E⁆ ≤ E)
    (hmove : lineV V E = ⁅lineV V E, lineY Y E⁆)
    (hY : ((lineY Y E).subgroupOf (lineNormalizer E)).map
      (d.equiv.toMonoidHom.comp (quotientMap E)) =
      (alternatingGroup (Fin 3)).prod ⊥)
    (y : lineNormalizer E)
    (hy : orderOf (d.equiv (quotientMap E y)).1 = 3)
    (hy2 : (d.equiv (quotientMap E y)).2 = 1)
    (x : SectionSpace V E) :
    x + sectionRepresentation V E y x + sectionRepresentation V E (y * y) x = 0 := by
  let f := d.equiv.toMonoidHom.comp (quotientMap E)
  let r := markedRepresentation V E d hcomm
  let t := sectionRepresentation V E y
  let N := (1 + t + t ^ 2 : Module.End (ZMod 2) (SectionSpace V E))
  change orderOf (f y).1 = 3 at hy
  change (f y).2 = 1 at hy2
  change ((lineY Y E).subgroupOf (lineNormalizer E)).map f = _ at hY
  have hy3 : (f y).1 ^ 3 = 1 := (orderOf_eq_prime_iff.mp hy).1
  have hyne : (f y).1 ≠ 1 := by
    intro he
    rw [he, orderOf_one] at hy
    contradiction
  have hf3 : f y ^ 3 = 1 := by
    apply Prod.ext
    · exact hy3
    · change (f y).2 ^ 3 = 1
      rw [hy2, one_pow]
  have ht3 : t ^ 3 = 1 := by
    have he : t = r (f y) := (markedRepresentation_apply V E d hcomm y).symm
    rw [he, ← map_pow, hf3, map_one]
  have hNt : N * t = N := by
    dsimp only [N]
    rw [add_mul, add_mul, one_mul, ← pow_succ, ← pow_two, ht3]
    abel
  have hNt2 : N * (t * t) = N := by rw [← mul_assoc, hNt, hNt]
  have hr (g : lineNormalizer E) : r (f g) = sectionRepresentation V E g :=
    markedRepresentation_apply V E d hcomm g
  have hkill (a : lineNormalizer E) (ha : (a : G) ∈ lineY Y E) :
      N * sectionRepresentation V E a = N := by
    have hm : f a ∈ ((lineY Y E).subgroupOf (lineNormalizer E)).map f :=
      mem_map_of_mem f (show a ∈ (lineY Y E).subgroupOf (lineNormalizer E) from ha)
    rw [hY] at hm
    have hc : (f a).1 = 1 ∨ (f a).1 = (f y).1 ∨ (f a).1 = (f y).1 * (f y).1 :=
      alternating_three_cases (f y).1 (f a).1 hy3 hyne
        (Equiv.Perm.mem_alternatingGroup.mp hm.1)
    have hs : (f a).2 = 1 := hm.2
    rcases hc with hc | hc | hc
    · have he : f a = 1 := Prod.ext hc hs
      rw [← markedRepresentation_apply V E d hcomm a]
      change N * r (f a) = N
      rw [he, map_one, mul_one]
    · have he : f a = f y := Prod.ext hc (hs.trans hy2.symm)
      rw [← markedRepresentation_apply V E d hcomm a]
      change N * r (f a) = N
      rw [he, hr]
      exact hNt
    · have he : f a = f (y * y) := by
        rw [map_mul]
        apply Prod.ext hc
        change (f a).2 = (f y).2 * (f y).2
        rw [hs, hy2, one_mul]
      rw [← markedRepresentation_apply V E d hcomm a]
      change N * r (f a) = N
      rw [he, hr, map_mul]
      exact hNt2
  let k := ((N.comp (sectionProjection V E)).toAddMonoidHom.toMultiplicativeRight).ker
  have hUK : lineV V E ≤ k.map (lineV V E).subtype := by
    conv_lhs => rw [hmove, commutator_comm]
    apply commutator_le.mpr
    intro a ha u hu
    let an : lineNormalizer E := ⟨a, (lineY_le Y E ha).2⟩
    let v : Additive (lineV V E) := Additive.ofMul ⟨u, hu⟩
    let w := spanRepresentation V E an v - v
    refine ⟨w.toMul, ?_, ?_⟩
    · change N (sectionProjection V E w) = 0
      change N (sectionProjection V E (spanRepresentation V E an v - v)) = 0
      rw [map_sub, ← sectionRepresentation_projection, map_sub]
      exact sub_eq_zero.mpr (LinearMap.congr_fun (hkill an ha) (sectionProjection V E v))
    · change a * u * a⁻¹ / u = ⁅a, u⁆
      rw [div_eq_mul_inv]
      rfl
  obtain ⟨v, rfl⟩ := sectionProjection_surjective V E x
  obtain ⟨w, hw, he⟩ := hUK v.toMul.property
  have hwv : w = v.toMul := Subtype.ext he
  subst w
  change N (sectionProjection V E v) = 0 at hw
  simpa only [N, t, LinearMap.add_apply, Module.End.one_apply, pow_two, map_mul,
    Module.End.mul_apply] using hw
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LocalStructure.PairedModule.SourceAction
