module
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.SylowNormalizerTorusAction
public import Theory.GroupTheory.NormalizedSupConsequences
public import Theory.FieldTheory.CubicDisplacement
public import Mathlib.GroupTheory.IsPerfect

/-!
# A contained cubic and the binary rank-one Borel

In a finite perfect cover of characteristic-two SL₂, a solvable subgroup
normalized by a Sylow two-subgroup lies in its actual Sylow normalizer.
The join is solvable and hence proper, so rank-one Borel separation applies
through the specified two-group kernel.

On the field-unit quotient, an inverted cubic with a fixed supplement
forces every field-automorphism displacement to have cube one. Cubic
rigidity bounds the field order by four: identity would both fix and
invert a nontrivial cubic. Neither a chosen Hall complement nor an
involutory assumption on the original actor is needed.

Source application: Aschbacher–Smith 14.7.41, the contained L₂(q) case,
printed p.1061, refs/quasithin.pdf.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Solvability places the specified Sylow-normalized subgroup in its Borel. -/
theorem solvable_sylow_normalized_le_normalizer
    [Group.IsPerfect G] (q : G →* SL(2,F)) (hq : Function.Surjective q)
    (P : Sylow 2 G) (hk : q.ker ≤ (P : Subgroup G))
    (A : Subgroup G) [Group.IsSolvable A]
    (hn : (P : Subgroup G) ≤ normalizer (A : Set G)) :
    A ≤ normalizer (P : Set G) := by
  let : Group.IsPerfect SL(2,F) := Group.IsPerfect.ofSurjective hq
  let : Nontrivial SL(2,F) := by
    let t := transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1 : F)
    refine ⟨⟨t,1,?_⟩⟩
    intro he
    have hh := congrArg (fun g : SL(2,F) => g.val 0 1) he
    simp [t,transvection_coe] at hh
  let := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (A ⊔ (P : Subgroup G) : Subgroup G) :=
    Group.isSolvable_sup_of_normalizes A P hn
  have hp : A ⊔ (P : Subgroup G) ≠ ⊤ := by
    intro he
    have hs : Group.IsSolvable (⊤ : Subgroup G) := he ▸ inferInstanceAs
      (Group.IsSolvable (A ⊔ (P : Subgroup G) : Subgroup G))
    let := hs
    let : Group.IsSolvable G := Group.isSolvable_of_surjective
      (f := (topEquiv (G := G)).toMonoidHom) (topEquiv (G := G)).surjective
    exact Group.IsPerfect.not_isSolvable SL(2,F) (Group.isSolvable_of_surjective hq)
  exact le_sup_left.trans
    (proper_overgroup_le_sylow_normalizer_of_two_kernel q hq P hk _ le_sup_right hp)
end Matrix.SpecialLinearGroup

namespace FiniteField
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The original inverted cubic and fixed supplement force field order at most four. -/
theorem card_le_four_of_inverted_cubic_fixed_supplement
    (σ : F ≃+* F) (P D : Subgroup Fˣ) (hP : Nat.card P = 3)
    (hgen : P ⊔ D = ⊤)
    (hfix : ∀ d ∈ D, Units.map σ.toMonoidHom d = d)
    (hinv : ∀ p ∈ P, Units.map σ.toMonoidHom p = p⁻¹) :
    Nat.card F ≤ 4 := by
  let δ : Fˣ →* Fˣ := (Units.map σ.toMonoidHom) * (MonoidHom.id _)⁻¹
  have hd (x : Fˣ) : δ x = Units.map σ.toMonoidHom x * x⁻¹ := rfl
  have hle : δ.range ≤ P := by
    rintro _ ⟨x,rfl⟩
    have hx : x ∈ P ⊔ D := hgen ▸ mem_top x
    obtain ⟨p,hp,d,hd',rfl⟩ := mem_sup_of_normal_right.mp hx
    rw [map_mul,hd,hd,hinv p hp,hfix d hd',mul_inv_cancel,mul_one]
    exact P.mul_mem (P.inv_mem hp) (P.inv_mem hp)
  have hc (x : Fˣ) : (Units.map σ.toMonoidHom x * x⁻¹)^3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨δ x,hle ⟨x,rfl⟩⟩ : P))
    rw [hP] at hh
    exact congrArg Subtype.val hh
  refine (eq_one_or_card_le_four_of_unit_displacement_cube σ hc).resolve_left ?_
  intro hσ
  have hbot : P = ⊥ := eq_bot_iff.mpr fun x hx => by
    have hi := hinv x hx
    rw [hσ] at hi
    change x = x⁻¹ at hi
    have htwo : x^2 = 1 := by
      rw [pow_two]
      exact (congrArg (x * ·) hi).trans (mul_inv_cancel _)
    have hthree : x^3 = 1 := by
      have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : P))
      rw [hP] at hh
      exact congrArg Subtype.val hh
    simpa [pow_succ,htwo] using hthree
  have hh := P.eq_bot_iff_card.mp hbot
  omega
end FiniteField
