module

public import Theory.GroupTheory.QuaternionCentralProductIndependentCubics
public import Theory.GroupTheory.QuaternionCentralProductEightCensus

/-!
# Cubic stabilizers of elementary eights

Conjugation by the nine independent cubic actors permutes the elementary
eights in the quaternion central product. The census bounds this family by
six members, so two actors have the same image of any chosen eight. Their
quotient is a nonidentity actor normalizing it.

This is the counting step of the intrinsic quaternion-product geometry used
in Stellmacher (8.6)(a), `refs/latex/stellmacher-n-group.tex`.
-/

namespace Subgroup

private theorem exists_nontrivial_normalizing_of_small_family
    {G : Type*} [Group G] [Finite G] (A U : Subgroup G)
    (P : Subgroup G → Prop)
    (hP : ∀ a : A, P (U.map (MulAut.conj (a : G)).toMonoidHom))
    (hcard : Nat.card {V : Subgroup G // P V} < Nat.card A) :
    ∃ a : A, a ≠ 1 ∧ (a : G) ∈ normalizer (U : Set G) := by
  classical
  let f : A → {V : Subgroup G // P V} :=
    fun a => ⟨U.map (MulAut.conj (a : G)).toMonoidHom, hP a⟩
  have hninj : ¬ Function.Injective f := by
    intro hinj
    exact (Nat.not_le_of_lt hcard) (Nat.card_le_card_of_injective f hinj)
  obtain ⟨a, b, hab, hne⟩ := Function.not_injective_iff.mp hninj
  refine ⟨b⁻¹ * a, ?_, ?_⟩
  · intro h
    apply hne
    calc
      a = b * (b⁻¹ * a) := by group
      _ = b := by rw [h, mul_one]
  · apply mem_normalizer_iff_map_conj_eq.mpr
    have heq : U.map (MulAut.conj (a : G)).toMonoidHom =
        U.map (MulAut.conj (b : G)).toMonoidHom := congrArg Subtype.val hab
    have hcomp (x y : G) :
        (MulAut.conj x).toMonoidHom.comp (MulAut.conj y).toMonoidHom =
          (MulAut.conj (x * y)).toMonoidHom := by
      ext z
      change x * (y * z * y⁻¹) * x⁻¹ = (x * y) * z * (x * y)⁻¹
      group
    have hh := congrArg (fun V : Subgroup G =>
      V.map (MulAut.conj (b : G)⁻¹).toMonoidHom) heq
    have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext z
      simp
    simp only [map_map, hcomp, inv_mul_cancel, hone, map_id] at hh
    exact hh

/-- A bound on the number of elementary eights supplies a nontrivial cubic
actor normalizing every actual elementary eight in the central product. -/
public theorem QuaternionIndependentCubics.exists_nontrivial_normalizing_of_card_lt
    {G : Type*} [Group G] [Finite G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C) (U : Subgroup G)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUQ : U ≤ B ⊔ C)
    (hcount : Nat.card {V : Subgroup G //
      V ≤ B ⊔ C ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 8} < 9) :
    ∃ a : actors.A, a ≠ 1 ∧ (a : G) ∈ normalizer (U : Set G) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply exists_nontrivial_normalizing_of_small_family actors.A U
    (fun V => V ≤ B ⊔ C ∧ IsElementaryAbelian 2 V ∧ Nat.card V = 8)
  · intro a
    refine ⟨?_, IsElementaryAbelian.map _, ?_⟩
    · calc
        U.map (MulAut.conj (a : G)).toMonoidHom ≤
            (B ⊔ C).map (MulAut.conj (a : G)).toMonoidHom := map_mono hUQ
        _ = B ⊔ C := mem_normalizer_iff_map_conj_eq.mp
          (actors.le_normalizer a.property)
    · rw [card_map_of_injective (MulAut.conj (a : G)).injective, hU]
  · simpa only [actors.card] using hcount

/-- Every elementary eight in a quaternion central product is normalized by
a nonidentity member of any independent cubic actor group. -/
public theorem QuaternionIndependentCubics.exists_nontrivial_normalizing
    {G : Type*} [Group G] [Finite G] {B C : Subgroup G}
    (actors : QuaternionIndependentCubics B C)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (U : Subgroup G) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 8) (hUQ : U ≤ B ⊔ C) :
    ∃ a : actors.A, a ≠ 1 ∧ (a : G) ∈ normalizer (U : Set G) :=
  actors.exists_nontrivial_normalizing_of_card_lt U hU hUQ
    (card_elementary_eights_lt_nine_of_quaternion_factors B C hB hC hinter hcomm)

end Subgroup
