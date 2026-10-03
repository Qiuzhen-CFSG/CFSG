module

public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.Tactic
public import Theory.GroupTheory.WreathTwoOddInverter
public import Theory.Representation.InvertedOddSubgroup

open scoped IsMulCommutative

namespace Stellmacher.SectionOne

public theorem faithful_binary_card_ge_sixteen_of_nine_dvd
    {X V : Type*} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (faithful : fixingSubgroup X (Set.univ : Set V) = ⊥)
    (nine_dvd : 9 ∣ Nat.card X) :
    16 ≤ Nat.card V := by
  classical
  let representation := Representation.ofElementaryAbelianAction (A := X) (G := V) (p := 2)
  have representation_injective : Function.Injective representation.asGroupHom := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply le_antisymm _ bot_le
    intro element member
    have acts_trivially : representation element = 1 :=
      congrArg Units.val (MonoidHom.mem_ker.mp member)
    apply faithful.le
    rw [mem_fixingSubgroup_iff]
    intro vector _
    apply Additive.ofMul.injective
    exact LinearMap.congr_fun acts_trivially (Additive.ofMul vector)
  let dimension := Module.finrank (ZMod 2) (Additive V)
  have card_eq : Nat.card V = 2 ^ dimension := by
    have card_eq := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    exact (Nat.card_congr Additive.toMul).symm.trans
      (by simpa only [Nat.card_zmod] using card_eq)
  let basis := Module.finBasis (ZMod 2) (Additive V)
  let matrixRepresentation : X →* Matrix.GeneralLinearGroup (Fin dimension) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.toMonoidHom.comp
      representation.asGroupHom
  have matrix_injective : Function.Injective matrixRepresentation :=
    (Matrix.GeneralLinearGroup.toLin' basis).symm.injective.comp representation_injective
  have card_dvd := nine_dvd.trans
    (Subgroup.card_dvd_of_injective matrixRepresentation matrix_injective)
  rw [Matrix.card_GL_field] at card_dvd
  norm_num only [ZMod.card] at card_dvd
  have dimension_ge : 4 ≤ dimension := by
    suffices bound : ∀ count : ℕ,
        9 ∣ ∏ index : Fin count, (2 ^ count - 2 ^ index.val) → 4 ≤ count from
      bound dimension card_dvd
    intro count divides
    by_contra too_small
    have count_le : count ≤ 3 := by omega
    interval_cases count <;> norm_num [Fin.prod_univ_succ] at divides
  rw [card_eq]
  exact (show 16 = 2 ^ 4 by norm_num).le.trans
    (Nat.pow_le_pow_right (by decide : 0 < 2) dimension_ge)

universe u

public theorem wreath_card_sixteen_of_small_quadratic_displacement
    {X V : Type u} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction X V]
    (model : Nonempty (X ≃* Stellmacher.Later.SL2TwoWreathC2))
    (faithful : fixingSubgroup X (Set.univ : Set V) = ⊥)
    (sylow : Sylow 2 X) (actor : Subgroup X)
    (actor_le : actor ≤ (sylow : Subgroup X))
    (actor_normal : (actor.subgroupOf (sylow : Subgroup X)).Normal)
    (actor_elementary : IsElementaryAbelian 2 actor)
    (actor_card : Nat.card actor = 4)
    (fixed : FixedPoints.subgroup (oddCore X) V = ⊥)
    (quadratic : commutatorAction₂ actor V = ⊥)
    (displacement : Nat.card (commutatorAction actor V) ≤ 4) :
    Nat.card V = 16 := by
  have _quadratic := quadratic
  obtain ⟨hcore_card, x, hxactor, hxinv, hxodd⟩ :=
    Theory.GroupTheory.wreathTwo_exists_actor_oddCore_inverter model sylow actor
      actor_le actor_normal actor_elementary actor_card
  have hdiv : 9 ∣ Nat.card X := by
    rw [← hcore_card]
    exact (oddCore X).card_subgroup_dvd_card
  have hlow := faithful_binary_card_ge_sixteen_of_nine_dvd faithful hdiv
  have hodd : Odd (Nat.card (oddCore X)) := by
    rw [hcore_card]
    norm_num
  have hinv_subtype : ∀ a : oddCore X, x * (a : X) * x⁻¹ = (a : X)⁻¹ := hxodd
  have hsq := invertedOddSubgroup_card_eq_commutator_sq (oddCore X) hodd x hxinv
    hinv_subtype fixed
  have hzpow_le : Subgroup.zpowers x ≤ actor := by
    intro z hz
    rcases hz with ⟨n, rfl⟩
    exact actor.zpow_mem hxactor n
  have hcomm_le : commutatorAction (Subgroup.zpowers x) V ≤ commutatorAction actor V := by
    rw [commutatorAction_eq_closure]
    refine (Subgroup.closure_le (K := commutatorAction actor V)).2 ?_
    rintro z ⟨a, v, rfl⟩
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨⟨a, hzpow_le a.property⟩, v, rfl⟩
  have hupper_comm : Nat.card (commutatorAction (Subgroup.zpowers x) V) ≤ 4 :=
    (Subgroup.card_le_of_le hcomm_le).trans displacement
  have hupper : Nat.card V ≤ 16 := by
    rw [hsq]
    nlinarith
  exact Nat.le_antisymm hupper hlow

end Stellmacher.SectionOne
