module
public import Theory.SpecificGroups.Rudvalis.Model.ExtraspecialFive.Relations
public import Theory.SpecificGroups.Rudvalis.Model.Order
public import Theory.GroupTheory.PGroup.HeisenbergPair
public import Theory.GroupTheory.PerfectCentralCoverSimultaneousInversion

/-!
# An actual extraspecial Sylow five-subgroup of Rudvalis

The certified noncommuting ATLAS words satisfy the Heisenberg relations, so
their generated subgroup has order 125 and is extraspecial. The proved model
order makes this literal subgroup Sylow. The certified simultaneous inverter
also excludes five from every finite perfect central kernel over this model.

The G.7 consumer restricts a faithful binary representation through this
actual subgroup and the given ambient-model isomorphism. The perfect-cover
consequence supplies the independent five-primary Ru multiplier calculation.

Source: Aschbacher–Smith G.7.2(6), printed pp.347–348; GLS III Table 5.3r,
printed p.279. The original ATLAS data and discovery attribution are retained
in `ExtraspecialFive/source/README.md`.
-/

namespace Rudvalis.ExtraspecialFive
open Subgroup

@[expose] public def subgroup : Subgroup Model := closure ({x, y} : Set Model)

public theorem card_subgroup : Nat.card subgroup = 5 ^ 3 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact PrimeCubePair.card_closure_pair x y x_fifth y_fifth commutator_fifth
    x_commute_commutator.symm y_commute_commutator.symm xy_ne_yx

public theorem subgroup_not_commutative : ¬ IsMulCommutative subgroup := by
  intro h
  let := h
  exact xy_ne_yx (congrArg Subtype.val
    (IsMulCommutative.is_comm.comm
      (⟨x, subset_closure (by simp)⟩ : subgroup) ⟨y, subset_closure (by simp)⟩))

public theorem subgroup_extraspecial : IsExtraspecial 5 subgroup := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact IsExtraspecial.of_noncommutative_card_prime_cube card_subgroup subgroup_not_commutative

public theorem subgroup_isPGroup : IsPGroup 5 subgroup := IsPGroup.of_card card_subgroup

private theorem not_five_dvd_index : ¬ 5 ∣ subgroup.index := by
  intro h
  have hd : 625 ∣ Nat.card Model := by
    rw [← subgroup.card_mul_index, card_subgroup]
    exact Nat.mul_dvd_mul_left 125 h
  rw [model_card] at hd
  norm_num at hd

/-- The word subgroup is Sylow in the literal degree-4060 carrier. -/
@[expose] public noncomputable def sylow : Sylow 5 Model :=
  letI : Fact (Nat.Prime 5) := ⟨by decide⟩
  subgroup_isPGroup.toSylow (by exact not_five_dvd_index)

public theorem closure_pair_eq_sylow : closure ({x, y} : Set Model) =
    (sylow : Subgroup Model) := rfl

/-- The five-primary part of every finite perfect central kernel over Ru is trivial. -/
public theorem not_five_dvd_card_kernel
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (f : E →* Model) (hf : Function.Surjective f) (hk : f.ker ≤ center E) :
    ¬ 5 ∣ Nat.card f.ker := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact PerfectCentralCovering.not_dvd_card_kernel_of_simultaneous_inversion
    f hf hk (by decide : Nat.Coprime 5 2) sylow x y r closure_pair_eq_sylow
    x_fifth y_fifth commutator_ne_one x_commute_commutator y_commute_commutator
    r_inverts_x r_inverts_y r_commute_commutator

end Rudvalis.ExtraspecialFive
