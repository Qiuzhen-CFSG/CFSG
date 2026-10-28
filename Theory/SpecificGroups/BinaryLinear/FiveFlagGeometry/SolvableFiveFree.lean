module
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.SylowOvergroups
public import Theory.SpecificGroups.BinaryLinear.FiveFlagGeometry.Residuals
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Theory.GroupTheory.SolvableNormalSup

/-!
# Five-free solvable Sylow overgroups in binary dimension five

Every full Sylow two-subgroup overgroup in GL₅(2) is an actual flag
stabilizer. A proper flag stabilizer whose order is divisible by five is
an endpoint parabolic, and both endpoint parabolics are perfect. The whole
group is perfect as well. Thus a solvable Sylow overgroup has order prime
to five. In particular no subgroup normalized by a full Sylow can have
two-core quotient of order five: adjoining that Sylow would give a solvable
Sylow overgroup with a factor five in its order.

The proof uses the complete binary flag-overgroup theorem and the existing
endpoint perfectness calculations, with no extra geometric premise.
Source: Aschbacher--Smith, A.3.12, printed pp.47--48, and the original15.2.4
model comparison on printed p.1107.
-/

public section
open Subgroup
namespace BinaryLinear.FiveFlagGeometry
open OuterCyclic

private instance : Finite (LinearGroup 5) :=
  Finite.of_injective (fun g : LinearGroup 5 => (g : Space 5 → Space 5))
    DFunLike.coe_injective

private theorem perfect_of_five_dvd (P : Sylow 2 (LinearGroup 5))
    (H : Subgroup (LinearGroup 5)) (hPH : (P : Subgroup (LinearGroup 5)) ≤ H)
    (hfive : 5 ∣ Nat.card H) : Group.IsPerfect H := by
  by_cases ht : H = ⊤
  · subst H
    let : Group.IsPerfect (LinearGroup 5) := linearGroup_isPerfect 5 (by decide)
    exact Group.IsPerfect.ofSurjective (f := (topEquiv (G := LinearGroup 5)).symm.toMonoidHom)
      (topEquiv (G := LinearGroup 5)).symm.surjective
  obtain ⟨b,cuts,rfl⟩ := isFlagParabolic_of_sylow_le P H hPH
  rcases cuts_eq_singleton_end_of_five_dvd b cuts ht hfive with rfl | rfl
  · rw [flagStabilizer_singleton,flagSpace_zero]
    exact pointParabolic_isPerfect (b.ne_zero 0)
  · have hf : b.coord 4 ≠ 0 := by
      intro he
      have hh := LinearMap.congr_fun he (b 4)
      simp [Module.Basis.coord_apply] at hh
    rw [flagStabilizer_singleton,flagSpace_last]
    exact hyperplaneParabolic_isPerfect hf

/-- A solvable overgroup of a full Sylow two-subgroup in GL₅(2) has order
prime to five. -/
theorem solvable_sylow_overgroup_five_free
    (P : Sylow 2 (LinearGroup 5)) (H : Subgroup (LinearGroup 5))
    [Group.IsSolvable H] (hPH : (P : Subgroup (LinearGroup 5)) ≤ H) :
    ¬ 5 ∣ Nat.card H := by
  intro hfive
  let : Group.IsPerfect H := perfect_of_five_dvd P H hPH hfive
  let : Nontrivial H := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 5) (Nat.le_of_dvd Nat.card_pos hfive))
  exact Group.IsPerfect.not_isSolvable H inferInstance

private theorem solvable_five_section {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (A ⧸ pCore 2 A) = 5) : Group.IsSolvable A := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Group.IsNilpotent (pCore 2 A) := (pCore_isPGroup (p := 2) (G := A)).isNilpotent
  have hp : IsPGroup 5 (A ⧸ pCore 2 A) := IsPGroup.of_card (n := 1) (by simpa using hc)
  let : Group.IsNilpotent (A ⧸ pCore 2 A) := hp.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr ⟨inferInstance,inferInstance⟩

private theorem solvable_normalized_sup {A : Type*} [Group A]
    (B S : Subgroup A) [Group.IsSolvable B] [Group.IsSolvable S]
    (hn : S ≤ normalizer (B : Set A)) : Group.IsSolvable (B ⊔ S : Subgroup A) := by
  let D := B ⊔ S
  let : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le B.le_normalizer hn)
  let : Group.IsSolvable (B.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).injective
  let : Group.IsSolvable (S.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (B.subgroupOf D) (S.subgroupOf D)
    (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])

/-- No subgroup normalized by a full Sylow two-subgroup of GL₅(2) has
two-core quotient of order five. -/
theorem no_normalized_five_section
    (P : Sylow 2 (LinearGroup 5)) (B : Subgroup (LinearGroup 5))
    (hn : (P : Subgroup (LinearGroup 5)) ≤ normalizer (B : Set (LinearGroup 5)))
    (hc : Nat.card (B ⧸ pCore 2 B) = 5) : False := by
  let : Group.IsSolvable B := solvable_five_section hc
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (P : Subgroup (LinearGroup 5)) : Subgroup (LinearGroup 5)) :=
    solvable_normalized_sup B P hn
  have hd : 5 ∣ Nat.card B := by
    have hh := (pCore 2 B).index_dvd_card
    rwa [Subgroup.index_eq_card,hc] at hh
  exact solvable_sylow_overgroup_five_free P _ le_sup_right
    (hd.trans (card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup (LinearGroup 5)) from le_sup_left)))

end BinaryLinear.FiveFlagGeometry
