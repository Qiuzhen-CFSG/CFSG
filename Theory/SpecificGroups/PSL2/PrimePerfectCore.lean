module

public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.SL2.OddProjectiveNonsolvable
public import Theory.PGroupCore
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Two-cores of perfect subgroups of prime-field PSL₂

A nontrivial perfect subgroup is nonsolvable. The proved prime-field
Dickson classification identifies a proper such subgroup with A₅. For the
whole group, nonsolvability excludes the field of order three, and PSL₂
is simple. Hence every nontrivial perfect subgroup is simple, and its
normal two-core is trivial: otherwise the whole perfect group would be
nilpotent and solvable. The homomorphism form retains the literal source
kernel and applies to central covers.

Source: Huppert II.8.27 and Aschbacher–Smith C.3.3, printed p.149.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Theory.PSL2

/-- Every nontrivial perfect subgroup of odd prime-field PSL₂ is simple. -/
theorem prime_perfect_subgroup_isSimple
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    (P : Subgroup PSL(2,F)) [Group.IsPerfect P] [Nontrivial P] :
    IsSimpleGroup P := by
  have hn := Group.IsPerfect.not_isSolvable P
  by_cases ht : P = ⊤
  · have hlarge := ProjectiveSpecialLinearGroup.card_gt_three_of_odd_of_not_isSolvable
      (hF ▸ ho) (by
        intro hs
        let := hs
        exact hn inferInstance)
    let : IsSimpleGroup PSL(2,F) := ProjectiveSpecialLinearGroup.rank_two_simple hlarge
    exact ((MulEquiv.subgroupCongr ht).trans Subgroup.topEquiv).isSimpleGroup
  · obtain ⟨_, _, ⟨e⟩⟩ :=
      Theory.PSL2.prime_nonsolvable_proper_is_alternating_five ho hF P ht hn
    let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup

/-- Every perfect subgroup has trivial two-core, including the small prime three. -/
theorem prime_perfect_subgroup_twoCore_eq_bot {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    (P : Subgroup PSL(2,F)) [Group.IsPerfect P] : pCore 2 P = ⊥ := by
  by_cases hP : P = ⊥
  · subst P
    exact Subsingleton.elim _ _
  let : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hP
  let : IsSimpleGroup P := prime_perfect_subgroup_isSimple ho hF P
  rcases (inferInstance : (pCore 2 P).Normal).eq_bot_or_eq_top with hbot | htop
  · exact hbot
  · have htwo : IsPGroup 2 P := by
      have ht : IsPGroup 2 (⊤ : Subgroup P) := htop ▸ pCore_isPGroup
      exact ht.of_equiv Subgroup.topEquiv
    let : Group.IsNilpotent P := htwo.isNilpotent
    exact (Group.IsPerfect.not_isSolvable P inferInstance).elim

/-- A homomorphism from a perfect group kills its two-core in odd prime-field PSL₂. -/
theorem prime_perfect_hom_twoCore_le_ker {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p)
    {A : Type*} [Group A] [Group.IsPerfect A] (f : A →* PSL(2,F)) :
    pCore 2 A ≤ f.ker := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have h : (pCore 2 A).map f.rangeRestrict ≤ pCore 2 f.range :=
    le_sSup ⟨(inferInstance : (pCore 2 A).Normal).map f.rangeRestrict f.rangeRestrict_surjective,
      pCore_isPGroup.map f.rangeRestrict⟩
  rw [prime_perfect_subgroup_twoCore_eq_bot ho hF f.range] at h
  have hk := (Subgroup.map_eq_bot_iff _).mp (bot_unique h)
  intro a ha
  exact congrArg Subtype.val (hk ha)

end Theory.PSL2
