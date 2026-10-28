module
public import Theory.SpecificGroups.SL2.TwoSubgroupExponent
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient

/-!
# The binary-three quotient obstruction in rank one

A group mapping onto SL₃(2) cannot have a representation in binary SL₂
with a two-group kernel. The latter kernel is killed by the quotient map,
and every two-subgroup of binary SL₂ has exponent two. Surjective Sylow
transport would make an explicit order-four element of SL₃(2) square to one.
The same obstruction applies when the target has binary SL₂ two-core quotient.

Source application: Aschbacher--Smith 10.2.6, printed pp.748--749,
the binary-three row of the A.3.12/C.2.7 comparison.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup

private theorem binary_three_core : pCore 2 SL(3,ZMod 2) = ⊥ := by
  apply Subgroup.map_injective (f := Matrix.PSL3Two.equiv.toMonoidHom)
    Matrix.PSL3Two.equiv.injective
  rw [pCore_map_iso, Matrix.PSL3Two.pCore_two_PSL_eq_bot, Subgroup.map_bot]

private def binaryThreeFour : SL(3,ZMod 2) :=
  ⟨!![1,1,0;0,1,1;0,0,1], by decide⟩

private theorem binaryThreeFour_square : binaryThreeFour ^ 2 ≠ 1 := by decide
private theorem binaryThreeFour_four : binaryThreeFour ^ 4 = 1 := by decide

/-- Two-group kernels cannot hide the order-four obstruction when all target two-subgroups have exponent two. -/
theorem no_binary_three_quotient_of_two_subgroup_exponent
    {A X : Type*} [Group A] [Finite A] [Group X]
    (hX : ∀ (P : Subgroup X), IsPGroup 2 P → ∀ x : P, x ^ 2 = 1)
    (π : A →* SL(3,ZMod 2)) (hπ : Function.Surjective π)
    (f : A →* X) (hf : IsPGroup 2 f.ker) : False := by
  have hcore : pCore 2 A ≤ π.ker := by
    have hn : ((pCore 2 A).map π).Normal := Subgroup.Normal.map inferInstance π hπ
    have hm : (pCore 2 A).map π ≤ pCore 2 SL(3,ZMod 2) :=
      le_sSup ⟨hn,pCore_isPGroup.map π⟩
    rw [binary_three_core] at hm
    exact (Subgroup.map_eq_bot_iff _).mp (bot_unique hm)
  have hker : f.ker ≤ π.ker := (le_sSup ⟨inferInstance,hf⟩ : f.ker ≤ pCore 2 A).trans hcore
  have hc : IsPGroup 2 (zpowers binaryThreeFour) := by
    apply IsPGroup.of_card_dvd_pow (n := 2)
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one binaryThreeFour_four
  obtain ⟨Q,hQ⟩ := hc.exists_le_sylow
  obtain ⟨P,hP⟩ := Sylow.mapSurjective_surjective hπ 2 Q
  have hx : binaryThreeFour ∈ (P : Subgroup A).map π := by
    change binaryThreeFour ∈ (P.mapSurjective hπ : Subgroup _)
    rw [hP]
    exact hQ (mem_zpowers _)
  obtain ⟨a,ha,he⟩ := hx
  have hs : f (a ^ 2) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val (hX ((P : Subgroup A).map f)
      (P.isPGroup'.map f) ⟨f a,mem_map_of_mem f ha⟩)
  have hz := MonoidHom.mem_ker.mp (hker (MonoidHom.mem_ker.mpr hs))
  rw [map_pow,he] at hz
  exact binaryThreeFour_square hz

/-- A binary rank-one representation with two-group kernel cannot coexist with this quotient. -/
theorem no_binary_three_quotient_of_two_kernel
    {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]
    (π : A →* SL(3,ZMod 2)) (hπ : Function.Surjective π)
    (f : A →* SL(2,F)) (hf : IsPGroup 2 f.ker) : False :=
  no_binary_three_quotient_of_two_subgroup_exponent twoSubgroup_pow_two π hπ f hf

/-- The obstruction survives an additional two-core in the rank-one target. -/
theorem no_binary_three_quotient_of_binary_core_quotient
    {A X F : Type*} [Group A] [Finite A] [Group X] [Field F] [Finite F] [CharP F 2]
    (π : A →* SL(3,ZMod 2)) (hπ : Function.Surjective π)
    (f : A →* X) (hf : IsPGroup 2 f.ker)
    (e : (X ⧸ pCore 2 X) ≃* SL(2,F)) : False := by
  let g := e.toMonoidHom.comp ((QuotientGroup.mk' (pCore 2 X)).comp f)
  apply no_binary_three_quotient_of_two_kernel π hπ g
  have he : g.ker = (pCore 2 X).comap f := by
    ext a
    change e (QuotientGroup.mk' (pCore 2 X) (f a)) = 1 ↔ f a ∈ pCore 2 X
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff (f a)
  rw [he]
  exact pCore_isPGroup.comap_of_ker_isPGroup f hf

end Matrix.SpecialLinearGroup
