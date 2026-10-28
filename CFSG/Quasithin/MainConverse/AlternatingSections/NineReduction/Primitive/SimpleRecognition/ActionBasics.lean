module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveNormal
public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Action reductions for the simple degree-nine recognition problem

A nontrivial normal subgroup of a faithful primitive group is transitive.
In degree nine a simple transitive group is primitive: a nontrivial block
system has three blocks, and simplicity would embed the group into S₃,
contradicting the factor nine in its order. A seven-cycle then gives triple
transitivity by Jordan's multiple-primitivity criterion. Jordan's
three-cycle theorem also excludes three-cycles from a proper primitive
subgroup of A₉.

These are reductions for condition K in the alternating case of
Aschbacher–Smith, Theorem 0.1.2(3), printed pp.4 and 482. They do not assert
that seven divides the order or that a three-point stabilizer is trivial.
Those are the remaining inputs to `SimpleRecognition`.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction
open MulAction Equiv
open scoped Pointwise

/-- A simple transitive group of degree nine is primitive. -/
public theorem simple_preprimitive_of_pretransitive_nine
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    [MulAction G (Fin 9)] [IsPretransitive G (Fin 9)] :
    IsPreprimitive G (Fin 9) := by
  classical
  have hnine : 9 ∣ Nat.card G := by
    have hi : (stabilizer G (0 : Fin 9)).index = 9 := by
      simpa using index_stabilizer_of_transitive G (0 : Fin 9)
    exact hi ▸ (stabilizer G (0 : Fin 9)).index_dvd_card
  refine { isTrivialBlock_of_isBlock := ?_ }
  intro B hB
  by_cases hs : B.Subsingleton
  · exact Or.inl hs
  by_cases hu : B = Set.univ
  · exact Or.inr hu
  have hb2 : 2 ≤ B.ncard := by
    have : ¬ B.ncard ≤ 1 := by simpa only [Set.ncard_le_one_iff_subsingleton] using hs
    omega
  have hb9 : B.ncard < 9 := by
    have hb := B.ncard_le_card
    have hbne : B.ncard ≠ 9 := by
      intro he
      apply hu
      apply B.eq_univ_iff_ncard.mpr
      simpa using he
    simp only [Nat.card_fin] at hb
    omega
  have hBne : B.Nonempty := (Set.ncard_pos (Set.toFinite B)).mp (by omega)
  have hm := hB.ncard_block_mul_ncard_orbit_eq hBne
  simp only [Nat.card_fin] at hm
  have horbit : Nat.card (orbit G B) = 3 := by
    change (orbit G B).ncard = 3
    interval_cases hb : B.ncard <;> omega
  let a := toPermHom G (orbit G B)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal a.ker inferInstance with hk | hk
  · have hinj := a.ker_eq_bot_iff.mp hk
    have hd := Subgroup.card_dvd_of_injective a hinj
    rw [Nat.card_perm, horbit] at hd
    have hbad := hnine.trans hd
    norm_num [Nat.factorial] at hbad
  · have hBfixed (g : G) : g • B = B := by
      have hg : a g = 1 := by
        apply a.mem_ker.mp
        rw [hk]
        trivial
      exact congrArg (fun p : Perm (orbit G B) => (p ⟨B, mem_orbit_self B⟩).val) hg
    apply (hu ?_).elim
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨b, hb⟩ := hBne
    obtain ⟨g, rfl⟩ := exists_smul_eq G b x
    rw [← hBfixed g]
    exact Set.smul_mem_smul_set hb

/-- A simple normal subgroup in the given primitive action is transitive. -/
public theorem primitive_simple_normal_pretransitive
    (H : Subgroup (alternatingGroup (Fin 9)))
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N] :
    IsPretransitive N (Fin 9) := by
  let := hp
  exact Atlas.GroupTheory.normal_pretransitive N
    ((Subgroup.nontrivial_iff_ne_bot N).mp inferInstance)

/-- In degree nine the simple normal subgroup itself acts primitively. -/
public theorem primitive_simple_normal_preprimitive
    (H : Subgroup (alternatingGroup (Fin 9)))
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N] :
    IsPreprimitive N (Fin 9) := by
  let := primitive_simple_normal_pretransitive H hp N
  exact simple_preprimitive_of_pretransitive_nine

private theorem primitive_nine_perm_three_pretransitive_of_seven
    (U : Subgroup (Perm (Fin 9)))
    (hp : IsPreprimitive U (Fin 9)) (hseven : 7 ∣ Nat.card U) :
    IsMultiplyPretransitive U (Fin 9) 3 := by
  classical
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 hseven
  have hgo : orderOf (g : Perm (Fin 9)) = 7 := by
    simpa using hg
  have hgc : (g : Perm (Fin 9)).IsCycle :=
    Perm.isCycle_of_prime_order' (hgo ▸ by decide) (by simp; omega)
  have hsupp : (g : Perm (Fin 9)).support.card = 7 := hgc.orderOf.symm.trans hgo
  have hsc : ((g : Perm (Fin 9)).supportᶜ : Set (Fin 9)).ncard = 1 + 1 := by
    have := Set.ncard_add_ncard_compl ((g : Perm (Fin 9)).support : Set (Fin 9))
    simp only [Set.ncard_coe_finset, hsupp, Nat.card_fin] at this
    omega
  have := Perm.isPretransitive_of_isCycle_mem hgc g.property
  have hprim : IsPreprimitive
      (fixingSubgroup U ((g : Perm (Fin 9)).supportᶜ : Set (Fin 9)))
      (SubMulAction.ofFixingSubgroup U ((g : Perm (Fin 9)).supportᶜ : Set (Fin 9))) := by
    apply IsPreprimitive.of_prime_card
    convert Nat.prime_seven using 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [← hsupp]
    apply congr_arg Finset.card
    ext x
    simp [SubMulAction.mem_ofFixingSubgroup_iff]
  exact (hp.isMultiplyPreprimitive hsc (by norm_num) hprim).isMultiplyPretransitive

/-- A factor seven forces triple transitivity in a faithful primitive nine-point action. -/
public theorem primitive_nine_three_pretransitive_of_seven
    {G : Type*} [Group G] [Finite G]
    [MulAction G (Fin 9)] [FaithfulSMul G (Fin 9)]
    (hp : IsPreprimitive G (Fin 9)) (hseven : 7 ∣ Nat.card G) :
    IsMultiplyPretransitive G (Fin 9) 3 := by
  let f := toPermHom G (Fin 9)
  let e : G ≃* f.range := MonoidHom.ofInjective toPerm_injective
  let X : Fin 9 →ₑ[e.toMonoidHom] Fin 9 :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  have hpU : IsPreprimitive f.range (Fin 9) :=
    (isPreprimitive_congr (f := X) e.surjective Function.bijective_id).mp hp
  have hs : 7 ∣ Nat.card f.range := (Nat.card_congr e.toEquiv) ▸ hseven
  have hthree := primitive_nine_perm_three_pretransitive_of_seven f.range hpU hs
  exact (IsPretransitive.of_embedding_congr (n := Fin 3) (f := X)
    e.surjective Function.bijective_id).mpr hthree

/-- The seven-divisibility input upgrades the simple normal subgroup to triple transitivity. -/
public theorem primitive_simple_normal_three_pretransitive_of_seven
    (H : Subgroup (alternatingGroup (Fin 9)))
    (hp : IsPreprimitive H (Fin 9))
    (N : Subgroup H) [N.Normal] [IsSimpleGroup N]
    (hseven : 7 ∣ Nat.card N) : IsMultiplyPretransitive N (Fin 9) 3 :=
  primitive_nine_three_pretransitive_of_seven
    (primitive_simple_normal_preprimitive H hp N) hseven

/-- A proper primitive subgroup of A₉ contains no three-cycle. -/
public theorem primitive_nine_not_isThreeCycle
    (H : Subgroup (alternatingGroup (Fin 9))) (hH : H ≠ ⊤)
    (hp : IsPreprimitive H (Fin 9)) (g : H) :
    ¬ Perm.IsThreeCycle (g.val.val : Perm (Fin 9)) := by
  intro hg
  let i := (alternatingGroup (Fin 9)).subtype
  let U := H.map i
  let e : H ≃* U := H.equivMapOfInjective i (alternatingGroup (Fin 9)).subtype_injective
  let X : Fin 9 →ₑ[e.toMonoidHom] Fin 9 :=
    { toFun := id, map_smul' := fun _ _ => rfl }
  have hpU : IsPreprimitive U (Fin 9) :=
    (isPreprimitive_congr (f := X) e.surjective Function.bijective_id).mp hp
  have hle : alternatingGroup (Fin 9) ≤ U :=
    Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hpU hg
      ⟨g.val, g.property, rfl⟩
  apply hH
  apply top_unique
  intro a _
  obtain ⟨b, hb, he⟩ := hle a.property
  exact ((alternatingGroup (Fin 9)).subtype_injective he) ▸ hb

end CFSG.Quasithin.MainConverse.NineReduction
