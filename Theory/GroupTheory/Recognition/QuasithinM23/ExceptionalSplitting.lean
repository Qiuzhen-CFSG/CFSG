module
public import Theory.Representation.BinaryAlternatingSevenFixedPoints
public import Theory.Representation.NormalElementaryQuotient
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model
public import Theory.GroupTheory.Gaschutz
public import Theory.GroupTheory.OddSubgroupLift
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Splitting the original exceptional A₇ extension

A three-cycle acts without nonzero fixed vectors on a faithful binary
four-space. Lift its cyclic subgroup through the actual elementary kernel.
Coprime normalizer lifting and fixed-point-freeness make the lifted normalizer
an internal complement in its product with the kernel. The quotient normalizer
contains a Sylow two-subgroup, so this product has odd index. Gaschütz extends
the complement to the whole group. The resulting section preserves the
supplied quotient map pointwise.

This is the splitting step of Aschbacher–Smith 5.2.17, printed p.655
(`refs/quasithin.pdf`). It requires no prior splitting or ambient recognition.
The finite checks concern only eight dihedral words and a three-cycle.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Theory.GroupTheory.QuasithinM23
private abbrev A7 := alternatingGroup (Fin 7)
private def cubic : A7 := ⟨Equiv.swap 4 5 * Equiv.swap 4 6, by change Equiv.Perm.sign _ = 1; decide⟩
private theorem cubic_order : orderOf cubic = 3 :=
  orderOf_eq_prime (by decide : cubic^3=1) (by decide : cubic ≠ 1)
private theorem cubic_three : cubic.val.IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private theorem cubic_normalizer_odd : Odd (normalizer (zpowers cubic : Set A7)).index := by
  have hle : (AlternatingSeven.DihedralLocals.fixedSylow : Subgroup A7) ≤
      normalizer (zpowers cubic : Set A7) := by
    intro g hg
    obtain ⟨i,hi⟩ := hg
    change AlternatingSeven.DihedralLocals.tWord i = g.val at hi
    have hconj : ∃ j : Fin 3, g*cubic*g⁻¹ = cubic^j.val := by
      have hh : ∀ i : Fin 8, ∃ j : Fin 3,
          AlternatingSeven.DihedralLocals.tWord i * cubic.val *
            (AlternatingSeven.DihedralLocals.tWord i)⁻¹ = (cubic.val)^j.val := by decide +kernel
      obtain ⟨j,hj⟩ := hh i
      exact ⟨j,Subtype.ext (by change g.val*cubic.val*g.val⁻¹ = cubic.val^j.val; rw [←hi]; exact hj)⟩
    rw [mem_normalizer_iff_map_conj_eq,MonoidHom.map_zpowers]
    have hle : zpowers ((MulAut.conj g) cubic) ≤ zpowers cubic := by
      obtain ⟨j,hj⟩ := hconj
      apply zpowers_le.mpr
      change g*cubic*g⁻¹ ∈ zpowers cubic
      rw [hj]
      exact pow_mem (mem_zpowers cubic) _
    exact eq_of_le_of_card_ge hle (by
      rw [Nat.card_zpowers,Nat.card_zpowers]
      exact ((MulAut.conj g).orderOf_eq cubic).symm.le)
  exact (Nat.not_even_iff_odd).mp (fun hd =>
    AlternatingSeven.DihedralLocals.fixedSylow.not_dvd_index
      ((even_iff_two_dvd.mp hd).trans (index_dvd_of_le hle)))

private theorem split_of_fixed_cubic
    {X : Type*} [Group X] [Finite X]
    (q : X →* A7) (hq : Function.Surjective q)
    [IsMulCommutative q.ker] (hk : Nat.card q.ker = 16)
    (hfree : ∀ c : X, q c = cubic → ∀ a ∈ q.ker, c*a = a*c → a = 1) :
    ∃ K : Subgroup X, q.ker.IsComplement' K := by
  have hker : IsPGroup 2 q.ker := IsPGroup.of_card (n := 4) hk
  have hc : Nat.card (zpowers cubic) = 3 := by rw [Nat.card_zpowers,cubic_order]
  obtain ⟨C,hC,hinj,hcard,_⟩ := q.exists_odd_subgroup_lift hq hker
    (zpowers cubic) (by rw [hc]; decide)
  rw [hc] at hcard
  obtain ⟨c,hcC,hqc⟩ := (show cubic ∈ C.map q from hC.symm ▸ mem_zpowers cubic)
  have hdis : Disjoint q.ker (normalizer (C : Set X)) := by
    apply disjoint_def.mpr
    intro a ha han
    have hac : a*c*a⁻¹ ∈ C := (mem_normalizer_iff.mp han c).mp hcC
    have he : (⟨a*c*a⁻¹,hac⟩ : C) = ⟨c,hcC⟩ := hinj (by
      change q (a*c*a⁻¹) = q c
      simp only [map_mul,map_inv,show q a = 1 from ha,one_mul,inv_one,mul_one])
    exact hfree c hqc a ha (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  let N := normalizer (C : Set X)
  have hp : IsPGroup 3 C := IsPGroup.of_card (n := 1) (by simpa using hcard)
  let : Fact (IsPGroup 3 C) := ⟨hp⟩
  have hmap : N.map q = normalizer (zpowers cubic : Set A7) := by
    rw [←normalizer_map_eq_of_coprime_kernel 3 C q hq (by rw [hk]; decide),hC]
  let D := q.ker ⊔ N
  have hD : D = (normalizer (zpowers cubic : Set A7)).comap q := by
    rw [←hmap,comap_map_eq,sup_comm]
  have hodd : Odd D.index := by
    rw [hD,index_comap_of_surjective _ hq]
    exact cubic_normalizer_odd
  apply exists_complement_of_coprime_overgroup q.ker D le_sup_left
    (by rw [hk]; exact hodd.coprime_two_left.pow_left 4)
  refine ⟨N.subgroupOf D,isComplement'_of_card_mul_and_disjoint ?_ ?_⟩
  · rw [Nat.card_congr (subgroupOfEquivOfLe (show q.ker ≤ D from le_sup_left)).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (show N ≤ D from le_sup_right)).toEquiv]
    exact (card_sup_eq_mul_of_normalizes_of_disjoint q.ker N
      (by rw [q.ker.normalizer_eq_top]; exact le_top) hdis).symm
  · apply disjoint_def.mpr
    intro x hx hxN
    exact Subtype.ext (disjoint_def.mp hdis hx hxN)

/-- An exceptional elementary-sixteen A₇ extension splits over its original core. -/
theorem exceptional_exists_complement
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16)
    (q : X →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = U) (hC : centralizer (U : Set X) = U) :
    ∃ K : Subgroup X, U.IsComplement' K := by
  let ρ := NormalElementaryQuotient.representation U q hq (hk.trans hC.symm)
  have hf := NormalElementaryQuotient.representation_injective U q hq (hk.trans hC.symm)
  have hd : Module.finrank (ZMod 2) (Additive U) = 4 := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    calc
      2 ^ Module.finrank (ZMod 2) (Additive U) = Nat.card (Additive U) := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
      _ = 2^4 := (Nat.card_congr Additive.toMul).trans hU
  have hfree (c : X) (hc : q c = cubic) (a : X) (ha : a ∈ q.ker)
      (hca : c*a = a*c) : a = 1 := by
    let v : Additive U := Additive.ofMul ⟨a,hk ▸ ha⟩
    have hv : ρ cubic v = v := by
      apply Additive.toMul.injective
      apply Subtype.ext
      rw [←hc,NormalElementaryQuotient.representation_apply]
      change c*a*c⁻¹ = a
      rw [hca,mul_inv_cancel_right]
    have hz := binaryAlternatingSeven_threeCycle_fixedPointFree ρ hf hd cubic cubic_three v hv
    exact congrArg (fun w : Additive U => (w.toMul : X)) hz
  let : IsMulCommutative q.ker := hk.symm ▸ inferInstanceAs (IsMulCommutative U)
  obtain ⟨K,hK⟩ := split_of_fixed_cubic q hq (hk ▸ hU) hfree
  exact ⟨K,hk ▸ hK⟩

/-- The splitting has a section of the supplied quotient map, pointwise. -/
theorem exceptional_exists_section
    {X : Type*} [Group X] [Finite X]
    (U : Subgroup X) [U.Normal] [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 16)
    (q : X →* alternatingGroup (Fin 7)) (hq : Function.Surjective q)
    (hk : q.ker = U) (hC : centralizer (U : Set X) = U) :
    ∃ s : alternatingGroup (Fin 7) →* X, q.comp s = MonoidHom.id _ := by
  obtain ⟨K,hK⟩ := exceptional_exists_complement U hU q hq hk hC
  let r := q.comp K.subtype
  have hi : Function.Injective r := by
    apply (MonoidHom.ker_eq_bot_iff r).mp
    rw [eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    exact disjoint_def.mp hK.disjoint (hk ▸ (show q x = 1 from hx)) x.property
  have hs : Function.Surjective r := by
    intro y
    obtain ⟨x,rfl⟩ := hq y
    obtain ⟨⟨u,k⟩,hu⟩ := hK.2 x
    refine ⟨k,?_⟩
    have hh := congrArg q hu
    rw [map_mul,show q u = 1 from (hk.symm ▸ u.property),one_mul] at hh
    exact hh
  let e := MulEquiv.ofBijective r ⟨hi,hs⟩
  refine ⟨K.subtype.comp e.symm.toMonoidHom,?_⟩
  apply MonoidHom.ext
  intro x
  exact e.apply_symm_apply x

end Theory.GroupTheory.QuasithinM23
