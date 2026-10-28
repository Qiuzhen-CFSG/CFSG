module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary.ModelCases
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.Reduction
public import Theory.SpecificGroups.SU3.SpecialProjectiveComparison
public import Theory.SpecificGroups.SU3.OddThreeLocal.Monomial
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Lifting projective order-nine pairs and descending their local cores

A nonabelian preimage of an elementary projective subgroup forces the actual
scalar kernel to have order three. Hence that preimage has order 27, and the
full preimage of a permuting Sylow pair has order 27 times its two-part.
A Sylow two-subgroup lifts isomorphically through the odd scalar kernel.

An upstairs three-core of order nine descends to a projective core of order
three. Since U is Sylow three in its product with T, this core is a subgroup
of U. Its intrinsic definition makes the resulting line invariant under the
full pair automizer. No lift of an outer automorphism to SU₃ is needed.

`MonomialPlacement` states the remaining geometric obligation. The lemmas
here prove the lift, counting, solvability and descent steps only; they do
not assert that placement or the completed source exclusion.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511 (PDF p.528),
and A.3.21(c), printed pp.55–56; GLS3, Theorem 6.5.3(a)–(d),
`refs/KGroup/GLS3/chapter6.tex`.
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary

namespace NonabelianLift

/-- Geometric placement of the full special preimage of a projective pair.
The equivalence is between actual unitary groups; the target form has an
orthonormal coordinate basis. This is a remaining obligation, not a theorem. -/
def MonomialPlacement (p : ℕ) : Prop :=
  ∀ {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E),
    IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) →
    Nat.card E = p ^ 2 → (∀ x, J.conj x = x ^ p) →
    ∀ (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
      (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)),
      IsElementaryAbelian 3 U → Nat.card U = 9 →
      ¬ IsMulCommutative (U.comap J.specialToProjective) →
      (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (T : Set _) =
        (T : Set _) * (U : Set _) →
      ∃ (J' : HermitianForm 3 E), (∀ x, J'.conj x = x ^ p) ∧ J'.form = 1 ∧
        ∃ e : J.specialSubgroup ≃* J'.specialSubgroup,
          ((U ⊔ (T : Subgroup _)).comap J.specialToProjective).map e.toMonoidHom ≤
            HermitianForm.OddThreeLocal.Monomial.special J'

variable {E : Type} [Field E] [Finite E] (J : HermitianForm 3 E)

omit [Finite E] in
private theorem scalar_kernel_three_group : IsPGroup 3 J.specialToProjective.ker :=
  fun x => ⟨1, by simpa using J.specialToProjective_ker_cube x⟩

/-- Noncommuting lifts force the scalar kernel to have order exactly three. -/
theorem scalar_kernel_card
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (he : IsElementaryAbelian 3 U)
    (hn : ¬ IsMulCommutative (U.comap J.specialToProjective)) :
    Nat.card J.specialToProjective.ker = 3 := by
  let _ := he
  let K := J.specialToProjective.ker
  let f : K →* center (GL (Fin 3) E) :=
    (J.specialSubgroup.subtype.comp K.subtype).codRestrict _ (by
      intro x
      apply Matrix.ProjGenLinGroup.mk_eq_one.mp
      change Matrix.ProjGenLinGroup.mk x.val.val = 1
      simpa only [J.specialToProjective_apply_val, Subgroup.coe_one] using
        congrArg Subtype.val (MonoidHom.mem_ker.mp x.property))
  have hf : Function.Injective f := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val) hxy))
  have hcyc : IsCyclic (center (GL (Fin 3) E)) := by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact isCyclic_of_surjective (Matrix.GeneralLinearGroup.scalar (Fin 3)).rangeRestrict
      (Matrix.GeneralLinearGroup.scalar (Fin 3)).rangeRestrict_surjective
  let _ := hcyc
  let _ : IsCyclic K := isCyclic_of_injective f hf
  have hd : Nat.card K ∣ 3 := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr J.specialToProjective_ker_cube
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hc | hc
  · have hi : Function.Injective J.specialToProjective :=
      J.specialToProjective.ker_eq_bot_iff.mp (Subgroup.card_eq_one.mp hc)
    apply False.elim
    apply hn
    exact .of_comm fun x y => by
      apply Subtype.ext
      apply hi
      change (J.specialToProjective (x.val * y.val)) =
        J.specialToProjective (y.val * x.val)
      rw [map_mul, map_mul]
      exact congrArg U.subtype (mul_comm'
        (⟨J.specialToProjective x.val, x.property⟩ : U)
        (⟨J.specialToProjective y.val, y.property⟩ : U))
  · exact hc

private theorem preimage_kernel {A B : Type*} [Group A] [Group B]
    (q : A →* B) (H : Subgroup B) :
    (q.subgroupComap H).ker = q.ker.subgroupOf (H.comap q) := by
  ext x
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

private theorem preimage_kernel_card {A B : Type*} [Group A] [Group B]
    (q : A →* B) (H : Subgroup B) :
    Nat.card (q.subgroupComap H).ker = Nat.card q.ker := by
  rw [preimage_kernel]
  exact Nat.card_congr (subgroupOfEquivOfLe (H.ker_le_comap q)).toEquiv

private theorem preimage_card {A B : Type*} [Group A] [Finite A] [Group B]
    (q : A →* B) (hq : Function.Surjective q) (H : Subgroup B) :
    Nat.card (H.comap q) = Nat.card q.ker * Nat.card H := by
  have hh := (q.subgroupComap H).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr
    (q.subgroupComap_surjective_of_surjective H hq),
    Nat.card_congr (Subgroup.topEquiv).toEquiv, preimage_kernel_card] at hh
  exact hh.symm

/-- The full special-unitary preimage is a nonabelian three-group of order 27. -/
theorem preimage_three_group_card
    (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (he : IsElementaryAbelian 3 U) (hc : Nat.card U = 9)
    (hn : ¬ IsMulCommutative (U.comap J.specialToProjective)) :
    IsPGroup 3 (U.comap J.specialToProjective) ∧
      Nat.card (U.comap J.specialToProjective) = 27 := by
  let _ := he
  refine ⟨(IsElementaryAbelian.isPGroup 3 U).comap_of_ker_isPGroup
    J.specialToProjective (scalar_kernel_three_group J), ?_⟩
  rw [preimage_card J.specialToProjective J.specialToProjective_surjective U,
    scalar_kernel_card J U he hn, hc]

/-- Choose a Sylow two-subgroup upstairs mapping isomorphically onto the given one. -/
theorem exists_special_sylow
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ S : Sylow 2 J.specialSubgroup,
      (S : Subgroup J.specialSubgroup).map J.specialToProjective = T ∧
      Nat.card S = Nat.card T := by
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective J.specialToProjective_surjective 2 T
  have hm : (S : Subgroup J.specialSubgroup).map J.specialToProjective = T := by
    simpa using congrArg Sylow.toSubgroup hS
  refine ⟨S, hm, ?_⟩
  have hi := injective_comp_subtype_of_coprime_ker J.specialToProjective
    (Nat.coprime_two_left.mpr (J.odd_card_specialToProjective_ker))
    (S : Subgroup J.specialSubgroup) S.isPGroup'
  let e := MulEquiv.ofBijective (J.specialToProjective.subgroupMap (S : Subgroup _))
    ⟨fun x y h => hi (congrArg Subtype.val h),
      J.specialToProjective.subgroupMap_surjective (S : Subgroup _)⟩
  exact (Nat.card_congr e.toEquiv).trans (congrArg (fun H : Subgroup _ => Nat.card H) hm)

private theorem card_local_core {G : Type*} [Group G] (H : Subgroup G) (r : ℕ) :
    Nat.card (H.pCoreIn r) = Nat.card (pCore r H) :=
  card_map_of_injective H.subtype_injective

section Pair
variable (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
  (U : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  (he : IsElementaryAbelian 3 U) (hc : Nat.card U = 9)
  (hperm : (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)) * (T : Set _) =
    (T : Set _) * (U : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
include he hc hperm

private theorem product_card :
    Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) = 9 * Nat.card T := by
  let _ := he
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hd := (IsElementaryAbelian.isPGroup 3 U).disjoint_of_coprime T.isPGroup' (by decide)
  have hh := card_set_mul_mul_card_inf U (T : Subgroup _)
  rw [hd.eq_bot, card_bot, mul_one,
    ← coe_sup_of_set_mul_comm U (T : Subgroup _) hperm, hc] at hh
  exact hh

/-- The full preimage of the product has order 27 times the Sylow two-order. -/
theorem preimage_product_card
    (hn : ¬ IsMulCommutative (U.comap J.specialToProjective)) :
    Nat.card ((U ⊔ (T : Subgroup _)).comap J.specialToProjective) =
      27 * Nat.card T := by
  rw [preimage_card J.specialToProjective J.specialToProjective_surjective,
    scalar_kernel_card J U he hn, product_card J T U he hc hperm]
  omega

/-- Burnside's two-prime theorem makes the full preimage of the product solvable. -/
theorem preimage_product_solvable
    (hn : ¬ IsMulCommutative (U.comap J.specialToProjective)) :
    Group.IsSolvable ((U ⊔ (T : Subgroup _)).comap J.specialToProjective) := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  apply Theory.GroupTheory.isSolvable_of_prime_dvd_card_eq_two_or_three
  intro r hr hd
  rw [preimage_product_card J T U he hc hperm hn] at hd
  rcases hr.dvd_mul.mp hd with hd | hd
  · right
    have h3 : r ∣ 3 := hr.dvd_of_dvd_pow (show r ∣ 3 ^ 3 from hd)
    exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hr.ne_one
  · left
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn] at hd
    exact ((Nat.dvd_prime Nat.prime_two).mp (hr.dvd_of_dvd_pow hd)).resolve_left hr.ne_one

/-- Normal three-subgroups of the pair product lie in its Sylow three-subgroup U. -/
theorem local_core_le : (U ⊔ (T : Subgroup _)).pCoreIn 3 ≤ U := by
  let _ := he
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let H := U ⊔ (T : Subgroup _)
  have hindex : (U.subgroupOf H).index = Nat.card T := by
    have hh := (U.subgroupOf H).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe (show U ≤ H from le_sup_left)).toEquiv,
      product_card J T U he hc hperm, hc] at hh
    omega
  let P : Sylow 3 H := (IsElementaryAbelian.isPGroup 3 U).comap_subtype.toSylow (by
    change ¬ 3 ∣ (U.subgroupOf H).index
    rw [hindex]
    obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
    rw [hn]
    intro hd
    have := Nat.prime_three.dvd_of_dvd_pow hd
    norm_num at this)
  have hh := H.pCoreIn_le_sylow P
  simpa only [P, IsPGroup.toSylow_coe, comap_subtype, map_subgroupOf_eq_of_le
    (show U ≤ H from le_sup_left)] using hh

/-- The order-three core is the required invariant line, for the full pair automizer. -/
theorem reducible_of_projective_core_three
    (hcore : Nat.card (pCore 3 ↥(U ⊔ (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))) = 3) :
    PairReducible (T : Subgroup _) U := by
  let _ := he
  let : Fact (IsPGroup 3 U) := ⟨IsElementaryAbelian.isPGroup 3 U⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hi : Nat.card (((U ⊔ (T : Subgroup _)).pCoreIn 3).subgroupOf U) = 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (local_core_le J T U he hc hperm)).toEquiv]
    have hh : Nat.card ((U ⊔ (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))).pCoreIn 3) =
        Nat.card (pCore 3 ↥(U ⊔ (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)))) :=
      card_local_core (U ⊔ (T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))) 3
    exact hh.trans hcore
  apply reducible_of_local_core_intersection (T : Subgroup _) U 3
  · rw [frattini_eq_bot_of_isElementaryAbelian (R := U) (p := 3)]
    intro h
    have hb := le_bot_iff.mp h
    rw [hb, card_bot] at hi
    omega
  · intro h
    rw [h, Nat.card_congr (Subgroup.topEquiv).toEquiv, hc] at hi
    omega

/-- Descend the special core through the actual scalar kernel of order three. -/
theorem reducible_of_special_core_nine
    (hn : ¬ IsMulCommutative (U.comap J.specialToProjective))
    (hcore : Nat.card (pCore 3 ((U ⊔ (T : Subgroup _)).comap
      J.specialToProjective)) = 9) : PairReducible (T : Subgroup _) U := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let H := U ⊔ (T : Subgroup _)
  let q := J.specialToProjective.subgroupComap H
  have hk : IsPGroup 3 q.ker := by
    rw [show q.ker = J.specialToProjective.ker.subgroupOf (H.comap J.specialToProjective)
      from preimage_kernel _ _]
    exact (scalar_kernel_three_group J).comap_subtype
  have hh := q.card_pCore_of_ker_isPGroup
    (J.specialToProjective.subgroupComap_surjective_of_surjective H
      J.specialToProjective_surjective) hk
  rw [hcore, preimage_kernel_card, scalar_kernel_card J U he hn] at hh
  have hthree : Nat.card (pCore 3 H) = 3 := by omega
  exact reducible_of_projective_core_three J T U he hc hperm hthree

end Pair
end NonabelianLift
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.UnitaryThree.ModTwoElementary
