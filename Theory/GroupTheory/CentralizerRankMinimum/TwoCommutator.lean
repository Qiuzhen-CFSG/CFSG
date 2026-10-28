module
public import Theory.GroupTheory.CentralizerRankMinimum
public import Theory.ElementaryAbelian.GeneratorRank
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# A two-element commutator and the centralizer-rank minimum

For an elementary abelian U, the difference of a normalizing automorphism
and the identity is a homomorphism. If its image has at most two elements,
its kernel has quotient rank at most one. A nontrivial action therefore
has minimum centralizer-detecting quotient rank exactly one.

Source application: Aschbacher–Smith C.6.3(b) and C.6.4, pp.166–168.
-/

@[expose] public noncomputable section
open scoped IsMulCommutative commutatorElement
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem centralizerRankMinimum_pos (R U : Subgroup G) [IsMulCommutative U]
    (hC : R ⊓ centralizer (U : Set G) < R) : 0 < centralizerRankMinimum R U := by
  obtain ⟨A,hAU,hA,hr⟩ := centralizerRankMinimum_mem R U hC
  by_contra h
  have hz : Group.rank (U ⧸ A.subgroupOf U) = 0 := hr.trans (Nat.eq_zero_of_not_pos h)
  let := (Group.rank_eq_zero_iff (G := U ⧸ A.subgroupOf U)).mp hz
  have hUA : U ≤ A := by
    intro u hu
    have hh : QuotientGroup.mk' (A.subgroupOf U) ⟨u,hu⟩ = 1 := Subsingleton.elim _ _
    have hu' : (⟨u,hu⟩ : U) ∈ A.subgroupOf U := (QuotientGroup.eq_one_iff _).mp hh
    exact hu'
  exact hA.ne (congrArg (fun B : Subgroup G => R ⊓ centralizer (B : Set G))
    (le_antisymm hUA hAU))

/-- A nontrivial action with at most two commutator values has minimum one. -/
theorem centralizerRankMinimum_eq_one_of_commutator_card_le_two
    (R U : Subgroup G) [IsElementaryAbelian 2 U]
    (hn : R ≤ normalizer (U : Set G))
    (hC : R ⊓ centralizer (U : Set G) < R)
    (hc : Nat.card (⁅R,U⁆ : Subgroup G) ≤ 2) : centralizerRankMinimum R U = 1 := by
  obtain ⟨r,hr,hrC⟩ := SetLike.exists_of_lt hC
  have hru : r ∉ centralizer (U : Set G) := fun h => hrC ⟨hr,h⟩
  let a := U.normalizerMonoidHom ⟨r,hn hr⟩
  let f : U →* U := {
    toFun := fun u => a u * u⁻¹
    map_one' := by simp
    map_mul' := by intro u v; simp only [map_mul,mul_inv_rev]; ac_rfl }
  let A := f.ker.map U.subtype
  have hAU : A ≤ U := map_subtype_le _
  have hAc : r ∈ centralizer (A : Set G) := by
    rintro v ⟨u,hu,rfl⟩
    have hh : a u * u⁻¹ = 1 := hu
    have hh' := congrArg Subtype.val (mul_inv_eq_one.mp hh)
    change r * (u : G) * r⁻¹ = (u : G) at hh'
    exact (mul_inv_eq_iff_eq_mul.mp hh').symm
  have hCA : R ⊓ centralizer (U : Set G) < R ⊓ centralizer (A : Set G) :=
    lt_of_le_not_ge (inf_le_inf le_rfl (centralizer_le hAU)) (fun h => hrC (h ⟨hr,hAc⟩))
  have hker : A.subgroupOf U = f.ker := comap_map_eq_self_of_injective U.subtype_injective _
  let e := (QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange f)
  have hmem (v : f.range) : (v.val : G) ∈ ⁅R,U⁆ := by
    obtain ⟨u,hu⟩ := v.property
    rw [← hu]
    exact commutator_mem_commutator hr u.property
  let j : f.range → (⁅R,U⁆ : Subgroup G) := fun v => ⟨v.val,hmem v⟩
  have hj : Function.Injective j := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : (⁅R,U⁆ : Subgroup G) => (w : G)) huv
  have hcard : Nat.card f.range ≤ 2 := (Nat.card_le_card_of_injective j hj).trans hc
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_injective f.range.subtype f.range.subtype_injective
  have hupper : centralizerRankMinimum R U ≤ 1 := by
    refine (centralizerRankMinimum_le R U A hAU hCA).trans ?_
    rw [Group.rank_congr e]
    exact IsElementaryAbelian.rank_le_of_card_le (p := 2) f.range (by simpa using hcard)
  exact Nat.le_antisymm hupper (centralizerRankMinimum_pos R U hC)

end Subgroup
