module
public import Theory.GroupAction.AbelianCoprimeFixedGeneration
public import Theory.GroupAction.CoprimeHall
public import Theory.GroupAction.AutomorphismFixedSubgroup
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
/-!
# Elementary two-actors with cyclic involution centralizers

A faithful elementary abelian two-group acting on a finite 3-group has
order at most four if each nonidentity actor has a cyclic fixed subgroup.
In the noncyclic case its common fixed subgroup in the original 3-group is
trivial.

A nonidentity common fixed point supplies a fixed subgroup of order three
inside every cyclic individual fixed group. All prime-order elements of
such a cyclic 3-group then belong to that subgroup, so coprime action makes
the whole individual fixed group fixed. Coprime fixed-point generation
forces the entire action to be trivial. Applying this argument to the
cyclic-quotient subgroups in the same generation theorem bounds the actor
order by four.

Source: the consequence of Aschbacher--Smith, *The Classification of
Quasithin Groups*, A.1.5 used in the initial reductions of D.2.14. The proof
uses the valid fixed-point generation clause of A.1.17. It does not assert
that the original 3-group is elementary abelian.
-/

open scoped IsMulCommutative
open Subgroup
namespace ElementaryTwoCyclicFixed
variable {A P : Type*} [Group A] [Finite A] [Group P] [Finite P]

private theorem prime_order_mem_cubic_line [IsCyclic P] (hP : IsPGroup 3 P)
    (y : P) (hy : orderOf y = 3) (z : P) (hz : Nat.Prime (orderOf z)) :
    z ∈ zpowers y := by
  classical
  let : Fintype P := Fintype.ofFinite P
  let C := zpowers y
  have hcard : Nat.card C = 3 := by simpa only [C, Nat.card_zpowers] using hy
  have hz3 : orderOf z = 3 := by
    obtain ⟨n, hn⟩ := hP.exists_orderOf_dvd_pow z
    exact (Nat.dvd_prime Nat.prime_three).mp (hz.dvd_of_dvd_pow hn) |>.resolve_left hz.ne_one
  have hsub : (C : Set P).toFinset ⊆ Finset.univ.filter (fun w : P => w^3=1) := by
    intro w hw
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hcard]
    exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨w,Set.mem_toFinset.mp hw⟩ : C)))
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    have hbound := IsCyclic.card_pow_eq_one_le (α := P) (by decide : 0<3)
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    change _ ≤ Nat.card C
    rw [hcard]
    exact hbound)
  apply Set.mem_toFinset.mp
  rw [heq]
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [← hz3]; exact pow_orderOf_eq_one z⟩

private theorem cyclic_action_trivial [IsCyclic P] [MulDistribMulAction A P]
    (hP : IsPGroup 3 P) (hcop : Nat.Coprime (Nat.card A) 3)
    (x : P) (hx : x ≠ 1) (hfix : ∀ a : A, a • x = x) : ActsTrivially A P := by
  let C := fixedPointSubgroup A P
  have hxC : x ∈ C := hfix
  have hxCne : (⟨x,hxC⟩ : C) ≠ 1 := fun he => hx (congrArg Subtype.val he)
  have hdiv : 3 ∣ Nat.card C :=
    ((hP.to_subgroup C).dvd_orderOf hxCne).trans (orderOf_dvd_natCard (⟨x,hxC⟩ : C))
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 hdiv
  have hcopP : Nat.Coprime (Nat.card A) (Nat.card P) := by
    obtain ⟨n,hn⟩ := hP.exists_card_eq
    rw [hn]
    exact hcop.pow_right n
  have hsolv : Group.IsSolvable P :=
    @IsNilpotent.to_isSolvable P inferInstance hP.isNilpotent
  apply actsTrivially_of_isMulCommutative_and_prime_order_mem_fixedPointSubgroup
    hsolv hcopP inferInstance
  intro z hz
  have hzline := prime_order_mem_cubic_line hP (y : P)
    (by simpa only [Subgroup.orderOf_coe] using hy) z hz
  exact (zpowers_le.mpr y.property) hzline

private theorem actor_coprime [IsElementaryAbelian 2 A] :
    Nat.Coprime (Nat.card A) 3 := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  rw [hn]
  exact (by decide : Nat.Coprime 2 3).pow_left n

omit [Finite A] in
private theorem cyclic_quotient_card_le_two [IsElementaryAbelian 2 A]
    (Y : Subgroup A) [Y.Normal] (hY : IsCyclic (A ⧸ Y)) : Nat.card (A ⧸ Y) ≤ 2 := by
  apply Nat.le_of_dvd (by decide)
  rw [← hY.exponent_eq_card]
  exact (Group.exponent_quotient_dvd Y).trans (IsElementaryAbelian.exponent_dvd_p 2 A)


/-- A noncyclic faithful elementary two-actor with cyclic nontrivial-element
fixed groups has no nonidentity common fixed point in the original 3-group. -/
public theorem common_fixed_eq_one [IsElementaryAbelian 2 A]
    (hP : IsPGroup 3 P) (f : A →* MulAut P) (hf : Function.Injective f)
    (hcyc : ∀ a : A, a ≠ 1 → IsCyclic (f a).fixedSubgroup)
    (hA : 2 < Nat.card A) (x : P) (hfix : ∀ a : A, f a x = x) : x = 1 := by
  classical
  by_contra hx
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P f
  let : Fact (IsPGroup 3 P) := ⟨hP⟩
  have hcop : Nat.Coprime (Nat.card A) 3 := actor_coprime
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := P) (A := A) (q := 3) hcop
  have hcentral (a : A) (ha : a ≠ 1) : (f a).fixedSubgroup ≤ fixedPointSubgroup A P := by
    let C := (f a).fixedSubgroup
    let : IsCyclic C := hcyc a ha
    have hstable (b : A) (y : P) (hy : y ∈ C) : b • y ∈ C := by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change f a (f b y) = f b y
      have hab : f a * f b = f b * f a := by rw [← map_mul, ← map_mul, mul_comm a b]
      have hy : f a y = y := (MulAut.mem_fixedSubgroup _ _).mp hy
      exact (DFunLike.congr_fun hab y).trans (congrArg (f b) hy)
    let : IsInvariant A P C := ⟨fun b y => ⟨hstable b y, fun hy => by
      simpa only [inv_smul_smul] using hstable b⁻¹ (b • y) hy⟩⟩
    have hxC : x ∈ C := (MulAut.mem_fixedSubgroup _ _).mpr (hfix a)
    have htriv := cyclic_action_trivial (hP.to_subgroup C) hcop (⟨x,hxC⟩ : C)
      (fun he => hx (congrArg Subtype.val he)) (fun b => Subtype.ext (hfix b))
    intro y hy b
    exact congrArg Subtype.val (htriv b ⟨y,hy⟩)
  have htop : (⊤ : Subgroup P) ≤ fixedPointSubgroup A P := by
    rw [← hgen]
    refine iSup₂_le fun Y hY => ?_
    have hq := cyclic_quotient_card_le_two Y hY
    have hcount := card_eq_card_quotient_mul_card_subgroup Y
    have hYgt : 1 < Nat.card Y := by nlinarith [Nat.card_pos (α := A ⧸ Y)]
    let : Nontrivial Y := Finite.one_lt_card_iff_nontrivial.mp hYgt
    obtain ⟨a,ha⟩ := exists_ne (1 : Y)
    have haone : (a : A) ≠ 1 := fun he => ha (Subtype.ext he)
    intro y hy
    apply hcentral a haone
    exact (MulAut.mem_fixedSubgroup _ _).mpr (hy a)
  have hone (a : A) : a = 1 := by
    apply hf
    ext y
    rw [map_one, MulAut.one_apply]
    exact htop (mem_top y) a
  have : Subsingleton A := ⟨fun a b => (hone a).trans (hone b).symm⟩
  have hc : Nat.card A = 1 := Nat.card_unique
  omega


/-- The faithful elementary binary actor has order at most four. -/
public theorem card_le_four [IsElementaryAbelian 2 A]
    (hP : IsPGroup 3 P) (f : A →* MulAut P) (hf : Function.Injective f)
    (hcyc : ∀ a : A, a ≠ 1 → IsCyclic (f a).fixedSubgroup) : Nat.card A ≤ 4 := by
  classical
  by_contra! hA
  let : CommGroup A := IsMulCommutative.instCommGroup
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P f
  let : Fact (IsPGroup 3 P) := ⟨hP⟩
  have hgen := iSup_fixedPoints_cyclicQuot_eq_top_of_coprime_abelian_pGroup
    (G := P) (A := A) (q := 3) actor_coprime
  have hbot : (⊤ : Subgroup P) ≤ ⊥ := by
    rw [← hgen]
    refine iSup₂_le fun Y hY x hx => ?_
    have hq := cyclic_quotient_card_le_two Y hY
    have hcount := card_eq_card_quotient_mul_card_subgroup Y
    have hYgt : 2 < Nat.card Y := by nlinarith [Nat.card_pos (α := A ⧸ Y)]
    let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
    exact common_fixed_eq_one hP (f.comp Y.subtype) (hf.comp Y.subtype_injective)
      (fun a ha => hcyc a (fun he => ha (Subtype.ext he))) hYgt x hx
  have hPone (x : P) : x = 1 := hbot (mem_top x)
  have hone (a : A) : a = 1 := by
    apply hf
    ext x
    exact (hPone _).trans (hPone _).symm
  have : Subsingleton A := ⟨fun a b => (hone a).trans (hone b).symm⟩
  have hc : Nat.card A = 1 := Nat.card_unique
  omega

/-- The noncyclic case of the cyclic involution-centralizer action bound:
the actor is a four-group and its common fixed subgroup is trivial. -/
public theorem card_eq_four_and_common_fixed_eq_one [IsElementaryAbelian 2 A]
    (hP : IsPGroup 3 P) (f : A →* MulAut P) (hf : Function.Injective f)
    (hcyc : ∀ a : A, a ≠ 1 → IsCyclic (f a).fixedSubgroup)
    (hA : 2 < Nat.card A) :
    Nat.card A = 4 ∧ ∀ x : P, (∀ a : A, f a x = x) → x = 1 := by
  refine ⟨?_, fun x hx => common_fixed_eq_one hP f hf hcyc hA x hx⟩
  have hle := card_le_four hP f hf hcyc
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hn2 : 2 ≤ n := by
    by_contra! h
    interval_cases n <;> simp_all
  have hlo : 4 ≤ Nat.card A := by
    rw [hn]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hn2
  omega

end ElementaryTwoCyclicFixed
