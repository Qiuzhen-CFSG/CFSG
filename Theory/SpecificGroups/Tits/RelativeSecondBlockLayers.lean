module

public import Theory.SpecificGroups.Tits.RelativeSecondBlockLayers.SecondOrder
public import Theory.PGroupCore
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Fintype.Perm

/-!
# The second Tits parabolic has no elementary two-core actor

The actual second parabolic has order 6144. The square of the Parrott
root element s3 belongs to its two-core: the action on the three Sylow
cosets has order dividing six, so the image of an element of order four
has square one. Its commutator with r8*s8 has nonidentity square, checked
at a point of the certified Atlas permutation action.

Every nontrivial two-perfect subgroup contains an element of order three.
Sylow conjugacy transports the concrete commutator witness into its
actor group. Thus such a subgroup cannot act with square-one commutators
on the two-core. This intrinsic statement does not identify a block with
the whole parabolic and requires no quotient or simplicity certificate
beyond the actual marked carrier and its proved order.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; Parrott (1972),
p.683, with conventions in refs/original/n-group-global/parrott-tits-presentation.md.
The three-coset proof is recovered in the SecondOrder descendant from the
saved qt-f-01-exceptional-tits-local work.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement Pointwise

namespace Tits.RelativeSecondBlockLayers
open ExceptionalParabolics

private theorem s_mem (i : ParrottGenerator) (hi : i ≠ .r1) (hi8 : i ≠ .r8) :
    atlas1600ParrottAssignment i ∈ S := by
  rw [S, atlas1600SylowTwoSubgroup_eq]
  apply Subgroup.subset_closure
  cases i <;> simp_all

/-- The actual Parrott generator s3 in the second parabolic. -/
def rootElement : second := ⟨atlas1600ParrottAssignment .s3, by
  exact sylow_le_second (s_mem .s3 (by decide) (by decide))⟩

/-- The order-three element r8*s8 in the second parabolic. -/
def rotation : second := ⟨atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .s8, by
  exact second.mul_mem reflection_mem_second (sylow_le_second (s_mem .s8 (by decide) (by decide)))⟩

theorem root_four : rootElement ^ 4 = 1 := by
  apply Subtype.ext
  simpa [rootElement, parrottRelator] using atlas1600ParrottAssignment_relations .i_s3

theorem rotation_three : rotation ^ 3 = 1 := by
  apply Subtype.ext
  simpa [rotation, parrottRelator] using atlas1600ParrottAssignment_relations .vi_r8_s8

private theorem val_mul (x y : Atlas1600Group) : (x * y).val = x.val * y.val := rfl
private theorem val_inv (x : Atlas1600Group) : x⁻¹.val = x.val⁻¹ := rfl
private theorem val_pow (x : Atlas1600Group) (n : ℕ) : (x ^ n).val = x.val ^ n := rfl

/-- A concrete failure of elementary two-core action. -/
theorem root_square_commutator_square_ne_one : ⁅rootElement ^ 2, rotation⁆ ^ 2 ≠ 1 := by
  intro hh
  have hf := congrArg (fun x : second => x.val.val 0) hh
  change ((⁅atlas1600ParrottAssignment .s3 ^ 2,
    atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .s8⁆ ^ 2 : Atlas1600Group).val) 0 = 0 at hf
  have hn : ((⁅atlas1600ParrottAssignment .s3 ^ 2,
    atlas1600ParrottAssignment .r8 * atlas1600ParrottAssignment .s8⁆ ^ 2 : Atlas1600Group).val) 0 ≠ 0 := by
    simp only [commutatorElement_def, val_mul, val_inv, val_pow, atlas1600ParrottAssignment_val]
    decide +kernel
  exact hn hf

theorem rotation_order : orderOf rotation = 3 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply orderOf_eq_prime rotation_three
  intro hh
  apply root_square_commutator_square_ne_one
  rw [hh]
  simp

/-- A fourth-order root square lies in the kernel of the three-coset action. -/
theorem root_square_mem_core : rootElement ^ 2 ∈ pCore 2 second := by
  classical
  let T : Subgroup second := S.subgroupOf second
  let f : second →* Equiv.Perm (second ⧸ T) := MulAction.toPermHom second (second ⧸ T)
  have hfour : orderOf (f rootElement) ∣ 4 :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, root_four, map_one])
  have hcard : Nat.card (Equiv.Perm (second ⧸ T)) = 6 := by
    let := Fintype.ofFinite (second ⧸ T)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card]
    change Nat.factorial T.index = 6
    rw [second_sylow_index]
    decide
  have hsix : orderOf (f rootElement) ∣ 6 := hcard ▸ orderOf_dvd_natCard (f rootElement)
  have htwo : (f rootElement) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_gcd hfour hsix)
  have hmem : rootElement ^ 2 ∈ T.normalCore := by
    rw [T.normalCore_eq_ker, MonoidHom.mem_ker, map_pow]
    exact htwo
  apply (show T.normalCore ≤ pCore 2 second from ?_) hmem
  apply le_sSup
  refine ⟨inferInstance, ?_⟩
  have hS : IsPGroup 2 S := IsPGroup.of_card (n := 11) (by simpa using sylow_card)
  exact hS.comap_subtype.to_le T.normalCore_le

private noncomputable def sylowThree (x : second) (hx : orderOf x = 3) : Sylow 3 second := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hcard : Nat.card (zpowers x) = 3 ^ 1 := by rw [Nat.card_zpowers, hx]; rfl
  apply (IsPGroup.of_card hcard).toSylow
  have hi : (zpowers x).index = 2048 := by
    have h := (zpowers x).card_mul_index
    rw [hcard, second_card] at h
    omega
  rw [hi]
  decide

private theorem sylowThree_coe (x : second) (hx : orderOf x = 3) :
    (sylowThree x hx : Subgroup second) = zpowers x := by
  rfl

/-- Every two-perfect actor with square-one core commutators is trivial.
No subnormality or block hypothesis is needed for this intrinsic calculation. -/
theorem eq_bot_of_core_square (X : Subgroup second) (hp : IsPPerfect 2 X)
    (hsquare : ∀ q ∈ pCore 2 second, ∀ x ∈ X, (⁅q, x⁆ : second) ^ 2 = 1) : X = ⊥ := by
  classical
  by_cases hthree : 3 ∣ Nat.card X
  · let : Fact (Nat.Prime 3) := ⟨by decide⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hthree
    have hxval : orderOf (x : second) = 3 := (Subgroup.orderOf_coe x).trans hx
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq second
      (sylowThree rotation rotation_order) (sylowThree x hxval)
    have hrot : (MulAut.conj g) rotation ∈ X := by
      have hm : (MulAut.conj g) rotation ∈
          (g • sylowThree rotation rotation_order : Sylow 3 second) := by
        change (MulAut.conj g) rotation ∈
          (sylowThree rotation rotation_order : Subgroup second).map (MulAut.conj g).toMonoidHom
        apply mem_map_of_mem
        rw [sylowThree_coe]
        exact mem_zpowers _
      rw [hg] at hm
      have hz : zpowers (x : second) ≤ X := zpowers_le.mpr x.property
      exact hz hm
    have hq : (MulAut.conj g) (rootElement ^ 2) ∈ pCore 2 second :=
      (inferInstance : (pCore 2 second).Normal).conj_mem _ root_square_mem_core g
    have he : (MulAut.conj g) (⁅rootElement ^ 2, rotation⁆ ^ 2) = (MulAut.conj g) 1 := by
      rw [map_pow, map_commutatorElement, map_one]
      exact hsquare _ hq _ hrot
    exact (root_square_commutator_square_ne_one ((MulAut.conj g).injective he)).elim
  · have hdiv : Nat.card X ∣ 3 * 2 ^ 11 := by
      simpa only [second_card, show 3 * 2 ^ 11 = 6144 by decide] using X.card_subgroup_dvd_card
    have hcop : (Nat.card X).Coprime 3 :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hthree |>.symm
    have htwo : IsPGroup 2 X := IsPGroup.of_card_dvd_pow (hcop.dvd_mul_left.mp hdiv)
    have hone := hp.hom_eq_one_of_isPGroup htwo (MonoidHom.id X)
    apply eq_bot_iff.mpr
    intro x hx
    exact mem_bot.mpr (congrArg Subtype.val (DFunLike.congr_fun hone ⟨x, hx⟩))

end Tits.RelativeSecondBlockLayers

end
