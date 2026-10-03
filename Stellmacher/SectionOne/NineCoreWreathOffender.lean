module

public import Stellmacher.SectionOne.NineCoreOffenderTransport
public import Theory.GroupAction.ComplementaryFourWreathAction

/-!
# A nontrivial offender in a complementary-four action of order 72

The faithful action preserving an unordered complementary pair of four-groups
is identified with the natural SL₂(2) wreath action. An involution swapping
the two entries in just one four-group fixes eight of the sixteen vectors.
Transport through the compatible group and module equivalences gives an
actual ambient offender; Sylow conjugation puts it in the prescribed join.
The small coordinate calculations are kernel-checked, not native evaluations.

The numerical helper reduces order 72 to divisibility by 72 and exclusion
of order 36 when the odd core has order nine and an actor has order four.
Neither helper assumes that the arbitrary order-four actor is an offender.

These are conditional assembly steps for Stellmacher (9.1)(8), printed p.47 /
PDF p.37 of `refs/files/stellmacher-n-group.pdf`. The support pair, its
normalizer bound, and the order-36 exclusion are separate prerequisites.
-/

namespace Stellmacher.SectionOne

universe u

private abbrev FourModule := Multiplicative (Fin 2 → ZMod 2)
private abbrev SwapGroup := Multiplicative (ZMod 2)
private abbrev WreathModule := SwapGroup → FourModule
private abbrev WreathGroup := RegularWreathProduct
  (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) SwapGroup

private def swapMatrix : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
  ⟨!![0, 1; 1, 0], by decide⟩

private def coordinateInvolution : WreathGroup :=
  ⟨fun coordinate => if coordinate = 1 then swapMatrix else 1, 1⟩

private theorem coordinateInvolution_square : coordinateInvolution ^ 2 = 1 := by
  rw [pow_two]
  apply RegularWreathProduct.ext
  · funext coordinate
    change (if coordinate = 1 then swapMatrix else 1) *
      (if (1 : SwapGroup)⁻¹ * coordinate = 1 then swapMatrix else 1) = 1
    simp only [inv_one, one_mul]
    split_ifs
    · apply Subtype.ext
      decide +kernel
    · exact one_mul 1
  · rfl

private theorem coordinateInvolution_ne_one : coordinateInvolution ≠ 1 := by
  intro heq
  have hentry := congrArg
    (fun element : WreathGroup => (element.left 1).1 0 0) heq
  change (0 : ZMod 2) = 1 at hentry
  exact zero_ne_one hentry

private theorem swap_fixed_card :
    Nat.card {vector : WreathModule //
      Matrix.mulVec swapMatrix.1 (vector 1).toAdd = (vector 1).toAdd} = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

public theorem oneJ_ne_bot_of_complementary_four_card_seventy_two
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (sylow : Sylow 2 K) (first second : Subgroup V)
    (hcompl : IsCompl first second)
    (hfirst : Nat.card first = 4) (hsecond : Nat.card second = 4)
    (hfaith : fixingSubgroup K (Set.univ : Set V) = ⊥)
    (hcard : Nat.card K = 72)
    (hperm : ∀ element : K,
      (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first ∧
       second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second) ∨
      (first.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = second ∧
       second.map (MulDistribMulAction.toMulAut K V element).toMonoidHom = first)) :
    oneJ (V := V) (sylow : Subgroup K) ≠ ⊥ := by
  obtain ⟨groupEquiv, moduleEquiv, hcompatible⟩ :=
    ComplementaryFourWreathAction.equiv_natural_wreath_of_complementary_four
      first second hcompl hfirst hsecond hfaith hcard hperm
  let actor := groupEquiv.symm coordinateInvolution
  have hsquare : actor ^ 2 = 1 := by
    apply groupEquiv.injective
    simpa [actor] using coordinateInvolution_square
  have hnontrivial : actor ≠ 1 := by
    intro hone
    apply coordinateInvolution_ne_one
    simpa [actor] using congrArg groupEquiv hone
  have hfixed (vector : V) :
      vector ∈ FixedPoints.subgroup (Subgroup.zpowers actor) V ↔
      Matrix.mulVec swapMatrix.1 (moduleEquiv vector 1).toAdd =
        (moduleEquiv vector 1).toAdd := by
    have hgenerator : vector ∈ FixedPoints.subgroup (Subgroup.zpowers actor) V ↔
        actor • vector = vector := by
      constructor
      · intro hvector
        exact hvector ⟨actor, Subgroup.mem_zpowers actor⟩
      · intro hvector member
        exact smul_eq_self_of_mem_zpowers member.property hvector
    rw [hgenerator]
    constructor
    · intro hvector
      have heq := hcompatible actor vector 1
      rw [hvector] at heq
      have heq' : moduleEquiv vector 1 =
          Multiplicative.ofAdd (Matrix.mulVec swapMatrix.1
            (moduleEquiv vector 1).toAdd) := by
        simpa [actor, coordinateInvolution] using heq
      exact (congrArg Multiplicative.toAdd heq').symm
    · intro hvector
      apply moduleEquiv.injective
      funext coordinate
      rw [hcompatible]
      simp only [actor, groupEquiv.apply_symm_apply, coordinateInvolution,
        inv_one, one_mul]
      by_cases hcoordinate : coordinate = 1
      · subst coordinate
        simp only [ite_true, hvector]
        rfl
      · simp [hcoordinate]
  have hfixedcard : Nat.card (FixedPoints.subgroup (Subgroup.zpowers actor) V) = 8 := by
    exact (Nat.card_congr (Equiv.subtypeEquiv moduleEquiv.toEquiv hfixed)).trans swap_fixed_card
  have hVcard : Nat.card V = 16 := by
    rw [Nat.card_congr moduleEquiv.toEquiv, Nat.card_fun]
    norm_num [Nat.card_fun]
  apply oneJ_ne_bot_of_involution_fixed_card_bound sylow actor hsquare hnontrivial
  rw [hfixedcard, hVcard]

public theorem nineCore_card_seventy_two_of_dvd
    {K : Type u} [Group K] [Finite K]
    (hoddcard : Nat.card (oddCore K) = 9)
    (actor : Subgroup K) (hactorcard : Nat.card actor = 4)
    (hdivides : Nat.card K ∣ 72) (hexcluded : Nat.card K ≠ 36) :
    Nat.card K = 72 := by
  have hnine : 9 ∣ Nat.card K := hoddcard ▸ (oddCore K).card_subgroup_dvd_card
  have hfour : 4 ∣ Nat.card K := hactorcard ▸ actor.card_subgroup_dvd_card
  have hthirtysix : 36 ∣ Nat.card K :=
    (show Nat.Coprime 9 4 by decide).mul_dvd_of_dvd_of_dvd hnine hfour
  have hpositive : 0 < Nat.card K := Nat.card_pos
  have hupper : Nat.card K ≤ 72 := Nat.le_of_dvd (by decide) hdivides
  obtain ⟨index, hindex⟩ := hthirtysix
  omega


end Stellmacher.SectionOne
