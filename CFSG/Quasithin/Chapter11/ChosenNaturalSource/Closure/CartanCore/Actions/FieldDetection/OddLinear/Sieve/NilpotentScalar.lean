module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Sieve.NilpotentPrimary
public import Theory.SpecificGroups.GL2.NoncommutativeCentralizer
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.GroupAction.CoprimeTwoOuter
public import Theory.SpecificGroups.PSL2.OuterSolvable.SmallDegreeTwoGroup

/-!
# The surviving nilpotent primary actors are scalars

A coprime automorphism fixes the SL₂(5) Fitting quotient. Indeed, its action
on the central PSL₂(5) quotient is trivial by the two-group outer theorem,
and perfectness detects the automorphism there. The literal primary
Frattini action has Fitting kernel, so the coprime actor centralizes its
image. This image contains Q₈ and is noncommutative. Its centralizer in
GL₂(p) consists of scalar matrices; consequently each primary actor has
order dividing p−1.

These statements retain every homocyclic exponent, extraspecial factor,
and the actual component and quotient actions. They do not assert that
such scalar actors are trivial. The remaining ambient exclusion and
11.5.6(3) assembly stay with qt-d-1222-natural-closure-cartan; the original
Geometry application is in `Sieve.Nilpotent`.
Source: Aschbacher--Smith A.3.6(4), pp.43--45, and 11.5.6(3), pp.780--781.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

/-- A coprime actor fixes the actual SL₂(5) Fitting quotient. -/
theorem nilpotent_quotient_actor_eq_one {Q : Type*} [Group Q] [Finite Q]
    (hn : A36Nilpotent Q) (hc : A36Common Q) (a : MulAut Q)
    (hcop : Nat.Coprime (orderOf a) (Nat.card Q)) :
    quotientAut (fittingSubgroup Q) a = 1 := by
  let R := Q ⧸ fittingSubgroup Q
  let : IsQuasisimple R := hc.2.1
  obtain ⟨F,_,_,hF,⟨e₀⟩⟩ := hn.2.2.1
  let e : R ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    (QuotientGroup.quotientMulEquivOfEq hn.1).symm.trans e₀
  let eZ : (R ⧸ center R) ≃* Theory.PSL2.Group F :=
    QuotientGroup.congr _ _ e (by
      ext z
      constructor
      · rintro ⟨w,hw,rfl⟩
        exact (centerCongr e ⟨w,hw⟩).property
      · intro hz
        exact ⟨e.symm z,(centerCongr e.symm ⟨z,hz⟩).property,e.apply_symm_apply z⟩)
  let b := quotientAut (fittingSubgroup Q) a
  let f := MulAut.centralQuotientAction eZ
  have hdiv : Nat.card (Theory.PSL2.Group F) ∣ Nat.card Q := by
    rw [← Nat.card_congr eZ.toEquiv]
    exact (center R).card_quotient_dvd_card.trans (fittingSubgroup Q).card_quotient_dvd_card
  have h120 : 120 ∣ Nat.card Q := by
    have hR : Nat.card R = 120 := by
      rw [Nat.card_congr e.toEquiv,Atlas.card_sl_two,hF]
      norm_num
    exact hR ▸ (fittingSubgroup Q).card_quotient_dvd_card
  have hd : orderOf (f b) ∣ orderOf a :=
    (orderOf_map_dvd f b).trans (orderOf_map_dvd (quotientAut (fittingSubgroup Q)) a)
  have ho : Odd (orderOf (f b)) :=
    (Nat.coprime_two_right.mp (hcop.of_dvd_right
      ((by norm_num : 2 ∣ 120).trans h120))).of_dvd_nat hd
  have hf : f b = 1 := MulAut.eq_one_of_odd_coprime_of_outer_two _ ho
    (hcop.of_dvd hd hdiv)
    (Theory.PSL2.OuterSolvable.SmallDegreeSquares.outer_isPGroup_two
      (p := 5) (n := 1) (by decide) (by decide) (by decide) (by simpa using hF))
  exact MulAut.centralQuotientAction_injective eZ (hf.trans (map_one f).symm)

/-- The actual primary actor centralizes the full component action image. -/
theorem nilpotent_primary_actor_centralizes {Q : Type*} [Group Q] [Finite Q]
    [Group.IsPerfect Q] (hn : A36Nilpotent Q) (hc : A36Common Q)
    (a : MulAut Q) (hcop : Nat.Coprime (orderOf a) (Nat.card Q))
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (fittingSubgroup Q)) :
    primaryFrattiniAut p Q a ∈
      centralizer ((FittingActions.coreFrattiniAction p Q).range :
        Set (MulAut (pCore p Q ⧸ frattini (pCore p Q)))) := by
  have hquot := nilpotent_quotient_actor_eq_one hn hc a hcop
  have hk := ((FittingActions.nilpotent_frattini_actions hn hc).2.2 p hd).2.1
  apply mem_centralizer_iff.mpr
  rintro b ⟨g,rfl⟩
  have hg := DFunLike.congr_fun hquot (QuotientGroup.mk' (fittingSubgroup Q) g)
  rw [quotientAut_apply_mk] at hg
  have hm : g⁻¹ * a g ∈ (FittingActions.coreFrattiniAction p Q).ker := by
    rw [hk]
    exact QuotientGroup.eq.mp hg.symm
  have he : FittingActions.coreFrattiniAction p Q (a g) =
      FittingActions.coreFrattiniAction p Q g := by
    have hh := MonoidHom.mem_ker.mp hm
    rw [map_mul,map_inv] at hh
    exact (inv_mul_eq_one.mp hh).symm
  have hconj := primaryFrattiniAut_conjugation p a g
  rw [he] at hconj
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

/-- A faithful linear realization sends the actual primary actor to a scalar. -/
theorem nilpotent_primary_actor_scalar {Q : Type*} [Group Q] [Finite Q]
    [Group.IsPerfect Q] (hn : A36Nilpotent Q) (hc : A36Common Q)
    (a : MulAut Q) (hcop : Nat.Coprime (orderOf a) (Nat.card Q))
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (fittingSubgroup Q)) :
    ∃ f : MulAut (pCore p Q ⧸ frattini (pCore p Q)) →*
        Matrix.GeneralLinearGroup (Fin 2) (ZMod p), Function.Injective f ∧
      ∃ u : (ZMod p)ˣ, Matrix.GeneralLinearGroup.scalar (Fin 2) u =
        f (primaryFrattiniAut p Q a) := by
  obtain ⟨hel,hcard⟩ := nilpotent_primary_frattini_shape hn hd
  let := hel
  let V := pCore p Q ⧸ frattini (pCore p Q)
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := p) (n := 2) V hcard.le
  let r := FittingActions.coreFrattiniAction p Q
  let U := r.range.map f
  have hnU : ¬ IsMulCommutative U := by
    intro hU
    let := hU
    let e := r.range.equivMapOfInjective f hf
    have hcomm : IsMulCommutative r.range := IsMulCommutative.of_comm (fun x y =>
      e.injective (by rw [map_mul, map_mul]; exact hU.is_comm.comm _ _))
    let := hcomm
    let S : Sylow 2 Q := Classical.arbitrary _
    obtain ⟨j,hj⟩ := (((FittingActions.nilpotent_frattini_actions hn hc).2.2 p hd).2.2.2 S).2
    have hle : (r.comp (S : Subgroup Q).subtype).range ≤ r.range := by
      rintro x ⟨s,rfl⟩
      exact ⟨s,rfl⟩
    let j' := (inclusion hle).comp j
    have h := ((inclusion_injective hle).comp hj) (show
      j' ((QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0) =
        j' ((QuaternionGroup.xa 0 : QuaternionGroup 2) * .a 1) by
      rw [map_mul, map_mul]
      exact hcomm.is_comm.comm _ _)
    exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) * .xa 0 ≠ .xa 0 * .a 1) h
  have hcent : f (primaryFrattiniAut p Q a) ∈
      centralizer (U : Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) := by
    apply mem_centralizer_iff.mpr
    rintro x ⟨b,hb,rfl⟩
    rw [← map_mul,← map_mul]
    exact congrArg f (mem_centralizer_iff.mp
      (nilpotent_primary_actor_centralizes hn hc a hcop hd) b hb)
  obtain ⟨u,hu⟩ := Matrix.GeneralLinearGroup.centralizer_le_scalar_of_noncommutative U hnU hcent
  exact ⟨f,hf,u,hu⟩

/-- Every primary action has order dividing the scalar group order. -/
theorem nilpotent_primary_actor_order_dvd {Q : Type*} [Group Q] [Finite Q]
    [Group.IsPerfect Q] (hn : A36Nilpotent Q) (hc : A36Common Q)
    (a : MulAut Q) (hcop : Nat.Coprime (orderOf a) (Nat.card Q))
    {p : ℕ} [Fact p.Prime] (hd : p ∣ Nat.card (fittingSubgroup Q)) :
    orderOf (primaryFrattiniAut p Q a) ∣ p - 1 := by
  obtain ⟨f,hf,u,hu⟩ := nilpotent_primary_actor_scalar hn hc a hcop hd
  rw [← orderOf_injective f hf,← hu]
  exact (orderOf_map_dvd (Matrix.GeneralLinearGroup.scalar (Fin 2)) u).trans (by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_units,ZMod.card] using orderOf_dvd_natCard u)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
