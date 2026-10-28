module
public import ABG.ChapterII.Section1.WreathedFusion
public import Theory.GroupTheory.WreathedThirtyTwo
public import Theory.GroupTheory.FrobeniusKernelNormalSubgroup
public import Theory.GroupTheory.CyclicNormalCentralizer
public import Theory.GroupTheory.PGroup.CyclicInvolution

/-!
# The central involution in a wreathed two-five group

For a group with Sylow two-subgroup C₄ wreath C₂ and order dividing 2^k·5,
ABG's two automizer indices cannot be six. The normal-complement fusion
case therefore supplies a normal two-complement of order dividing five.
The unique central Sylow involution lies in the Sylow commutator, hence
centralizes this cyclic complement and is central in the whole group.
Every automorphism fixes it, by uniqueness in the cyclic Sylow center.

Source: Alperin–Brauer–Gorenstein II.1 Proposition 2, pp.11–13; used for
the linear-three row of Aschbacher–Smith 5.1.13 and5.2.2, pp.637–638,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.WreathedTwoFive
variable {Y : Type*} [Group Y] [Finite Y]

private theorem normal_complement (S : Sylow 2 Y) (eS : S ≃* WreathedThirtyTwo)
    (h3 : ¬ 3 ∣ Nat.card Y) : HasNormalPComplement 2 Y := by
  have hS : ABG.IsWreathedOfHeight S 2 :=
    ABG.wreathed_equiv eS.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hS
  let U := P.U.map (S : Subgroup Y).subtype
  let V := P.V.map (S : Subgroup Y).subtype
  have hf := P.fusionFrame S
  have hu : ABG.automizerIndex U = 2 :=
    (ABG.Wreathed.u_automizer_index S 2 U V hf).resolve_right (by
      intro he
      apply h3
      exact (show 3 ∣ 6 by decide).trans (he ▸
        (relIndex_dvd_card (centralizer (U : Set Y)) (normalizer (U : Set Y))).trans
          (normalizer (U : Set Y)).card_subgroup_dvd_card))
  have hv : ABG.outerAutomizerIndex V = 2 :=
    (ABG.Wreathed.v_outer_automizer_index S 2 U V hf).resolve_right (by
      intro he
      apply h3
      exact (show 3 ∣ 6 by decide).trans (he ▸
        (relIndex_dvd_card (V ⊔ centralizer (V : Set Y)) (normalizer (V : Set Y))).trans
          (normalizer (V : Set Y)).card_subgroup_dvd_card))
  exact ABG.hasNormalTwoComplement_of_cyclic_focalSubgroupOf S (by
    rw [(ABG.Wreathed.focal_subgroup_cases S P).1 hu hv]
    exact P.derived_structure.2.1)

private theorem central_involution_derived
    {Q : Type*} [Group Q] [Finite Q] (e : Q ≃* WreathedThirtyTwo)
    (z : Q) (hz : orderOf z = 2) (hc : z ∈ center Q) : z ∈ commutator Q := by
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation
    (ABG.wreathed_equiv e.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight)
  let : IsCyclic (center Q) := P.center_cyclic
  have he : (⟨z,hc⟩ : center Q) = ⟨P.x,P.x_mem_center⟩ :=
    IsCyclic.eq_of_orderOf_eq_two ((orderOf_coe _).symm.trans hz)
      ((orderOf_coe _).symm.trans P.x_orderOf)
  have hzP : z = P.x := congrArg Subtype.val he
  rw [hzP,←P.r_half,P.derived_structure.1]
  exact (zpowers P.r).pow_mem (mem_zpowers _) _

/-- Every automorphism fixes the central Sylow involution in the two-five case. -/
theorem fixed_central_involution (S : Sylow 2 Y) (eS : S ≃* WreathedThirtyTwo)
    {k : ℕ} (hd : Nat.card Y ∣ 2^k*5)
    (z : S) (hz : orderOf z = 2) (hc : z ∈ center S) (φ : MulAut Y) :
    φ (z : Y) = z := by
  have h3 : ¬ 3 ∣ Nat.card Y := by
    intro h
    have hh := h.trans hd
    rcases Nat.prime_three.dvd_mul.mp hh with hh | hh
    · exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hh)
    · norm_num at hh
  obtain ⟨N,hN,hcop,hquot⟩ := normal_complement S eS h3
  let : N.Normal := hN
  have hN5 : Nat.card N ∣ 5 :=
    (hcop.symm.pow_right k).dvd_of_dvd_mul_left (N.card_subgroup_dvd_card.trans hd)
  let : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let : IsCyclic N := isCyclic_of_card_dvd_prime hN5
  have hzcomm : (z : Y) ∈ commutator Y := by
    have hh := mem_map_of_mem (S : Subgroup Y).subtype (central_involution_derived eS z hz hc)
    rw [map_commutator_eq] at hh
    exact commutator_mono le_top le_top hh
  have hzN : (z : Y) ∈ centralizer (N : Set Y) :=
    commutator_le_centralizer_of_isCyclic_normal N hzcomm
  have hzcentral : (z : Y) ∈ center Y := by
    apply mem_center_iff.mpr
    intro y
    have hall : N ⊔ (S : Subgroup Y) ≤ centralizer ({(z : Y)} : Set Y) := by
      apply sup_le
      · intro n hn
        exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzN) n hn)
      · intro s hs
        exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_center_iff.mp hc (⟨s,hs⟩ : S)))
    have hy := hall (show y ∈ N ⊔ (S : Subgroup Y) from by
      rw [sup_comm,S.sup_eq_top_of_quotient_isPGroup N hquot]; trivial)
    exact mem_centralizer_singleton_iff.mp hy
  have hpz : φ (z : Y) ∈ center Y := (centerCongr φ ⟨z,hzcentral⟩).property
  have hpord : orderOf (φ (z : Y)) = 2 := (φ.orderOf_eq _).trans ((orderOf_coe z).trans hz)
  have hps : φ (z : Y) ∈ S := by
    let Q := zpowers (φ (z : Y))
    have hQc : Q ≤ center Y := zpowers_le.mpr hpz
    let : Q.Normal := ⟨fun x hx g => by
      have hc := mem_center_iff.mp (hQc hx) g
      simpa only [hc,mul_inv_cancel_right] using hx⟩
    have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by
      simpa only [Q,Nat.card_zpowers,pow_one] using hpord)
    exact hQp.le_sylow_of_normal S (mem_zpowers _)
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation
    (ABG.wreathed_equiv eS.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight)
  let : IsCyclic (center S) := P.center_cyclic
  let zz : center S := ⟨z,hc⟩
  let ww : center S := ⟨⟨φ z,hps⟩,mem_center_iff.mpr
    (fun s => Subtype.ext (mem_center_iff.mp hpz s))⟩
  have he : ww = zz := IsCyclic.eq_of_orderOf_eq_two
    ((orderOf_coe ww).symm.trans ((orderOf_coe ww.val).symm.trans hpord))
    ((orderOf_coe zz).symm.trans hz)
  exact congrArg (fun x : center S => x.val.val) he
end Theory.GroupTheory.WreathedTwoFive
