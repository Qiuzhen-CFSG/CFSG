module
public import Stellmacher.SectionOne.CoreKernelTransvectionFactor
public import Stellmacher.SectionOne.OneSevenInvariantFourDisplacement
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# Involutions fixing an invariant plane in a sixteen-element module

For a finite solvable core-kernel action on an elementary group of order
sixteen, let a two-subgroup in the actual automorphism range have order greater
than four and preserve a plane of order four. Every supplied involution fixing
that plane has all its displacement in the plane. The original action and
plane are retained, and the involution need not belong to the two-subgroup.

Involution rank-nullity bounds displacement by four. Displacement of order
four exhausts the fixed subgroup and hence the plane; trivial displacement
is immediate. For order two, the core-kernel factor theorem supplies a canonical
factor containing the actor. The large two-subgroup moves its support to a
complementary support, and the invariant-four displacement theorem places the
line in the original plane. This proves the local action containment needed
before the triple-intersection commutativity step in Stellmacher (9.10),
Journal of Algebra 190 (1997), printed p.58.
-/

namespace Stellmacher.SectionOne
universe u

set_option maxHeartbeats 800000 in
public theorem core_kernel_involution_displacement_le_invariant_four
    {P W : Type u} [Group P] [Finite P] [Group W] [Finite W]
    [IsElementaryAbelian 2 W]
    (hsolv : Group.IsSolvable P) (action : P →* MulAut W)
    (hkernel : action.ker = pCore 2 P) (hW : Nat.card W = 16)
    (S : Subgroup action.range) (hS : IsPGroup 2 S) (hlarge : 4 < Nat.card S)
    (I : Subgroup W) (hI : Nat.card I = 4)
    (hInv : ∀ s:S, ∀ w∈I, (s:action.range).val w∈I)
    (actor : P) (hsquare : (action actor)^2 = 1)
    (hfix : ∀ w∈I, action actor w=w) :
    commutatorAction (Subgroup.zpowers (action actor)) W ≤ I := by
  classical
  let a := action actor
  let A := Subgroup.zpowers a
  let R := commutatorAction A W
  by_cases hone : a=1
  · rw [show action actor=1 from hone]
    rw [commutatorAction_eq_closure,Subgroup.closure_le]
    rintro w ⟨mover,vector,rfl⟩
    have hm : (mover:MulAut W)=1 := by
      obtain ⟨n,hn⟩ := mover.property
      simpa using hn.symm
    change vector⁻¹*(mover:MulAut W) vector∈I
    rw [hm]
    simp
  have hA : Nat.card A=2 := by rw [Nat.card_zpowers,orderOf_eq_prime hsquare hone]
  let generator : A := ⟨a,Subgroup.mem_zpowers a⟩
  let _ : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [hW]; decide)
  obtain ⟨hprod,hRC⟩ := card_two_action_fixed_commutator_card_data (U:=W)
    generator ⟨fun heq => hone (congrArg Subtype.val heq),Subtype.ext hsquare⟩ hA
  let C := FixedPoints.subgroup A W
  change Nat.card W=Nat.card C*Nat.card R at hprod
  change R≤C at hRC
  have hIC : I≤C := by
    intro w hw mover
    exact smul_eq_self_of_mem_zpowers mover.property (hfix w hw)
  have hClower : 4≤Nat.card C := hI ▸ Subgroup.card_le_of_le hIC
  have hRupper : Nat.card R≤4 := by rw [hW] at hprod; nlinarith
  have hRpos : 0<Nat.card R := Nat.card_pos
  have hRdvd : Nat.card R∣16 := hW ▸ R.card_subgroup_dvd_card
  have hRcases : Nat.card R=1 ∨ Nat.card R=2 ∨ Nat.card R=4 := by
    rw [hW] at hprod
    interval_cases h : Nat.card R <;> omega
  rcases hRcases with hRone | hRtwo | hRfour
  · have hbot : R=⊥ := Subgroup.card_eq_one.mp hRone
    change R≤I
    rw [hbot]
    exact bot_le
  · obtain ⟨hyp,hD⟩ := core_kernel_transvection_factor hsolv action hkernel actor hRtwo
    let D := ⁅oddCore action.range,Subgroup.zpowers (action.rangeRestrict actor)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict actor)
    obtain ⟨c,hmove,hspan⟩ := oneSevenFactor_exists_complementary_two_group_conjugate
      hyp D S hD hS hW hlarge
    have hImap : I.map ((c:action.range):MulAut W).toMonoidHom=I := by
      apply le_antisymm
      · rintro w ⟨v,hv,rfl⟩
        exact hInv c v hv
      · intro w hw
        refine ⟨((c:action.range):MulAut W).symm w,hInv c⁻¹ w hw,?_⟩
        exact MulEquiv.apply_symm_apply _ w
    exact oneSevenFactor_displacement_le_invariant_four action.range hyp D hD
      (action.rangeRestrict actor) (c:action.range)
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) hRtwo hmove hspan I hI
      (fun w hw => (hfix w hw).symm ▸ hw) hImap
  · have hCfour : Nat.card C=4 := by rw [hW,hRfour] at hprod; omega
    have hRI : R=I :=
      (Subgroup.eq_of_le_of_card_ge hRC (by rw [hCfour,hRfour])).trans
        (Subgroup.eq_of_le_of_card_ge hIC (by rw [hI,hCfour])).symm
    change R≤I
    exact hRI.le

end Stellmacher.SectionOne
