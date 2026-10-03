module
public import Stellmacher.SectionThree.CentralCoatomInvolutionCard
public import Theory.GroupAction.NormalizingActor

/-!
# Square power-of-two displacement for a central coatom

Retain the finite elementary-two module and central-coatom generation
hypotheses of `central_coatom_involution_module_card_eq_square`. For every
b in the central coatom, the cyclic displacement of its actual action has
order 2^(2*n) for some n. There is no module-order bound and no additional
faithfulness or action-kernel premise.

The image of b commutes with the entire action image, so its displacement
T is invariant under that image. Restrict the literal original action to T,
using this same invariance instance. The central-coatom image remains
central, the residual still has trivial fixed subgroup, and the selected
actor still squares to one. The existing exact-square theorem applied to
T says its order is a square. The smaller displacement whose order is
squared is a two-group, giving the claimed even exponent.

This supplies the central-actor displacement count in Stellmacher (8.6),
source (17), printed p.44 of `refs/files/stellmacher-n-group.pdf`. The actual
quotient action and the later numerical bound are separate graph inputs.
-/

namespace Stellmacher.SectionThree
open scoped IsMulCommutative

public theorem central_coatom_displacement_card_is_square_power
    {K V : Type*} [Group K] [Finite K] [Group V] [Finite V]
    [IsElementaryAbelian 2 V]
    (action : K →* MulAut V) (A A0 : Subgroup K) (a x : K)
    (hgen : (⊤ : Subgroup K) = A ⊔ A.conjBy x)
    (hA : A = Subgroup.zpowers a ⊔ A0)
    (htwo : IsPGroup 2 A0)
    (hcentral : A0.map action ≤ Subgroup.centralizer (action.range : Set (MulAut V)))
    (hfixed : FixedPoints.subgroup ((twoResidualAmbient (⊤ : Subgroup K)).map action) V = ⊥)
    (hsquare : (action a) ^ 2 = 1)
    (b : K) (hb : b ∈ A0) :
    ∃ n : ℕ, Nat.card (commutatorAction (Subgroup.zpowers (action b)) V) = 2 ^ (2 * n) := by
  let R := action.range
  let B := Subgroup.zpowers (action b)
  let T := commutatorAction B V
  have hbcentral : action b ∈ Subgroup.centralizer (R : Set (MulAut V)) :=
    hcentral (Subgroup.mem_map_of_mem action hb)
  have hnormal : R ≤ Subgroup.normalizer (B : Set (MulAut V)) :=
    (Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hbcentral)).trans
      (Subgroup.centralizer_le_normalizer _)
  let _ : IsInvariant R V T := commutatorAction_isInvariant_of_normalizing_actor R B hnormal
  let restricted : K →* MulAut T :=
    (MulDistribMulAction.toMulAut R T).comp action.rangeRestrict
  let _ : IsElementaryAbelian 2 T := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun point =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 V) (point : V)) }
  have hrestrictedCentral : A0.map restricted ≤
      Subgroup.centralizer (restricted.range : Set (MulAut T)) := by
    rintro mover ⟨lift,hlift,rfl⟩ other ⟨actor,rfl⟩
    ext point
    change action actor (action lift (point : V)) = action lift (action actor (point : V))
    exact DFunLike.congr_fun
      (hcentral (Subgroup.mem_map_of_mem action hlift) _ ⟨actor,rfl⟩) (point : V)
  have hrestrictedFixed :
      FixedPoints.subgroup ((twoResidualAmbient (⊤ : Subgroup K)).map restricted) T = ⊥ := by
    apply bot_unique
    intro point hpoint
    have hpointFixed : (point : V) ∈
        FixedPoints.subgroup ((twoResidualAmbient (⊤ : Subgroup K)).map action) V := by
      intro mover
      obtain ⟨lift,hlift,hEq⟩ := mover.property
      have hh := hpoint
        ⟨restricted lift,Subgroup.mem_map_of_mem restricted hlift⟩
      change (mover : MulAut V) (point : V) = point
      rw [← hEq]
      exact congrArg Subtype.val hh
    rw [hfixed] at hpointFixed
    exact Subtype.ext hpointFixed
  have hrestrictedSquare : (restricted a) ^ 2 = 1 := by
    ext point
    change action a (action a (point : V)) = point
    exact DFunLike.congr_fun hsquare (point : V)
  have hsquared := central_coatom_involution_module_card_eq_square
    restricted A A0 a x hgen hA htwo hrestrictedCentral hrestrictedFixed hrestrictedSquare
  obtain ⟨n,hn⟩ := ((IsElementaryAbelian.isPGroup 2 T).to_subgroup
    (commutatorAction (Subgroup.zpowers (restricted a)) T)).exists_card_eq
  refine ⟨n,?_⟩
  change Nat.card T = 2 ^ (2 * n)
  rw [hsquared,hn,← pow_mul,Nat.mul_comm n 2]

end Stellmacher.SectionThree
