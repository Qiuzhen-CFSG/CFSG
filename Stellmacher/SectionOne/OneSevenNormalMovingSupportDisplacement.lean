module
public import Theory.GroupAction.SwappedSupportCommutatorLowerBound
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# A support-moving normal subgroup has at least eight displacements

In a sixteen-point canonical one-seven module, let N be normalized by S.
Suppose S contains a rank-one actor in a supplied factor and N contains an
actor moving that factor's support to a distinct one. Then N has displacement
of cardinal at least eight, even if N is a proper subgroup of S.

Normality puts the commutator of the moving actor with the rank-one actor in
N. On the original support this commutator acts as the rank-one actor, since
the conjugate factor fixes that support. The rank-one actor fixes the other
support, so its entire displacement line lies in N's displacement. The
moving actor contributes a disjoint order-four difference image, giving the
order-eight bound without identifying N with the whole Sylow subgroup.

This supplies a direct normal-subgroup alternative to the compressed edge
generation inference in Stellmacher (9.10)(10), sufficient for (12), printed
pp.58–59.
-/
open scoped IsMulCommutative
namespace Stellmacher.SectionOne
universe u

public theorem oneSevenFactor_normal_subgroup_moving_support_commutator_card_ge_eight
    {K V : Type u} [Group K] [Group V] [Finite K] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction K V]
    (hyp : Hypotheses K V) (D S N : Subgroup K)
    (hD : IsOneSevenFactor (V := V) D) (hV : Nat.card V = 16)
    (hnormal : S ≤ Subgroup.normalizer (N : Set K))
    (a : K) (haD : a ∈ D) (haS : a ∈ S)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers a) V) = 2)
    (c : K) (hc : c ∈ N)
    (hmove : commutatorAction D V ≠ (commutatorAction D V).map
      (MulDistribMulAction.toMulAut K V c).toMonoidHom) :
    8 ≤ Nat.card (commutatorAction N V) := by
  let E := D.conjBy c
  let U := commutatorAction D V
  let U' := commutatorAction E V
  let R := commutatorAction (Subgroup.zpowers a) V
  let F := commutatorAction N V
  have hE := hD.conjBy D c
  have hmap : U.map (MulDistribMulAction.toMulAut K V c).toMonoidHom = U' :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D c
  have hDE : D ≠ E := by
    intro heq
    apply hmove
    rw [hmap]
    exact congrArg (fun J : Subgroup K => commutatorAction J V) heq
  have hdisjoint : Disjoint U U' := oneSevenFactor_support_disjoint_of_ne hyp D E hD hE hDE
  have hspan : U ⊔ U' = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge le_top
    have hh := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint U U'
      (by rw [Subgroup.normalizer_eq_top]; exact le_top) hdisjoint
    rw [hD.2.2.1, hE.2.2.1] at hh
    rw [hh, Nat.card_congr (Subgroup.topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv, hV]
  have hUfixed : U ≤ FixedPoints.subgroup E V :=
    oneSevenFactor_commutatorAction_le_fixedPoints hyp E D hE hD hDE.symm
  have hU'fixed : U' ≤ FixedPoints.subgroup D V :=
    oneSevenFactor_commutatorAction_le_fixedPoints hyp D E hD hE hDE
  have hUinvariant : IsInvariant D V U :=
    commutatorAction_isInvariant_of_normalizing_actor D D D.le_normalizer
  let d := c * a⁻¹ * c⁻¹ * a
  have hd : d ∈ N := by
    have hh := N.mul_mem hc (Subgroup.le_normalizer_iff.mp hnormal a⁻¹
      (S.inv_mem haS) c⁻¹ (N.inv_mem hc))
    simpa only [d, inv_inv, mul_assoc] using hh
  have hconjugate : c * a⁻¹ * c⁻¹ ∈ E :=
    Subgroup.mem_map_of_mem (MulAut.conj c).toMonoidHom (D.inv_mem haD)
  have hdAction (point : V) (hpoint : point ∈ U) : d • point = a • point := by
    change (c * a⁻¹ * c⁻¹ * a) • point = a • point
    rw [mul_smul]
    exact ((FixedPoints.mem_subgroup (M := E) (a := a • point)).mp
      (hUfixed ((hUinvariant.invariant ⟨a, haD⟩ point).mp hpoint))) ⟨_, hconjugate⟩
  have hpointwise (point : V) : point⁻¹ * (a • point) ∈ F := by
    have hpoint : point ∈ U ⊔ U' := hspan.symm ▸ Subgroup.mem_top point
    obtain ⟨left, hleft, right, hright, rfl⟩ := Subgroup.mem_sup.mp hpoint
    have hfix : a • right = right :=
      ((FixedPoints.mem_subgroup (M := D) (a := right)).mp (hU'fixed hright)) ⟨a, haD⟩
    have hmem : left⁻¹ * (d • left) ∈ F := by
      change left⁻¹ * (d • left) ∈ commutatorAction N V
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨⟨d, hd⟩, left, rfl⟩
    rw [hdAction left hleft] at hmem
    have heq : (left * right)⁻¹ * (a • (left * right)) = left⁻¹ * (a • left) := by
      rw [smul_mul', hfix, mul_inv_rev]
      calc
        right⁻¹ * left⁻¹ * (a • left * right) =
            right⁻¹ * right * (left⁻¹ * (a • left)) := by ac_rfl
        _ = left⁻¹ * (a • left) := by rw [inv_mul_cancel, one_mul]
    rw [heq]
    exact hmem
  let fixing : Subgroup K :=
    { carrier := {actor | ∀ point : V, point⁻¹ * (actor • point) ∈ F}
      one_mem' := by intro point; simp
      mul_mem' := by
        intro first second hfirst hsecond point
        have hh := F.mul_mem (hsecond point) (hfirst (second • point))
        simpa only [mul_smul, mul_assoc, mul_inv_cancel_left] using hh
      inv_mem' := by
        intro actor hactor point
        have hh := F.inv_mem (hactor (actor⁻¹ • point))
        simpa only [smul_inv_smul, mul_inv_rev, inv_inv] using hh }
  have hcyclic : Subgroup.zpowers a ≤ fixing := Subgroup.zpowers_le.mpr hpointwise
  have hRF : R ≤ F := by
    change commutatorAction (Subgroup.zpowers a) V ≤ F
    rw [commutatorAction_eq_closure, Subgroup.closure_le]
    rintro point ⟨actor, vector, rfl⟩
    exact hcyclic actor.property vector
  have hRU : R ≤ U := by
    change commutatorAction (Subgroup.zpowers a) V ≤ commutatorAction D V
    rw [commutatorAction_eq_closure, commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro point ⟨actor, vector, rfl⟩
    exact ⟨⟨actor, (Subgroup.zpowers_le.mpr haD) actor.property⟩, vector, rfl⟩
  exact commutatorAction_card_ge_eight_of_swapped_support_line N U R c hc hD.2.2.1
    hrank hRU hRF (hmap.symm ▸ hdisjoint)

end Stellmacher.SectionOne
