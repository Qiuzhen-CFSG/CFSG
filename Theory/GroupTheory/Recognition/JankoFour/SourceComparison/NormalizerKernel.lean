module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.NormalizerActions
public import Theory.GroupTheory.PerfectCentralCoverActions

/-!
# The retained central kernel of the cubic normalizer action

The original normalizer projection onto Aut(M₂₂) has kernel A Z(H), and
perfectness gives exactly the same kernel for conjugation on the six-cover.
Consequently equal actors differ by this literal central attachment. The
quotient equivalence retains its original map and relative normality.

This is the action-kernel clause in AS91 (8.3), p.606. Together with the
separate N → H/Q calculation, it distinguishes the six-element action
kernel from the two-element kernel of that quotient map.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu PerfectCentralCovering
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))

include h in
/-- The full actor kernel keeps both the scalar cubic and central involution. -/
theorem cubicNormalizerProjection_ker :
    (cubicNormalizerProjection e X).ker =
      (cubicCenterInH e X).subgroupOf (cubicNormalizerInH e X) := by
  ext n
  change e.projection (QuotientGroup.mk' (core z) n.val) = 1 ↔ n.val ∈ cubicCenterInH e X
  constructor
  · intro hn
    obtain ⟨a,ha,han⟩ := (cubicSylow_map_coreQuotient h e X).ge hn
    have hnQ : n.val * a⁻¹ ∈ core z := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (core z) (n.val*a⁻¹)=1
      rw [map_mul,map_inv,han,mul_inv_cancel]
    have hnN : n.val*a⁻¹ ∈ cubicNormalizerInH e X :=
      mul_mem n.property (inv_mem ((cubicSylowImage e X).le_normalizer ha))
    have hnZ := (core_inf_cubicNormalizer h e X).le ⟨hnQ,hnN⟩
    have hm : (n.val*a⁻¹)*a ∈ cubicCenterInH e X := mul_mem
      ((le_sup_right : center (centralizer z) ≤ cubicCenterInH e X) hnZ)
      ((le_sup_left : cubicSylowImage e X ≤ cubicCenterInH e X) ha)
    simpa only [inv_mul_cancel_right] using hm
  · intro hn
    have hk := (cubicCentralizerProjection_ker h e X).ge (show
      (⟨n.val,cubicCenterInH_le h e X hn⟩ : cubicCentralizerInH e X) ∈
        (cubicCenterInH e X).subgroupOf (cubicCentralizerInH e X) from hn)
    have he := cubicCentralizerProjection_conj h e X
      ⟨n.val,cubicCenterInH_le h e X hn⟩
    rw [show cubicCentralizerProjection h e X _ = 1 from hk,map_one] at he
    exact he.symm

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))

include h hp in
/-- The kernel of the conjugation action is exactly the same actual six-element subgroup. -/
theorem cubicNormalizerAction_ker :
    (cubicNormalizerAction e X).ker =
      (cubicCenterInH e X).subgroupOf (cubicNormalizerInH e X) :=
  ((cubicCentralizerCover h e X hp).equivariantActions_ker
    (cubicNormalizerAction e X) (cubicNormalizerProjection e X)
    (cubicNormalizerAction_projection h e X)).trans (cubicNormalizerProjection_ker h e X)

include h hp in
/-- Equal normalizer actions differ by precisely the retained central attachment. -/
theorem cubicNormalizerAction_eq_iff (m n : cubicNormalizerInH e X) :
    cubicNormalizerAction e X m = cubicNormalizerAction e X n ↔
      m.val*n.val⁻¹ ∈ cubicCenterInH e X := by
  rw [← mul_inv_eq_one,← map_inv,← map_mul,← MonoidHom.mem_ker,cubicNormalizerAction_ker h e X hp]
  rfl

instance cubicCenterInH_normal_in_normalizer :
    ((cubicCenterInH e X).subgroupOf (cubicNormalizerInH e X)).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  exact (le_inf le_rfl le_normalizer_of_normal).trans
    (normalizer_inf_normalizer_le_normalizer_sup (cubicSylowImage e X) (center (centralizer z)))

/-- The quotient by the entire action kernel is literally Aut(M22). -/
noncomputable def cubicNormalizerActionQuotientEquiv :
    (cubicNormalizerInH e X ⧸
      (cubicCenterInH e X).subgroupOf (cubicNormalizerInH e X)) ≃* MulAut M22 :=
  (QuotientGroup.quotientMulEquivOfEq (cubicNormalizerProjection_ker h e X).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (cubicNormalizerProjection e X)
      (cubicNormalizerProjection_surjective h e X))

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
