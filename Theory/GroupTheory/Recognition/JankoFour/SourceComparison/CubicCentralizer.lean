module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.Defs
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicCentralizer
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original perfect six-cover in the J₄ centralizer

Restrict the original map H → H/Q → Aut(M₂₂) to C_H(A). Its image is M₂₂
and its kernel is exactly A Z(H). The fixed-core identity C_Q(A) = Z(H)
proves the kernel assertion without discarding either central factor.
The independently supplied perfectness then identifies this kernel with
Z(C_H(A)), of order six, and proves quasisimplicity.

This is the literal cover used by the comparison in AS91 (8.3), printed
p.606, using (4.1) and the perfectness clause of (4.9). It does not infer
perfectness of a central extension from perfectness of its quotient.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison
open Subgroup SourceRecognition LocalGeometry Sporadic.Mathieu
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {z : G}
variable (h : IsTypeJ4 z)
variable (e : CubicAutomorphismQuotient (centralizer z ⧸ core z))
variable (X : Sylow 3 (CubicLift.subgroup e))
include h

theorem cubicSylowImage_card : Nat.card (cubicSylowImage e X) = 3 := by
  rw [cubicSylowImage, card_map_of_injective (CubicLift.subgroup e).subtype_injective]
  exact cubicSylow_card e h X

theorem cubicSylowImage_le_centralizer : cubicSylowImage e X ≤ cubicCentralizerInH e X := by
  let : IsCyclic (cubicSylowImage e X) := isCyclic_of_prime_card (cubicSylowImage_card h e X)
  exact le_centralizer_iff_isMulCommutative.mpr inferInstance

/-- The original centralizer maps onto the triple cover through H/Q. -/
noncomputable def cubicCentralizerToInner : cubicCentralizerInH e X →* innerPreimage e :=
  ((QuotientGroup.mk' (core z)).comp (cubicCentralizerInH e X).subtype).codRestrict
    (innerPreimage e) (fun c =>
      (cubicCentralizer_map_coreQuotient h e X).le (mem_map_of_mem _ c.property))

@[simp] theorem cubicCentralizerToInner_apply (c : cubicCentralizerInH e X) :
    (cubicCentralizerToInner h e X c : centralizer z ⧸ core z) =
      QuotientGroup.mk' (core z) c.val := rfl

theorem cubicCentralizerToInner_surjective : Function.Surjective (cubicCentralizerToInner h e X) := by
  intro y
  obtain ⟨g,hg,hgy⟩ := (cubicCentralizer_map_coreQuotient h e X).ge y.property
  exact ⟨⟨g,hg⟩, Subtype.ext hgy⟩

theorem cubicCentralizerToInner_ker :
    (cubicCentralizerToInner h e X).ker =
      (center (centralizer z)).subgroupOf (cubicCentralizerInH e X) := by
  ext c
  change cubicCentralizerToInner h e X c = 1 ↔ c.val ∈ center (centralizer z)
  constructor
  · intro hc
    have hQ : c.val ∈ core z := (QuotientGroup.eq_one_iff c.val).mp
      (congrArg Subtype.val hc)
    rw [← core_center_eq_centralizer_center h]
    exact mem_map_of_mem (core z).subtype
      ((core_cubic_centralizer h e X).le (show
        (⟨c.val,hQ⟩ : core z) ∈ (cubicCentralizerInH e X).subgroupOf (core z) from c.property))
  · intro hc
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff c.val).mpr (centralizer_center_le_core h hc)

/-- The cubic scalar together with the original central involution. -/
noncomputable def cubicCenterInH : Subgroup (centralizer z) :=
  cubicSylowImage e X ⊔ center (centralizer z)

theorem cubicCenterInH_le : cubicCenterInH e X ≤ cubicCentralizerInH e X :=
  sup_le (cubicSylowImage_le_centralizer h e X) (center_le_centralizer _)

/-- The literal projection of the original centralizer onto M₂₂. -/
noncomputable def cubicCentralizerProjection : cubicCentralizerInH e X →* M22 :=
  (innerProjection e).comp (cubicCentralizerToInner h e X)

theorem cubicCentralizerProjection_surjective :
    Function.Surjective (cubicCentralizerProjection h e X) :=
  (innerProjection_surjective e).comp (cubicCentralizerToInner_surjective h e X)

/-- The kernel keeps both central factors; neither is killed in the carrier. -/
theorem cubicCentralizerProjection_ker :
    (cubicCentralizerProjection h e X).ker =
      (cubicCenterInH e X).subgroupOf (cubicCentralizerInH e X) := by
  ext c
  change innerProjection e (cubicCentralizerToInner h e X c) = 1 ↔
    c.val ∈ cubicCenterInH e X
  rw [← MonoidHom.mem_ker, innerProjection_ker_iff]
  constructor
  · intro hc
    obtain ⟨x,hx,hxc⟩ := (cubicSylow_map_coreQuotient h e X).ge hc
    have hcQ : c.val * x⁻¹ ∈ core z := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' (core z) (c.val * x⁻¹) = 1
      rw [map_mul, map_inv, hxc]
      exact mul_inv_cancel _
    have hcC : c.val * x⁻¹ ∈ cubicCentralizerInH e X :=
      mul_mem c.property (inv_mem (cubicSylowImage_le_centralizer h e X hx))
    have hcZ : c.val * x⁻¹ ∈ center (centralizer z) := by
      rw [← core_center_eq_centralizer_center h]
      exact mem_map_of_mem (core z).subtype
        ((core_cubic_centralizer h e X).le (show
          (⟨c.val * x⁻¹,hcQ⟩ : core z) ∈
            (cubicCentralizerInH e X).subgroupOf (core z) from hcC))
    have hm : (c.val * x⁻¹) * x ∈ cubicCenterInH e X :=
      mul_mem
        ((le_sup_right : center (centralizer z) ≤ cubicCenterInH e X) hcZ)
        ((le_sup_left : cubicSylowImage e X ≤ cubicCenterInH e X) hx)
    simpa only [inv_mul_cancel_right] using hm
  · intro hc
    have hle : cubicCenterInH e X ≤
        e.projection.ker.comap (QuotientGroup.mk' (core z)) := by
      apply sup_le
      · intro x hx
        exact (cubicSylow_map_coreQuotient h e X).le (mem_map_of_mem _ hx)
      · intro x hx
        change QuotientGroup.mk' (core z) x ∈ e.projection.ker
        have hxq : QuotientGroup.mk' (core z) x = 1 :=
          (QuotientGroup.eq_one_iff x).mpr (centralizer_center_le_core h hx)
        rw [hxq]
        exact one_mem _
    exact hle hc

theorem cubicCentralizerProjection_ker_le_center :
    (cubicCentralizerProjection h e X).ker ≤ center (cubicCentralizerInH e X) := by
  rw [cubicCentralizerProjection_ker h e X]
  intro c hc
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  have hle : cubicCenterInH e X ≤
      Subgroup.centralizer (cubicCentralizerInH e X : Set (centralizer z)) :=
    sup_le (le_centralizer_iff.mp le_rfl) (center_le_centralizer _)
  exact (hle hc y y.property)

theorem cubicCenterInH_card : Nat.card (cubicCenterInH e X) = 6 := by
  rw [cubicCenterInH, card_sup_eq_mul_of_normalizes_of_disjoint]
  · rw [cubicSylowImage_card h e X, centralizer_center_card h]
  · exact (center_le_centralizer _).trans (centralizer_le_normalizer _)
  · apply disjoint_of_coprime_natCard
    rw [cubicSylowImage_card h e X, centralizer_center_card h]
    decide

variable (hp : Group.IsPerfect (cubicCentralizerInH e X))
include hp

/-- The six-cover specified by the original quotient, using section 4 perfectness. -/
noncomputable def cubicCentralizerCover :
    PerfectCentralCovering.Cover (cubicCentralizerInH e X) M22 where
  toMonoidHom := cubicCentralizerProjection h e X
  surjective := cubicCentralizerProjection_surjective h e X
  isPerfect := hp
  ker_le_center := cubicCentralizerProjection_ker_le_center h e X

theorem cubicCentralizer_center :
    center (cubicCentralizerInH e X) =
      (cubicCenterInH e X).subgroupOf (cubicCentralizerInH e X) := by
  have hc := (cubicCentralizerCover h e X hp).comap_center
  rw [m22_center_eq_bot] at hc
  exact hc.symm.trans (cubicCentralizerProjection_ker h e X)

theorem cubicCentralizer_center_card : Nat.card (center (cubicCentralizerInH e X)) = 6 := by
  rw [cubicCentralizer_center h e X hp]
  exact (Nat.card_congr (subgroupOfEquivOfLe (cubicCenterInH_le h e X)).toEquiv).trans
    (cubicCenterInH_card h e X)

/-- The central quotient is M₂₂ through the retained original projection. -/
noncomputable def cubicCentralizerCentralQuotientEquiv :
    (cubicCentralizerInH e X ⧸ center (cubicCentralizerInH e X)) ≃* M22 :=
  (QuotientGroup.quotientMulEquivOfEq
    ((cubicCentralizerProjection_ker h e X).trans (cubicCentralizer_center h e X hp).symm).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (cubicCentralizerProjection h e X)
        (cubicCentralizerProjection_surjective h e X))

theorem cubicCentralizer_quasisimple : IsQuasisimple (cubicCentralizerInH e X) := by
  let : Group.IsPerfect (cubicCentralizerInH e X) := hp
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  exact ⟨(cubicCentralizerCentralQuotientEquiv h e X hp).isSimpleGroup⟩

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison
