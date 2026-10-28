module

public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems

/-!
# Central quotients of embedded subgroups

A centerless subgroup embeds through the ambient central projection. A
subgroup centralizing a noncentral element has proper image through that
same projection: the ambient center also centralizes the element, so a
surjective image would force the whole group to centralize it.

This is the central-version bookkeeping needed for the matrix subsystem
inclusions of GLS3 §2.6 and Aschbacher--Smith A.2.17 (printed p.39).
-/

@[expose] public section

namespace TwistedE6.FoldedSubsystem.HigherRealizations

variable {H G : Type*} [Group H] [Group G]

theorem centralProjection_injective (f : H →* G) (hf : Function.Injective f)
    (hc : Subgroup.center H = ⊥) :
    Function.Injective ((QuotientGroup.mk' (Subgroup.center G)).comp f) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hfx : f x ∈ Subgroup.center G := (QuotientGroup.eq_one_iff (f x)).mp hx
  have hxcenter : x ∈ Subgroup.center H := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply hf
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp hfx (f y)
  simpa only [hc, Subgroup.mem_bot] using hxcenter

/-- Properness in the quotient needs only a noncentral witness in the cover. -/
theorem centralProjection_range_ne_top (f : H →* G) (x : G)
    (hx : x ∉ Subgroup.center G) (hcomm : ∀ h, Commute x (f h)) :
    ((QuotientGroup.mk' (Subgroup.center G)).comp f).range ≠ ⊤ := by
  intro htop
  apply hx
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨h, hh⟩ := MonoidHom.range_eq_top.mp htop
    (QuotientGroup.mk' (Subgroup.center G) g)
  have hz : f h / g ∈ Subgroup.center G := QuotientGroup.eq_iff_div_mem.mp hh
  have hzcomm : Commute x (f h / g) := Subgroup.mem_center_iff.mp hz x
  have hg : g = (f h / g)⁻¹ * f h := by simp [div_eq_mul_inv, mul_assoc]
  rw [hg]
  exact ((hzcomm.inv_right).mul_right (hcomm h)).eq.symm

/-- Combine faithfulness and the noncentral centralizer obstruction. -/
def properEmbeddingOfCentralizer (f : H →* G) (hf : Function.Injective f)
    (hc : Subgroup.center H = ⊥) (x : G) (hx : x ∉ Subgroup.center G)
    (hcomm : ∀ h, Commute x (f h)) :
    ExceptionalSplit.ProperEmbedding H (G ⧸ Subgroup.center G) where
  hom := (QuotientGroup.mk' (Subgroup.center G)).comp f
  injective := centralProjection_injective f hf hc
  proper := centralProjection_range_ne_top f x hx hcomm

end TwistedE6.FoldedSubsystem.HigherRealizations
