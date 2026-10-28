module
public import Theory.GroupTheory.AbelianSylowSections
public import Theory.GroupTheory.PerfectCentralCoverAbelianSylow
public import Theory.Mathieu.M22.TripleCover

/-!
# The triple Mathieu cover cannot be an abelian-Sylow section

Central transfer forbids a nontrivial central three-subgroup in a finite
perfect group with abelian Sylow three-subgroups. The genuine triple
Mathieu cover has center of order three, so it cannot be a quotient of a
subgroup of any group with abelian Sylow three-subgroups.

Source: Aschbacher--Smith, final proof of 15.2.15, printed p.1118.
-/

public section
open Subgroup Theory.GroupTheory
namespace Sporadic.Mathieu.M22TripleCover

/-- Central transfer excludes abelian Sylow three-subgroups in the genuine triple cover. -/
theorem not_hasAbelianSylow_three : ¬ HasAbelianSylow 3 M22TripleCover := by
  intro h
  let q := QuotientGroup.mk' (center M22TripleCover)
  let P : Sylow 3 M22TripleCover := Classical.choice inferInstance
  have hn := PerfectCentralCovering.not_dvd_card_kernel_of_abelian_sylow q
    (by rw [QuotientGroup.ker_mk']) P (h P)
  rw [QuotientGroup.ker_mk',center_card] at hn
  exact hn dvd_rfl

/-- No subgroup of a group with abelian Sylow three-subgroups has a triple-Mathieu quotient. -/
theorem not_section_of_hasAbelianSylow_three
    {G : Type*} [Group G] [Finite G] (h : HasAbelianSylow 3 G)
    (R : Subgroup G) (N : Subgroup R) [N.Normal]
    (e : (R ⧸ N) ≃* M22TripleCover) : False := by
  have hr : HasAbelianSylow 3 R := h.of_injective R.subtype R.subtype_injective
  exact not_hasAbelianSylow_three ((hr.of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)).of_surjective e.toMonoidHom e.surjective)
end Sporadic.Mathieu.M22TripleCover
