module
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Basic
public import Theory.GroupTheory.NormalizingInvolutionCard

/-!
# The two-component action and the enlarged Sylow subgroup

An element of H normalizing a subgroup X of L that is not central in L
cannot interchange L and its commuting conjugate: it would place X in
their central intersection. Together with 16.2.8(3), this gives control by
the individual component for noncentral two-subgroups. The same permutation
action shows that an element fixing one component fixes the other.

When Z(L) is trivial, the central involution z lies outside L. Adjoining it
to T_L therefore gives the actual two-subgroup R = T_L⟨z⟩ of order 2|T_L|.
These results supply the normalizer and counting steps in 16.2.11–16.2.12;
they do not assert the missing placement or the two-component containment.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, p.1176.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination
open ChapterI.Section06To08
variable {G : Type*} [Group G] {T : Sylow 2 G} {z u : G} {L : Subgroup G}
namespace EarlierConclusions
variable (h : EarlierConclusions T z u L)
include h

/-- The two factors are distinct in the genuine counterexample. -/
theorem swapped_ne : conjSubgroup L u ≠ L := by
  intro he
  exact h.u_not_normalizer (mem_normalizer_iff_map_conj_eq.mpr he)

/-- An element of H preserving L also preserves the second component. -/
theorem normalizes_swapped :
    localComponentNormalizer z L ⊓ normalizer (L : Set G) ≤
      normalizer (conjSubgroup L u : Set G) := by
  intro g hg
  have huH := h.sylow_le h.u_mem
  rcases h.permutes (g * u) ((localComponentNormalizer z L).mul_mem hg.1 huH) with he | he
  · have he' : conjSubgroup (conjSubgroup L u) g = L := by
      rwa [conjSubgroup_conjSubgroup]
    have heL : conjSubgroup L g⁻¹ = L :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (L : Set G)).inv_mem hg.2)
    have hf := congrArg (fun X => conjSubgroup X g⁻¹) he'
    rw [conjSubgroup_inv, heL] at hf
    exact (h.swapped_ne hf).elim
  · apply mem_normalizer_iff_map_conj_eq.mpr
    change conjSubgroup (conjSubgroup L u) g = _
    rwa [conjSubgroup_conjSubgroup]

/-- A subgroup of L not contained in its center prevents H from swapping
the components when normalizing that subgroup. -/
theorem fixes_component_of_normalizes_noncentral {X : Subgroup G}
    (hXL : X ≤ L) (hXC : ¬ X ≤ componentCenter L) :
    localComponentNormalizer z L ⊓ normalizer (X : Set G) ≤
      normalizer (L : Set G) := by
  intro g hg
  rcases h.permutes g hg.1 with he | he
  · exact mem_normalizer_iff_map_conj_eq.mpr he
  · have hXg : conjSubgroup X g = X := mem_normalizer_iff_map_conj_eq.mp hg.2
    have hXLu : X ≤ conjSubgroup L u := by
      simpa only [hXg, he] using conjSubgroup_mono hXL g
    exact (hXC ((le_inf hXL hXLu).trans h.intersection_le_center)).elim

/-- Normalizer control becomes control by the individual component whenever
the two-subgroup is not central in that component. -/
theorem normalizer_noncentral_two_subgroup {X : Subgroup G}
    (hp : IsPGroup 2 X) (hXL : X ≤ L) (hXC : ¬ X ≤ componentCenter L) :
    normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  have hne : X ≠ ⊥ := fun he => hXC (he ▸ bot_le)
  exact (le_inf (h.normalizer_control X hp hne (hXL.trans le_sup_right)) le_rfl).trans
    (h.fixes_component_of_normalizes_noncentral hXL hXC)

/-- When the center is trivial, the central involution is external to L. -/
theorem central_involution_not_mem_component (hc : center L = ⊥) : z ∉ L := by
  intro hz
  have hzC : (⟨z, hz⟩ : L) ∈ center L := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (h.localSetup.component.1 x.property)
  rw [hc] at hzC
  have hz1 : z = 1 := congrArg L.subtype (mem_bot.mp hzC)
  have ho := h.localSetup.involution
  rw [hz1, orderOf_one] at ho
  omega

/-- The actual group R = T_L⟨z⟩ in 16.2.12 is a two-subgroup of T and has
exactly twice the order of T_L. This retains the strict counting input. -/
theorem enlarged_sylow_card (hc : center L = ⊥) :
    componentSylow T L ⊔ zpowers z ≤ (T : Subgroup G) ∧
      IsPGroup 2 ↥(componentSylow T L ⊔ zpowers z) ∧
      Nat.card ↥(componentSylow T L ⊔ zpowers z) = 2 * Nat.card (componentSylow T L) := by
  have hRT : componentSylow T L ⊔ zpowers z ≤ (T : Subgroup G) :=
    sup_le inf_le_left (zpowers_le.mpr h.localSetup.mem_sylow)
  refine ⟨hRT, T.isPGroup'.to_le hRT, ?_⟩
  apply card_sup_zpowers_of_normalizing_involution
  · simpa only [h.localSetup.involution] using pow_orderOf_eq_one z
  · exact fun hz => h.central_involution_not_mem_component hc hz.2
  · apply centralizer_le_normalizer
    intro x hx
    exact mem_centralizer_singleton_iff.mp (h.localSetup.sylow_centralizes hx.1)

end EarlierConclusions
end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
