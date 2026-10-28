module
public import Theory.SpecificGroups.Alternating.FiveChiefDegree
public import Theory.GroupTheory.Commutator.SimpleSubnormal
public import Theory.GroupAction.SubgroupQuotientFullAction
/-!
# A₅ movement on a factor modulo its fixed subgroup

A perfect two-perfect A₅ extension acting nontrivially on a finite abelian
two-group also acts nontrivially modulo its full fixed subgroup. Otherwise
its second commutator vanishes and perfectness makes its first commutator
vanish. The order-five action bound consequently forces index at least
sixteen in the fixed subgroup.

Source application: Aschbacher–Smith, 10.2.12, printed p.754; the actual
moved-factor consumer is Chapter10.SourceA5WeakClosureLowerBound.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative
namespace alternatingGroup.FiveChiefDegree
variable {G : Type*} [Group G] [Finite G]
theorem centralizer_relIndex_ge_sixteen
    (L W : Subgroup G) [Group.IsPerfect L] [IsMulCommutative W]
    (hp : IsPPerfect 2 L) (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hW : IsPGroup 2 W) (hLW : L ≤ normalizer (W : Set G))
    (hm : ⁅W,L⁆ ≠ ⊥) : 16 ≤ (centralizer (L : Set G)).relIndex W := by
  let C := centralizer (L : Set G)
  let : (C.subgroupOf W).Normal := inferInstance
  obtain ⟨ρ,hρ⟩ := exists_quotient_conjugation_action L W C hLW
    ((le_centralizer_iff.mpr (le_rfl : C ≤ centralizer (L : Set G))).trans
      (centralizer_le_normalizer (C : Set G))) inferInstance
  have hn : ρ ≠ 1 := by
    intro he
    have hc : ⁅W,L⁆ ≤ C := by
      rw [commutator_comm]
      apply commutator_le.mpr
      intro l hl w hw
      have hh := hρ ⟨l,hl⟩ ⟨w,hw⟩
      rw [he] at hh
      have hi := QuotientGroup.eq_iff_div_mem.mp hh.symm
      change l * w * l⁻¹ / w ∈ C at hi
      simpa only [commutatorElement_def, div_eq_mul_inv] using hi
    apply hm
    apply commutator_eq_bot_of_iterated_eq_bot
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hb := sixteen_le_card_of_nontrivial_action hp e ρ hn
    (hW.of_surjective (QuotientGroup.mk' (C.subgroupOf W)) (QuotientGroup.mk'_surjective _))
  simpa only [Subgroup.relIndex, Subgroup.index] using hb
end alternatingGroup.FiveChiefDegree
