module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Parabolic

/-!
# Noncommutation in the original orthogonal critical pair

The critical pair asserts noncentrality of a covering plane against the whole
conjugate module. To obtain noncommutation of the moved modules, assume the
opposite: the faithful marked actor kernel puts the plane into the conjugate
two-core. F.9 then puts its commutator with the whole conjugate module in the
conjugate central line. Exclusion of that line from the plane makes this
commutator trivial, contradicting critical-pair noncentrality.

The second lemma places the same commutator in the conjugate moved module.
These statements retain one conjugator throughout; no crossing record is assumed.

Source: Aschbacher--Smith, 14.6.13(1), 14.6.17(2--4), printed pp.1031--1036.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open Chapter15.Section03
variable {G : Type*} [Group G]
namespace SourceOrthogonalFourAction
variable {H U Z Q : Subgroup G} (d : SourceOrthogonalFourAction H U Z Q)
attribute [local instance] orthogonalAction

include d in
theorem centralizer_moved_le_core : H ⊓ centralizer ((⁅U,H⁆ : Subgroup G) : Set G) ≤ Q := by
  let := FourGroupMatrixCoordinates.naturalAction
  let := FourGroupMatrixCoordinates.naturalAction_faithful
  let : FaithfulSMul OrthogonalActor OrthogonalVector :=
    RegularWreathProduct.functionModule_faithful _ _ _
  intro x hx
  have hxk : (⟨x,hx.1⟩ : H) ∈ d.actor.ker := by
    change d.actor ⟨x,hx.1⟩ = 1
    apply FaithfulSMul.eq_of_smul_eq_smul (α := OrthogonalVector)
    intro v
    obtain ⟨a,rfl⟩ := d.surjective v
    rw [one_smul,←d.compatible]
    congr 1
    apply Subtype.ext
    change x * (a : G) * x⁻¹ = a
    exact mul_inv_eq_iff_eq_mul.mpr (hx.2 a a.property).symm
  rw [d.actor_kernel] at hxk
  exact hxk

end SourceOrthogonalFourAction

namespace OddCriticalPair
variable [Finite G] {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

include h in
theorem critical_pair_crosses
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (Mc : Subgroup G) (c : SourceOrthogonalCriticalPair d Mc)
    (hpoint : ¬ D.V₁.map (MulAut.conj c.g).toMonoidHom ≤ d.plane c.first) :
    ¬ ⁅D.UH,D.H⁆ ≤ centralizer
      ((⁅D.UH,D.H⁆).map (MulAut.conj c.g).toMonoidHom : Set G) := by
  let A := ⁅D.UH,D.H⁆
  let W := d.plane c.first
  have hWU : W ≤ D.UH := (d.plane_le c.first).trans
    (le_normalizer_iff_commutator_le_left.mp d.normalized)
  intro hc
  have hback : W.map (MulAut.conj c.g⁻¹).toMonoidHom ≤ D.QH := by
    rintro x ⟨w,hw,rfl⟩
    apply d.centralizer_moved_le_core
    constructor
    · obtain ⟨a,ha,he⟩ := c.reverse (hWU hw)
      rw [←he]
      simpa [MulAut.conj_apply,mul_assoc] using ha
    · intro a ha
      have he := hc (d.plane_le c.first hw)
        ((MulAut.conj c.g) a) (mem_map_of_mem _ ha)
      have he' := congrArg (MulAut.conj c.g⁻¹) he
      simpa [MulAut.conj_apply,mul_assoc] using he'
  have hcomm : ⁅W,D.UH.map (MulAut.conj c.g).toMonoidHom⁆ ≤
      D.V₁.map (MulAut.conj c.g).toMonoidHom := by
    apply commutator_le.mpr
    rintro w hw _ ⟨v,hv,rfl⟩
    have hh : ⁅(MulAut.conj c.g⁻¹) w,v⁆ ∈ D.V₁ := by
      have hz := h.commutator_UH_QH_le_point
      rw [commutator_comm] at hz
      exact hz (commutator_mem_commutator (hback (mem_map_of_mem _ hw)) hv)
    have hm := mem_map_of_mem (MulAut.conj c.g).toMonoidHom hh
    simpa only [MulEquiv.coe_toMonoidHom,map_commutatorElement,
      MulAut.conj_apply,inv_inv,mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hm
  have hWcomm : ⁅W,D.UH.map (MulAut.conj c.g).toMonoidHom⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp (c.normalizes.trans inf_le_right)
  have hdis : W ⊓ D.V₁.map (MulAut.conj c.g).toMonoidHom = ⊥ := by
    have hd : Nat.card (W ⊓ D.V₁.map (MulAut.conj c.g).toMonoidHom : Subgroup G) ∣ 2 := by
      have hc : Nat.card (D.V₁.map (MulAut.conj c.g).toMonoidHom) = 2 := by
        rw [card_map_of_injective (MulAut.conj c.g).injective,h.point_card]
      rw [←hc]
      exact card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact card_eq_one.mp h1
    · exfalso
      apply hpoint
      have he : W ⊓ D.V₁.map (MulAut.conj c.g).toMonoidHom =
          D.V₁.map (MulAut.conj c.g).toMonoidHom := by
        apply eq_of_le_of_card_ge inf_le_right
        rw [card_map_of_injective (MulAut.conj c.g).injective,h.point_card,h2]
      exact he ▸ inf_le_left
  apply c.noncentral
  exact (le_inf hWcomm hcomm).trans (hdis.le.trans bot_le)

omit [Finite G] in
theorem critical_commutator_le_moved_conjugate
    (d : SourceOrthogonalFourAction D.H D.UH D.V₁ D.QH)
    (Mc : Subgroup G) (c : SourceOrthogonalCriticalPair d Mc) :
    ⁅d.plane c.first,D.UH.map (MulAut.conj c.g).toMonoidHom⁆ ≤
      (⁅D.UH,D.H⁆).map (MulAut.conj c.g).toMonoidHom := by
  rw [map_commutator,commutator_comm]
  apply commutator_mono le_rfl
  exact ((d.plane_le c.first).trans
    (le_normalizer_iff_commutator_le_left.mp d.normalized)).trans c.reverse

end OddCriticalPair
end CFSG.Quasithin.Chapter14.Section06
