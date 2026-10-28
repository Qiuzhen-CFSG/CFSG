module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.Frattini
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Basic

/-!
# Commutation of the source two-core and component actions

O₂(XT) fixes X/O₂(X), since its commutator with the normal subgroup X is
a normal two-subgroup of X. Its commutators with L therefore lie in the
kernel of the odd Frattini action. The C-component kernel theorem puts
this kernel in O∞(L), which centralizes the actual moved module U.
Thus the two original actions on U commute, without assuming the desired
point-centralizer identity.

Source: Aschbacher--Smith, proof of 13.1.12, printed p.873.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
open Chapter1 Chapter1.Section02 Chapter12.Section02 Chapter1.RadicalNormalizers
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem radicalCore_frattini_action_eq_one (p : ℕ) {L T : Subgroup G}
    (hT : T ≤ normalizer (L : Set G))
    (r : normalizer (L : Set G)) (hr : (r : G) ∈ radicalCore p L T) :
    xiFrattiniAction (normalizer (L : Set G)) (XiP p L) (XiP_invariant p le_rfl) r = 1 := by
  let X := XiP p L
  let a : MulAut X := X.normalizerMonoidHom
    ⟨(r : G), XiP_invariant p le_rfl r.property⟩
  have hq : quotientAut (pCore 2 X) a = 1 := by
    apply MulEquiv.ext
    intro v
    induction v using QuotientGroup.induction_on with | H x =>
      change quotientAut (pCore 2 X) a (QuotientGroup.mk' (pCore 2 X) x) =
        QuotientGroup.mk' (pCore 2 X) x
      rw [quotientAut_apply_mk]
      have hc : a x * x⁻¹ ∈ pCore 2 X := by
        have hh : ⁅(r : G),(x : G)⁆ ∈ X.pCoreIn 2 := by
          apply commutator_radicalCore_le p hT
          rw [commutator_comm]
          exact commutator_mem_commutator hr x.property
        obtain ⟨c,hc,he⟩ := hh
        exact (show c = a x * x⁻¹ from Subtype.ext he) ▸ hc
      have he := (QuotientGroup.eq_one_iff (a x * x⁻¹)).mpr hc
      change QuotientGroup.mk' (pCore 2 X) (a x * x⁻¹) = 1 at he
      rw [map_mul,map_inv] at he
      exact mul_inv_eq_one.mp he
  change quotientAut (frattini (XiQuotient X)) (quotientAut (pCore 2 X) a) = 1
  rw [hq,map_one]

/-- The original two-core action commutes with the original component action.
The two-core fixes X/O₂(X); hence its commutators with L lie in the
Frattini-action kernel, which the C-component argument puts in O∞(L). -/
theorem radicalCore_commutes_component_action
    {T : Sylow 2 G} (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {L : Subgroup G} (hL : FaithfulMaximalLocal T L)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L)))
    (r : normalizer (L : Set G)) (hr : (r : G) ∈ radicalCore p L T)
    (l : L) :
    action L r * componentAction L l = componentAction L l * action L r := by
  have hT := radicalLocal_invariant_source hL.1.1
    (uniqueness_local_quotient_sqtk h.simpleQTKE hL.1.1.2.2) hn
  let σ := xiFrattiniAction (normalizer (L : Set G)) (XiP p L) (XiP_invariant p le_rfl)
  let c : L := ⟨⁅(r : G),(l : G)⁆, L.mul_mem
    ((mem_normalizer_iff.mp r.property l).mp l.property) (L.inv_mem l.property)⟩
  have hcM : inclusion L.le_normalizer c = ⁅r,inclusion L.le_normalizer l⁆ := rfl
  have hc : c ∈ (xiFrattiniAction L (XiP p L) (XiP_invariant p L.le_normalizer)).ker := by
    rw [MonoidHom.mem_ker, xiFrattiniAction_restrict L.le_normalizer
      (XiP_invariant p le_rfl) c]
    change σ (inclusion L.le_normalizer c) = 1
    rw [hcM,map_commutatorElement]
    have hrσ : σ r = 1 := radicalCore_frattini_action_eq_one p hT r hr
    rw [hrσ]
    simp
  have hcU : c ∈ (componentAction L).ker := by
    rw [componentAction_ker_eq_radical h hmany hL hn]
    exact component_frattini_kernel_le_radical h.simpleQTKE hL.1.1 hn ho hd hc
  have he := MonoidHom.mem_ker.mp hcU
  change action L (inclusion L.le_normalizer c) = 1 at he
  rw [hcM,map_commutatorElement] at he
  exact commutatorElement_eq_one_iff_mul_comm.mp he

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.ModuleOrbits.LinearThree
