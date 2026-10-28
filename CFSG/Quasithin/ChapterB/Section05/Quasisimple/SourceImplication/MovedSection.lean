module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Statement
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.MovedSpaceTransport

/-!
# The actual moved quotient in the B.5.1 setup

Perfectness gives [L Z(G), L Z(G)] = L. Since F*(G) is normal, the source
hypothesis F*(G) = L Z(G) therefore makes L normal, without adding a normality
assumption. Normality constructs both ambient actions in the literal section
[V,L] / C_[V,L](L). The nonsplitting equivalence is the two lattice conditions
for the corresponding direct sum.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.1,
printed pp.99 and 102. This proves the construction and equivalence only;
the nonsplitting list and the four action alternatives remain separate.
-/

@[expose] public section
open scoped commutatorElement
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

noncomputable def MovedSection.ofNormal (L : Subgroup G) [L.Normal] : MovedSection ρ L := by
  have hn : (⊤ : Subgroup G) ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (inferInstance : L.Normal)]
  have hm : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (moved ρ L) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hn
  let U : Subrepresentation ρ :=
    ⟨moved ρ L, fun g v hv => (hm (Subgroup.mem_top g) v).2 hv⟩
  have hc := fixedSpace_stable_of_normal U.toRepresentation L
  exact ⟨U, rfl,
    ⟨fixedSpace U.toRepresentation L, fun g v hv => (hc (Subgroup.mem_top g) v).2 hv⟩,
    rfl⟩

theorem nonsplitting_iff (L : Subgroup G) (s : MovedSection ρ L) :
    (¬ IsCompl s.space.toSubmodule (fixedSpace ρ L)) ↔
      s.space.toSubmodule ⊓ fixedSpace ρ L ≠ ⊥ ∨
      s.space.toSubmodule ⊔ fixedSpace ρ L ≠ ⊤ := by
  rw [isCompl_iff, disjoint_iff, codisjoint_iff]
  tauto

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem commutator_sup_center (L : Subgroup G) :
    ⁅L ⊔ center G, L ⊔ center G⁆ = ⁅L, L⁆ := by
  apply le_antisymm _ (commutator_mono le_sup_left le_sup_left)
  apply commutator_le.mpr
  intro x hx y hy
  obtain ⟨l, hl, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨m, hm, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
  have hzcomm : ⁅z, m * w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp hz) _).symm
  have hwcomm : ⁅l, w⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr ((mem_center_iff.mp hw) _)
  rw [commutatorElement_mul_left_eq_conj_mul, hzcomm, mul_one, mul_inv_cancel, one_mul]
  rw [commutatorElement_mul_right_eq_mul_conj, hwcomm, mul_one, mul_inv_cancel_right]
  exact commutator_mem_commutator hl hm

omit [AddCommGroup V] [Module (ZMod 2) V] in
theorem component_normal_of_fitting_eq_sup_center [Finite G] (L : Subgroup G)
    [IsQuasisimple L] (hf : generalizedFitting G = L ⊔ center G) : L.Normal := by
  have he : ⁅generalizedFitting G, generalizedFitting G⁆ = L := by
    rw [hf, commutator_sup_center, commutator_eq_self]
  rw [← he]
  infer_instance

/-- Construct the literal moved section from the original B.5.1 hypotheses. -/
noncomputable def QuasisimpleSourceHypothesis.movedSection [Finite G]
    {K : CFSG.Quasithin.GroupClass} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) : MovedSection ρ L := by
  letI : IsQuasisimple L := h.quasisimple
  letI : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  exact MovedSection.ofNormal ρ L

end CFSG.Quasithin.ChapterB.QuasisimpleSource
