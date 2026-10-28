module

public import Theory.Representation.BinaryOffender.PerfectCentralizer
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Degree bounds for commuting actors

A nontrivial actor commuting with a subgroup produces a nonzero invariant
displacement space. A lower bound for the subgroup’s nonzero sections therefore
bounds both the actor’s fixed codimension and its moved dimension. A fixed-free
perfect subgroup also rules out an Irr⁺ moved space for any commuting actor.

These bounds support the B.5 module alternatives in the quiet Suzuki branch
of Aschbacher–Smith, 10.1.1 and 10.2.12.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace Representation.BinaryOffender
variable {Q W : Type*} [Group Q] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem not_irrPlus_moved_of_commuting_perfect
    (ρ : Representation (ZMod 2) Q W) (S K : Subgroup Q) [Group.IsPerfect S]
    (hfix : fixedSpace ρ S = ⊥) (hc : S ≤ centralizer (K : Set Q)) :
    ¬ IsIrrPlus ρ K (subspaceCommutator ρ ⊤ K) := by
  intro h
  have hs : S ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ K) :=
    subspaceCommutator_invariant_normalizer ρ (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      (hc.trans (Subgroup.centralizer_le_normalizer _))
  have hh := h.le_fixedSpace_of_perfect_centralizes ρ hc hs
  exact h.ne_bot ρ (bot_unique (hh.trans_eq hfix))


end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {Q W : Type*} [Group Q] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

theorem degree_le_fixedCodim_of_commuting
    (ρ : Representation (ZMod 2) Q W) (S A : Subgroup Q) {d : ℕ}
    (hdegree : ∀ U : Subrepresentation (ρ.comp S.subtype), U ≠ ⊥ →
      d ≤ Module.finrank (ZMod 2) U.toSubmodule)
    (hA : ¬ A ≤ ρ.ker) (hc : A ≤ centralizer (S : Set Q)) :
    d ≤ fixedCodim ρ A := by
  obtain ⟨a,ha,han⟩ := SetLike.not_le_iff_exists.mp hA
  have hcomm (s : S) : ρ s * ρ a = ρ a * ρ s := by
    rw [←map_mul,←map_mul]
    exact congrArg ρ (hc ha s s.property)
  let U : Subrepresentation (ρ.comp S.subtype) := {
    toSubmodule := LinearMap.range (ρ a - 1)
    apply_mem_toSubmodule s v hv := by
      obtain ⟨w,rfl⟩ := hv
      refine ⟨ρ s w,?_⟩
      change ρ a (ρ s w) - ρ s w = ρ s (ρ a w - w)
      rw [map_sub]
      exact congrArg (fun z => z - ρ s w) (LinearMap.congr_fun (hcomm s).symm w) }
  have hU : U ≠ ⊥ := by
    intro he
    apply han
    apply LinearMap.ext
    intro w
    have hz : ρ a w - w = 0 := by
      have hh : ρ a w - w ∈ U.toSubmodule := ⟨w,rfl⟩
      rw [he] at hh
      exact hh
    exact sub_eq_zero.mp hz
  have hd := hdegree U hU
  change d ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) at hd
  rw [←fixedCodim_zpowers_eq_displacement_rank] at hd
  have hfixle : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) :=
    fun v hv x => hv ⟨x,(zpowers_le.mpr ha) x.property⟩
  have hdimle := Submodule.finrank_mono hfixle
  have hfirst := fixedCodim_add_finrank ρ A
  have hsecond := fixedCodim_add_finrank ρ (zpowers a)
  omega

omit [FiniteDimensional (ZMod 2) W] in
theorem degree_le_moved_finrank_of_commuting
    (ρ : Representation (ZMod 2) Q W) (S K : Subgroup Q) {d : ℕ}
    (hdegree : ∀ U : Subrepresentation (ρ.comp S.subtype), U ≠ ⊥ →
      d ≤ Module.finrank (ZMod 2) U.toSubmodule)
    (hK : ¬ K ≤ ρ.ker) (hc : K ≤ centralizer (S : Set Q)) :
    d ≤ Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ K) := by
  have hs : S ≤ subspaceStabilizer ρ (subspaceCommutator ρ ⊤ K) :=
    subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by intros; trivial))
      ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
  let U : Subrepresentation (ρ.comp S.subtype) := {
    toSubmodule := subspaceCommutator ρ ⊤ K
    apply_mem_toSubmodule s v hv := (hs s.property v).2 hv }
  apply hdegree U
  intro he
  apply hK
  intro k hk
  apply LinearMap.ext
  intro v
  have hh := (subspaceCommutator_eq_bot_iff ρ ⊤ K).mp
    (congrArg (fun Z : Subrepresentation (ρ.comp S.subtype) => Z.toSubmodule) he)
  exact hh Submodule.mem_top ⟨k,hk⟩

end Representation.BinaryOffender
