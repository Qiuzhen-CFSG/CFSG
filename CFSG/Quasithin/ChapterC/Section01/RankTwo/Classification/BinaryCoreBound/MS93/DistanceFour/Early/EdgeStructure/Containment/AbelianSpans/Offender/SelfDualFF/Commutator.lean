module

public import Theory.Representation.BinaryOffender.IrreducibleExistence
public import Theory.Representation.QuadraticDuality
import Mathlib.Tactic.LinearCombination

/-!
# The commutator module for a perfect actor

The span of the action differences is an actual invariant subspace. For a
perfect group its restricted action is commutator-generated. To prove this,
extend a functional annihilating the second commutator to the original module.
Its values on the differences at any vector define a homomorphism from the
perfect actor to the additive field, and hence vanish. Dual separation finishes
the argument, without a splitting or semisimplicity assumption.

This is the full-commutator reduction used for the binary model obstruction in
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(4.6.4), printed p.902.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
namespace SelfDualFF

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The two span conventions for the full action commutator agree. -/
lemma fullCommutator_eq (ρ : Representation (ZMod 2) G V) :
    subspaceCommutator ρ ⊤ ⊤ = Coinvariants.ker ρ := by
  unfold subspaceCommutator Coinvariants.ker
  congr 1
  ext v
  simp only [Set.mem_ofPred_eq, Subgroup.mem_top, Submodule.mem_top, true_and,
    Set.mem_range, Prod.exists]
  constructor <;> rintro ⟨g, w, h⟩ <;> exact ⟨g, w, h.symm⟩

/-- The action on the literal span of all action differences. -/
noncomputable def commutatorSubrepresentation (ρ : Representation (ZMod 2) G V) :
    Subrepresentation ρ where
  toSubmodule := Coinvariants.ker ρ
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨⟨h, w⟩, rfl⟩ := hv
      have hm := Coinvariants.sub_mem_ker (ρ := ρ) (g * h * g⁻¹) (ρ g w)
      have he : ρ (g * h * g⁻¹) (ρ g w) = ρ g (ρ h w) := by
        change (ρ (g * h * g⁻¹) * ρ g) w = (ρ g * ρ h) w
        rw [← map_mul, ← map_mul]
        simp
      simpa only [he, map_sub] using hm
    | zero => simp
    | add x y hx hy ihx ihy => simpa only [map_add] using (Coinvariants.ker ρ).add_mem ihx ihy
    | smul a x hx ih => simpa only [map_smul] using (Coinvariants.ker ρ).smul_mem a ih

/-- Perfectness makes the commutator module commutator-generated. -/
lemma commutator_full (ρ : Representation (ZMod 2) G V) [Group.IsPerfect G] :
    subspaceCommutator (commutatorSubrepresentation ρ).toRepresentation ⊤ ⊤ = ⊤ := by
  rw [fullCommutator_eq]
  apply Subspace.dualAnnihilator_inj.mp
  rw [Submodule.dualAnnihilator_top]
  apply le_bot_iff.mp
  intro f hf
  rw [Submodule.mem_dualAnnihilator] at hf
  let C := commutatorSubrepresentation ρ
  let F := Subspace.dualLift C.toSubmodule f
  have hinv (g : G) (w : V) (hw : w ∈ C.toSubmodule) : F (ρ g w) = F w := by
    have h := hf _ (Coinvariants.sub_mem_ker (ρ := C.toRepresentation) g ⟨w, hw⟩)
    rw [map_sub] at h
    change f ⟨ρ g w, C.apply_mem_toSubmodule g hw⟩ - f ⟨w, hw⟩ = 0 at h
    change F (ρ g w) = F w
    simpa only [F, Subspace.dualLift_of_mem hw,
      Subspace.dualLift_of_mem (C.apply_mem_toSubmodule g hw)] using sub_eq_zero.mp h
  have hdiff (g : G) (v : V) : F (ρ g v - v) = 0 := by
    let d : G →* Multiplicative (ZMod 2) := {
      toFun a := Multiplicative.ofAdd (F (ρ a v - v))
      map_one' := by simp
      map_mul' a b := by
        change F (ρ (a * b) v - v) = F (ρ a v - v) + F (ρ b v - v)
        have h := hinv a (ρ b v - v) (Coinvariants.sub_mem_ker b v)
        simp only [map_sub] at h
        simp only [map_mul, Module.End.mul_apply, map_sub]
        linear_combination h
    }
    let : Group.IsPerfect d.range := Group.IsPerfect.range d
    have h : d g = 1 := congrArg Subtype.val
      (Subsingleton.elim (⟨d g, g, rfl⟩ : d.range) 1)
    exact h
  have hC : C.toSubmodule ≤ F.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact hdiff g v
  change f = 0
  ext v
  have h : F (v : V) = 0 := hC v.property
  simpa only [F, Subspace.dualLift_of_subtype, LinearMap.zero_apply] using h

end SelfDualFF
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
