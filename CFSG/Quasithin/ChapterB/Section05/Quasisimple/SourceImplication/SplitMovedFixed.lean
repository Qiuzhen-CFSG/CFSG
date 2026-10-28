module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection

/-!
# Fixed-space transport across an actual split moved section

Decompose a fixed vector into its moved and component-fixed summands. If the
acting subgroup fixes no nonzero vector of the central moved quotient, the
moved summand lies in its central part, so the original vector is component
fixed. This retains the literal section and its quotient action.

Source: the split case of Aschbacher–Smith B.5.1,C.2.7 and15.3.21,
printed pp.99–103,145–147,1127.
-/
public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {D W : Type*} [Group D] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) D W} {C B : Subgroup D}

theorem MovedSection.fixed_mem_fixed_of_split
    (s : MovedSection ρ C) (hc : IsCompl s.space.toSubmodule (fixedSpace ρ C))
    (hBC : B ≤ C)
    (hff : ∀ v : s.space.toSubmodule ⧸ s.central.toSubmodule,
      (∀ b : B, MovedSection.action ρ s (b : D) v = v) → v = 0)
    (w : W) (hw : ∀ b : B, ρ b w = w) : w ∈ fixedSpace ρ C := by
  have htop : w ∈ s.space.toSubmodule ⊔ fixedSpace ρ C := by rw [hc.sup_eq_top]; trivial
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp htop
  let u' : s.space.toSubmodule := ⟨u,hu⟩
  have hufix (b : B) : s.space.toRepresentation b u' = u' := by
    apply Subtype.ext
    have hzb : ρ b z = z := hz ⟨b,hBC b.property⟩
    have hh := hw b
    rw [map_add,hzb] at hh
    exact add_right_cancel hh
  have huq : (Submodule.mkQ s.central.toSubmodule) u' = 0 := by
    apply hff
    intro b
    exact congrArg (Submodule.mkQ s.central.toSubmodule) (hufix b)
  have huC : u' ∈ s.central.toSubmodule := by
    rw [←Submodule.ker_mkQ s.central.toSubmodule]
    exact huq
  rw [s.central_eq] at huC
  have huf : u ∈ fixedSpace ρ C := fun g => congrArg Subtype.val (huC g)
  exact (fixedSpace ρ C).add_mem huf hz
end CFSG.Quasithin.ChapterB.QuasisimpleSource
