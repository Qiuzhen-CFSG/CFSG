module
public import Theory.Representation.BinaryOffender.AlternatingSevenIrrPlus
public import Theory.Representation.QuadraticDuality

/-!
# Full commutator generation from the original dual fixed space

The annihilator of the actual commutator span is the dual fixed space.
If that fixed space vanishes, double annihilation gives full generation.
This transfers the proved C.5.13 full-moved group identity without
quotienting its central layer.
Source: Aschbacher–Smith C.5.13, p.163, and B.4.7.
-/
public section
open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
theorem subspaceCommutator_top_eq_top_of_dual_fixed
    (ρ : Representation (ZMod 2) G V) (hf : fixedSpace ρ.dual ⊤ = ⊥) :
    subspaceCommutator ρ ⊤ ⊤ = ⊤ := by
  have hfix : ρ.dual.invariants = ⊥ := by
    have he : ρ.dual.invariants = fixedSpace ρ.dual ⊤ := by
      ext f
      exact ⟨fun h g => h g.val, fun h g => h ⟨g,mem_top g⟩⟩
    exact he.trans hf
  have hc : Coinvariants.ker ρ = ⊤ := by
    apply Submodule.dualAnnihilator_eq_bot_iff.mp
    rw [dualAnnihilator_coinvariantsKer,hfix]
  have he : subspaceCommutator ρ ⊤ ⊤ = Coinvariants.ker ρ := by
    unfold subspaceCommutator Coinvariants.ker
    congr 1
    ext v
    constructor
    · rintro ⟨g,_,w,_,rfl⟩
      exact ⟨⟨g,w⟩,rfl⟩
    · rintro ⟨⟨g,w⟩,rfl⟩
      exact ⟨g,mem_top g,w,Submodule.mem_top,rfl⟩
  exact he.trans hc
end Representation.BinaryOffender
