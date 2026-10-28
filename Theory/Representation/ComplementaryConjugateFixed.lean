module
public import Theory.Representation.BinaryOffender.Defs
public import Theory.Representation.GeneratedSubgroupInvariants

/-!
# Exact fixed spaces from complementary conjugate subspaces

Let two subgroups generate an actor group. If complementary subspaces are
fixed by the respective subgroups and one subspace is a conjugate of the
other, they are the full fixed spaces and the global fixed space is zero.
Split a globally fixed vector into the two summands; one summand is then
fixed by both generators. Conjugacy puts that summand in their intersection.
The same splitting identifies each full fixed space.

This argument requires no Sylow, quadratic, irreducibility or finiteness
hypothesis. Its source application is the actual two-seed quotient in
DGS85, Groups and Graphs (1985), (11.3)(b), printed pp.168--171.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- Complementary conjugate fixed subspaces exhaust the two fixed spaces. -/
theorem complementary_conjugate_fixed_spaces
    (ρ : Representation (ZMod 2) G W) (A B : Subgroup G)
    (U V : Submodule (ZMod 2) W) (g : G)
    (hgen : A ⊔ B = ⊤) (hc : IsCompl U V)
    (hU : U ≤ fixedSpace ρ A) (hV : V ≤ fixedSpace ρ B)
    (hconj : V = U.map (ρ g)) :
    fixedSpace ρ ⊤ = ⊥ ∧ fixedSpace ρ A = U ∧ fixedSpace ρ B = V := by
  have hi : fixedSpace ρ A ⊓ fixedSpace ρ B = fixedSpace ρ ⊤ := by
    exact (ρ.invariants_comp_sup A B).symm.trans (congrArg (fixedSpace ρ) hgen)
  have hz (v : W) (hv : v ∈ fixedSpace ρ ⊤) (hvV : v ∈ V) : v = 0 := by
    obtain ⟨u,hu,he⟩ := hconj ▸ hvV
    have hfix := hv ⟨g,mem_top _⟩
    have hvu : v = u := (ρ.apply_bijective g).injective (hfix.trans he.symm)
    exact hc.disjoint.le_bot ⟨hvu ▸ hu,hvV⟩
  have hf : fixedSpace ρ ⊤ = ⊥ := by
    apply bot_unique
    intro v hv
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ U ⊔ V from hc.sup_eq_top.symm ▸ Submodule.mem_top)
    have hwA : w ∈ fixedSpace ρ A := by
      have hh := (fixedSpace ρ A).sub_mem
        (ρ.invariants_comp_subtype_antitone le_top hv) (hU hu)
      simpa only [add_sub_cancel_left] using hh
    have hw0 := hz w (hi ▸ ⟨hwA,hV hw⟩) hw
    have huF : u ∈ fixedSpace ρ ⊤ := by simpa only [hw0,add_zero] using hv
    have huV : u ∈ V := hconj ▸ ⟨u,hu,huF ⟨g,mem_top _⟩⟩
    have hu0 := hz u huF huV
    simp only [hu0,hw0,add_zero,Submodule.mem_bot]
  refine ⟨hf,le_antisymm ?_ hU,le_antisymm ?_ hV⟩
  · intro v hv
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ U ⊔ V from hc.sup_eq_top.symm ▸ Submodule.mem_top)
    have hwA : w ∈ fixedSpace ρ A := by
      simpa only [add_sub_cancel_left] using (fixedSpace ρ A).sub_mem hv (hU hu)
    have hw0 : w = 0 := by
      have hh : w ∈ fixedSpace ρ ⊤ := hi ▸ ⟨hwA,hV hw⟩
      simpa only [hf,Submodule.mem_bot] using hh
    simpa only [hw0,add_zero] using hu
  · intro v hv
    obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ U ⊔ V from hc.sup_eq_top.symm ▸ Submodule.mem_top)
    have huB : u ∈ fixedSpace ρ B := by
      simpa only [add_sub_cancel_right] using (fixedSpace ρ B).sub_mem hv (hV hw)
    have hu0 : u = 0 := by
      have hh : u ∈ fixedSpace ρ ⊤ := hi ▸ ⟨hU hu,huB⟩
      simpa only [hf,Submodule.mem_bot] using hh
    simpa only [hu0,zero_add] using hw
end Representation
