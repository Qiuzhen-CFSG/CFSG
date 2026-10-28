module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Irreducible.RootOrbit
public import Theory.Representation.BinaryTransvectionGroups.RootForms.Generation

/-!
# Global irreducibility and root-form envelopes

A root-form envelope has an annihilator invariant under every generating root
group.  Global irreducibility forces that annihilator to be zero, so the
envelope is the whole dual and each center has its full root group.  This is
a conditional reduction: constructing the envelope remains an obligation.

This avoids the false inference in the printed enlargement argument that a
particular boundary root must move the fixed space of the local subgroup.
Source: Aschbacher--Smith, G.3.1, printed pp.337--338.
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (GL V)} {Δ : Set V}

/-- Irreducibility is used for the global group, through an invariant
annihilator; it is not passed to a local restriction. -/
theorem RootGeneratedOrbit.envelope_eq_top [Finite G]
    (r : RootGeneratedOrbit G Δ) (hirr : Irreducible G)
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)}
    (he : IsRootFormEnvelope G Δ E) : E = ⊤ := by
  let : FiniteDimensional (ZMod 2) V := r.finiteDimensional
  have hpar : G ≤ parabolic E.dualCoannihilator := by
    rw [← r.generated_eq]
    exact generated_le_parabolic_envelope he r.nonzero
  rcases hirr E.dualCoannihilator hpar with hb | ht
  · rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := E), hb,
      Submodule.dualAnnihilator_bot]
  · exfalso
    apply he.1
    apply bot_unique
    intro f hf
    change f = 0
    ext v
    exact (Submodule.mem_dualCoannihilator v).mp (ht ▸ Submodule.mem_top) f hf

/-- Once the envelope is constructed, every root form vanishing at a center
occurs in the actual ambient group. -/
theorem RootGeneratedOrbit.full_rootForms_of_envelope [Finite G]
    (r : RootGeneratedOrbit G Δ) (hirr : Irreducible G)
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)}
    (he : IsRootFormEnvelope G Δ E) {x : V} (hx : x ∈ Δ) :
    rootForms G x = (centerLine x).dualAnnihilator := by
  have hEt := r.envelope_eq_top hirr he
  rcases he.2 x hx with hxc | hforms
  · rw [hEt, Submodule.dualCoannihilator_top, Submodule.mem_bot] at hxc
    exact (r.nonzero x hx hxc).elim
  · simpa only [hEt, top_inf_eq] using hforms

/-- The global recognition conclusion follows from a root-form envelope.
The construction of the envelope is a separate mathematical obligation. -/
theorem RootGeneratedOrbit.eq_top_of_envelope [Finite G]
    (r : RootGeneratedOrbit G Δ) (hirr : Irreducible G)
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)}
    (he : IsRootFormEnvelope G Δ E) : G = ⊤ := by
  let : FiniteDimensional (ZMod 2) V := r.finiteDimensional
  exact eq_top_of_rootForms_on_spanning G Δ r.span_eq_top
    (fun _ hx => r.full_rootForms_of_envelope hirr he hx)

end CFSG.Quasithin.ChapterG.Section03.Reduced
