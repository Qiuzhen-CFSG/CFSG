module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels

/-!
# Unconditional axis actions of the Parker triality group

The concrete normal-form theorem discharges all three premises of the
permutation-kernel calculations. These are the permutation ingredients of
Aschbacher, *Sporadic Groups*, 14.4, 14.6 and 27.3(5–6), pp. 61–63 and 146.
The two axis-2 orbit relations are kept distinct.
-/

public section
open Atlas.Fischer
namespace Sporadic.Monster.Construction.TrialitySpin

theorem trialityOrbitPresentation : OrbitPresentation where
  normalForm_bijective := normalForm_bijective
  normalForm_mem_Q1 := normalForm_mem_Q1_iff
  normalForm_mem_NPlus := normalForm_mem_NPlus_iff

theorem N1_mapsTo_A (g : N) (hg : g ∈ N1) : Set.MapsTo g.val A A :=
  N1_preserves_A trialityOrbitPresentation g hg

theorem N1_commute_k1 (g : N) (hg : g ∈ N1) : Commute g k1 :=
  N1_commutes_k1 trialityOrbitPresentation g hg

theorem N1_orbit_kernel (g : N) (hg : g ∈ N1) :
    FixesK1Orbits g ↔ g ∈ J :=
  fixesK1Orbits_iff_mem_J trialityOrbitPresentation g hg

theorem Q1_inf_J_eq_K1 : Q1 ⊓ J = K1 := Q1_inf_J trialityOrbitPresentation

theorem Q1_axis1_characterization (g : N) (hg : g ∈ N1) :
    g ∈ Q1 ↔ ∀ d : ParkerLoop, ∃ e : ParkerLoop,
      g.val (axis1 d) = axis1 e ∧ e.1 = d.1 :=
  mem_Q1_iff_axis1_code trialityOrbitPresentation g hg

theorem NPlus_mapsTo_axes (g : N) (hg : g ∈ NPlus) :
    Set.MapsTo g.val A2 A2 ∧ Set.MapsTo g.val A3 A3 :=
  NPlus_preserves_axes trialityOrbitPresentation g hg

theorem NPlus_axis2_k1_kernel (g : N) (hg : g ∈ NPlus) :
    FixesAxis2K1Orbits g ↔ g ∈ axis2K1Kernel :=
  fixesAxis2K1Orbits_iff_mem_axis2K1Kernel trialityOrbitPresentation g hg

theorem NPlus_axis2_k3_kernel (g : N) (hg : g ∈ NPlus) :
    FixesAxis2K3Orbits g ↔ g ∈ axis2K3Kernel :=
  fixesAxis2K3Orbits_iff_mem_axis2K3Kernel trialityOrbitPresentation g hg

theorem NPlus_commute_k3 (g : N) (hg : g ∈ NPlus) : Commute g k3 :=
  NPlus_commutes_k3 trialityOrbitPresentation g hg

end Sporadic.Monster.Construction.TrialitySpin
