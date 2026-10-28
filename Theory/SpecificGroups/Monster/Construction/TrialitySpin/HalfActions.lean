module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SpinAction

/-!
# The two actual half-spin actions of `NPlus`

The even triality subgroup preserves each axis. Restricting its actual
permutations gives the two 2048-dimensional signed modules, with invariant
positive forms and monomial bases. The first action has exactly the specified
three-generator kernel, by the concrete axis-orbit theorem.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.3(5) and the paragraph before
Lemma 27.5, printed pp. 146–147. Odd first automorphisms act on the full spin
space instead; they need not preserve either half separately.
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin.HalfActions

def inclusion : NPlus →* N1 := Subgroup.inclusion NPlus_le_N1

def permutations : NPlus →* Equiv.Perm Triple := SpinAction.permutations.comp inclusion

theorem preserves_axis2 (g : NPlus) (a : Triple) :
    a ∈ A2 ↔ permutations g a ∈ A2 :=
  (NPlus_mem_axes_iff trialityOrbitPresentation g.val g.prop a).1.symm

theorem preserves_axis3 (g : NPlus) (a : Triple) :
    a ∈ A3 ↔ permutations g a ∈ A3 :=
  (NPlus_mem_axes_iff trialityOrbitPresentation g.val g.prop a).2.symm

theorem commutes_k1 (g : NPlus) (a : Triple) :
    permutations g (k1.val a) = k1.val (permutations g a) :=
  SpinAction.commutes_k1 (inclusion g) a

theorem commutes_z1 (g : NPlus) (a : Triple) :
    permutations g (z1 a) = z1 (permutations g a) :=
  SpinAction.commutes_z1 (inclusion g) a

def secondRepresentation : Representation ℝ NPlus B1A2 :=
  secondAxisDomain.inducedRepresentation permutations preserves_axis2 commutes_k1 commutes_z1

def thirdRepresentation : Representation ℝ NPlus B1A3 :=
  thirdAxisDomain.inducedRepresentation permutations preserves_axis3 commutes_k1 commutes_z1

theorem secondRepresentation_kernel :
    secondRepresentation.ker = axis2K1Kernel.subgroupOf NPlus := by
  ext g
  change secondRepresentation g = 1 ↔ g.val ∈ axis2K1Kernel
  rw [← NPlus_axis2_k1_kernel g.val g.prop]
  rw [show secondRepresentation g = 1 ↔
      ∀ a ∈ A2, permutations g a = a ∨ permutations g a = k1.val a from
    secondAxisDomain.inducedRepresentation_kernel_iff permutations preserves_axis2
      commutes_k1 commutes_z1 g]
  constructor
  · intro h b
    exact h (axis2 b) ⟨b,rfl⟩
  · rintro h a ⟨b,rfl⟩
    exact h b

theorem secondRepresentation_isometry (g : NPlus) (v w : B1A2) :
    secondAxisDomain.form (secondRepresentation g v) (secondRepresentation g w) =
      secondAxisDomain.form v w :=
  secondAxisDomain.representation_isometry
    (secondAxisDomain.restrictPermutations permutations preserves_axis2)
    (fun g a => Subtype.ext (commutes_k1 g a.val))
    (fun g a => Subtype.ext (commutes_z1 g a.val)) g v w

theorem thirdRepresentation_isometry (g : NPlus) (v w : B1A3) :
    thirdAxisDomain.form (thirdRepresentation g v) (thirdRepresentation g w) =
      thirdAxisDomain.form v w :=
  thirdAxisDomain.representation_isometry
    (thirdAxisDomain.restrictPermutations permutations preserves_axis3)
    (fun g a => Subtype.ext (commutes_k1 g a.val))
    (fun g a => Subtype.ext (commutes_z1 g a.val)) g v w

theorem secondRepresentation_monomial (g : NPlus)
    (a : secondAxisDomain.signedOrbits.toPairing.Orbit) :
    ∃ b, secondRepresentation g (secondAxisDomain.basis a) = secondAxisDomain.basis b ∨
      secondRepresentation g (secondAxisDomain.basis a) = -secondAxisDomain.basis b :=
  secondAxisDomain.representation_monomial
    (secondAxisDomain.restrictPermutations permutations preserves_axis2)
    (fun g a => Subtype.ext (commutes_k1 g a.val))
    (fun g a => Subtype.ext (commutes_z1 g a.val)) g a

theorem thirdRepresentation_monomial (g : NPlus)
    (a : thirdAxisDomain.signedOrbits.toPairing.Orbit) :
    ∃ b, thirdRepresentation g (thirdAxisDomain.basis a) = thirdAxisDomain.basis b ∨
      thirdRepresentation g (thirdAxisDomain.basis a) = -thirdAxisDomain.basis b :=
  thirdAxisDomain.representation_monomial
    (thirdAxisDomain.restrictPermutations permutations preserves_axis3)
    (fun g a => Subtype.ext (commutes_k1 g a.val))
    (fun g a => Subtype.ext (commutes_z1 g a.val)) g a

end Sporadic.Monster.Construction.TrialitySpin.HalfActions
