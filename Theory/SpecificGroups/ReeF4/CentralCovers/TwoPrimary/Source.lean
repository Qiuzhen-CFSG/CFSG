module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.PairSplitting
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.NormalizedBlocks.QuartetSplitting.EightAmbient
public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations

/-!
# Excluding two-primary kernels in Ree covers

The additive pair sections, Suzuki quartet sections, simultaneous torus
normalization and tail relations give a section over the literal positive
subgroup in every central cover of prime kernel order two. At field eight,
the actual perfect-seed centralizer argument supplies the formerly exceptional
Suzuki-root class-two identity. The positive subgroup has odd index, so the
prime-kernel reduction excludes the entire two-primary covering kernel.

Every local source calculation is discharged, with the original projection
triangles retained. Source: Aschbacher--Smith I.1.1--4, pp.407--408;
GLS3 section 6.1 and Table 2.4.
-/

public section
namespace ReeF4.CentralCovers.TwoPrimary
open PerfectCentralCovering

/-- All perfect central covers of the positive-parameter Ree groups have
odd kernel order. This includes the exceptional field-eight case. -/
theorem not_two_dvd_kernel (m : ℕ) (hm : 1 ≤ m)
    {E : Type*} [Group E] [Finite E] (c : Cover E (ReeF4.Model m)) :
    ¬ 2 ∣ Nat.card c.toMonoidHom.ker := by
  apply ReeF4.CentralCovers.not_two_dvd_kernel_of_prime_unipotent_sections m _ c
  intro F _ _ d hd
  have hsmall : m = 1 →
      ReeF4.CentralCovers.TwoPrimary.QuartetSplitting.LiftedRootClassTwo m d.toMonoidHom := by
    rintro rfl
    exact ReeF4.CentralCovers.TwoPrimary.QuartetSplitting.EightAmbient.liftedRootClassTwo
      d.toMonoidHom d.surjective d.ker_le_center
  obtain ⟨L, hL⟩ :=
    ReeF4.CentralCovers.TwoPrimary.exists_torusEquivariant_of_pair_and_quartet_sections m d hd
      (ReeF4.CentralCovers.TwoPrimary.PairSplitting.exists_pair_sections m hm d hd)
      (ReeF4.CentralCovers.TwoPrimary.QuartetSplitting.quartet_sections_of_small_class_two
        m hm d.toMonoidHom d.surjective d.ker_le_center hsmall)
  exact ReeF4.CentralCovers.TwoPrimary.unipotent_section_of_torusEquivariant m hm d L hL

end ReeF4.CentralCovers.TwoPrimary
