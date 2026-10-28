module

public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.Reduction
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.LocalLifts
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.OctadSplitting

/-!
# Assembly of the two-primary M₂₄ kernel exclusion

This assembly applies two separate local calculations to the
literal octad preimage of each perfect central double cover. The first is a
splitting criterion for central double extensions of the native octad
stabilizer, given an elementary translation preimage and an involutory root
lift. The second constructs precisely those two inputs inside each ambient
M₂₄ double cover. Local transfer then excludes a kernel of order two.

The proved prime-kernel quotient theorem reduces every finite perfect central
cover with even kernel to this double-cover case. The unconditional theorem
supplies both local calculations and excludes two from every finite perfect
central cover kernel. Combined with the independent odd-primary exclusion,
this gives the trivial multiplier asserted for M₂₄ in I.1.3.

Source: Aschbacher–Smith I.1.1–I.1.3, printed p.407, citing GLS3 §6.1;
M₂₄ occurs in A.2.3(5) and is absent from the exhaustive nontrivial list I.1.3.
-/

open Subgroup PerfectCentralCovering

namespace Sporadic.Mathieu.SchurMultipliers
open M24TwoPrimary
universe u

/-- Local splitting and the actual local lift calculation together exclude the
entire two-primary part, with no bound assumed on its original exponent. -/
public theorem m24_cover_kernel_not_two_of_local_inputs
    {E : Type u} [Group E] [Finite E]
    (localSplitting : ∀ (L : Type u) [Group L] [Finite L] (q : L →* OctadGroup),
      Function.Surjective q → q.ker ≤ center L → Nat.card q.ker = 2 →
      ElementaryKernelPreimage q → HasInvolutoryRoot q →
      ∃ s : OctadGroup →* L, q.comp s = MonoidHom.id OctadGroup)
    (localLifts : ∀ (D : Type u) [Group D] [Finite D] (g : Cover D M24),
      Nat.card g.toMonoidHom.ker = 2 →
      ElementaryKernelPreimage (octadProjection g) ∧
      HasInvolutoryRoot (octadProjection g))
    (f : Cover E M24) : ¬ 2 ∣ Nat.card f.toMonoidHom.ker := by
  intro hdiv
  obtain ⟨D, hD, hfin, g, hcard⟩ := PrimaryReduction.exists_prime_order_quotient f hdiv
  let := hD
  let := hfin
  obtain ⟨hV, ht⟩ := localLifts D g hcard
  obtain ⟨s, hs⟩ := localSplitting (octadPreimage g) (octadProjection g)
    (octadProjection_surjective g) (octadProjection_ker_le_center g)
    ((octadProjection_kernel_card g).trans hcard) hV ht
  exact not_two_of_octad_section g s hs (by rw [hcard])

/-- Two does not divide the kernel order of any finite perfect central cover
of the native Witt-design model of M₂₄. The local lifting and splitting
premises are discharged by the actual octad calculations. -/
public theorem m24_cover_kernel_not_two
    {E : Type u} [Group E] [Finite E] (f : Cover E M24) :
    ¬ 2 ∣ Nat.card f.toMonoidHom.ker :=
  m24_cover_kernel_not_two_of_local_inputs
    (fun _ _ _ q => octad_double_extension_section q)
    m24_double_cover_local_lifts f

end Sporadic.Mathieu.SchurMultipliers
