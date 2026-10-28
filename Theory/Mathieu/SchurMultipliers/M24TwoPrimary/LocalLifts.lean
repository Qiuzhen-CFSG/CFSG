module

public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.Reduction
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.LocalLifts.TranslationSquares
public import Theory.Mathieu.SchurMultipliers.M24TwoPrimary.LocalLifts.RootFusion

/-!
# The local lifts in a double cover of native M₂₄

Over the full preimage of the literal seed-octad stabilizer, every lift of a
pointwise translation squares to one. An octad double transposition is fused
to a nonidentity translation in the native ambient group; lifting the
conjugating element through the original cover supplies an involutory root
lift. These are the two local inputs required by the octad splitting argument.

Source context: Aschbacher–Smith, I.1.3, printed p.407; GLS3 §6.1 and the
native E₁₆.A₈ subgroup in Table 5.3e.
-/

open PerfectCentralCovering Sporadic.Mathieu
namespace Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
universe u

/-- The two local lift properties for the actual octad restriction of every
finite perfect central cover of M₂₄ whose kernel has order two. -/
public theorem m24_double_cover_local_lifts
    (E : Type u) [Group E] [Finite E] (f : Cover E M24)
    (hcard : Nat.card f.toMonoidHom.ker = 2) :
    ElementaryKernelPreimage (octadProjection f) ∧
      HasInvolutoryRoot (octadProjection f) := by
  have helem := m24_double_cover_elementary_preimage f hcard
  obtain ⟨v, a, ha, hconj⟩ := exists_octad_root_fusion
  exact ⟨helem, hasInvolutoryRoot_of_fusion f helem v a ha hconj⟩

end Sporadic.Mathieu.SchurMultipliers.M24TwoPrimary
