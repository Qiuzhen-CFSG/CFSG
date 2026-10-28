module

public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.ModelConstruction.Product
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Cases
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.EmptyCase
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Elementary
public import CFSG.Quasithin.Chapter16.Section04To05.InnerFamily.Alternating.ModelConstruction.Choices

/-!
# Construction of the marked alternating overgroup

The A₈ branch constructs the actual isomorphism LE ≅ S₈ × C₂. Transport
of the ambient action to Aut(A₈) gives an odd permutation; its square and
sign give precisely the transposition and triple-transposition alternatives.
The central factor and the images of L and r are then proved by `Product`.
The construction applies to the original data, with no change of Sylow.

For A₆ the same construction is supplied conditional on compatible
transposition coordinates. Deriving those coordinates from the actual
PGL₂(9) exclusion remains a separate obligation; the conditional theorem
below does not assert that recognition result. Neither theorem identifies
LT with LE, so the full Aut(A₆) exception remains available.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 16.4.9(2), printed p.1192.
-/

@[expose] public section

open Subgroup Equiv Equiv.Perm
open Theory.SpecificGroups.Alternating.OddInvolutionExtension
namespace CFSG.Quasithin.Chapter16.Intersections
variable {G : Type*} [Group G] [Finite G]

/-- The A₈ marked product exists for the original intersection setup. -/
theorem IntersectionSetup.alternatingProductModel_eight
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (hrout : r ∉ centralizer (L : Set G) ⊔ L)
    (e : L ≃* alternatingGroup (Fin 8)) :
    Nonempty (AlternatingProductModel L z r 8) := by
  have hrpow : r ^ 2 = 1 := hr2 ▸ pow_orderOf_eq_one r
  obtain ⟨s, hs, ho, ha⟩ := exists_odd_involution_action (by decide) (by decide) e
    (h.sylow_normalizes (h.le_sylow hr)) hrpow hrout
  apply alternatingProductModel_of_odd_action (by decide) e h.involution hrpow
    h.component.1 (h.sylow_centralizes (h.le_sylow hr)) s hs ho ha
  rcases odd_involution_eight_cycleType s hs ho with hc | hc
  · exact Or.inl hc
  · exact Or.inr ⟨rfl, hc⟩

/-- The conditional A₆ assembly: compatible transposition coordinates suffice.
Their construction from the PGL₂(9) exclusion is a separate obligation. -/
theorem IntersectionSetup.alternatingProductModel_six_of_transposition
    {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R) (hr : r ∈ R) (hr2 : orderOf r = 2)
    (e : L ≃* alternatingGroup (Fin 6)) (s : Perm (Fin 6)) (hs : s.IsSwap)
    (haction : ∀ k : alternatingGroup (Fin 6),
      (e.symm (MulAut.conjNormal s k) : G) = r * (e.symm k : G) * r⁻¹) :
    Nonempty (AlternatingProductModel L z r 6) := by
  exact alternatingProductModel_of_odd_action (by decide) e h.involution
    (hr2 ▸ pow_orderOf_eq_one r) h.component.1 (h.sylow_centralizes (h.le_sylow hr))
    s (hs.orderOf ▸ pow_orderOf_eq_one s) hs.sign_eq haction
    (Or.inl (isSwap_iff_cycleType.mp hs))

end CFSG.Quasithin.Chapter16.Intersections
