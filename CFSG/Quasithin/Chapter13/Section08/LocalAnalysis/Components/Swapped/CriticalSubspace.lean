module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The critical-line dimension bound in 13.8.16

An element whose displacement sends D into a line has displacement rank at
most `codim(D) + 1` on the whole module. The proof compares the restricted
and full kernels by rank-nullity. Consequently displacement rank at least
four contradicts the critical-line condition when D has codimension two.

In the orthogonal branch of 13.8.16 this is the final linear contradiction
from F.9.13(6) and F.9.16(2). The displacement bound for the actual
Omega-four-plus model, and the construction of D and its commutator line,
remain separate obligations; no assertion about an arbitrary module of
dimension eight is made here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.8.16, printed p.953 (PDF p.970).
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped
variable {k G U : Type*} [Field k] [Group G] [AddCommGroup U] [Module k U]
    [FiniteDimensional k U]

/-- A small displacement image on D bounds displacement on the whole module by its codimension. -/
theorem displacement_rank_le_of_critical_line (ρ : Representation k G U)
    (D S : Submodule k U) (g : G)
    (hcomm : ∀ d ∈ D, ρ g d - d ∈ S) :
    Module.finrank k (LinearMap.range (ρ g - LinearMap.id)) ≤
      Module.finrank k (U ⧸ D) + Module.finrank k S := by
  let f : U →ₗ[k] U := ρ g - LinearMap.id
  let fD : D →ₗ[k] U := f.comp D.subtype
  have hr : LinearMap.range fD ≤ S := by
    rintro _ ⟨d, rfl⟩
    exact hcomm d d.property
  have hk : (LinearMap.ker fD).map D.subtype ≤ LinearMap.ker f := by
    rintro _ ⟨d, hd, rfl⟩
    exact hd
  have hkd := (Submodule.equivMapOfInjective D.subtype D.subtype_injective
    (LinearMap.ker fD)).finrank_eq
  have hkdim := Submodule.finrank_mono hk
  have hrdim := Submodule.finrank_mono hr
  have htotal := f.finrank_range_add_finrank_ker
  have hrestricted := fD.finrank_range_add_finrank_ker
  have hD := D.finrank_quotient_add_finrank
  change Module.finrank k (LinearMap.range f) ≤ _
  omega

/-- Rank-four displacement cannot send a codimension-two subspace into a line. -/
theorem no_critical_line_of_displacement_rank_four (ρ : Representation k G U)
    (D S : Submodule k U) (g : G)
    (hD : Module.finrank k (U ⧸ D) ≤ 2) (hS : Module.finrank k S ≤ 1)
    (hg : 4 ≤ Module.finrank k (LinearMap.range (ρ g - LinearMap.id))) :
    ¬ ∀ d ∈ D, ρ g d - d ∈ S := by
  intro hcomm
  have := displacement_rank_le_of_critical_line ρ D S g hcomm
  omega

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped

end
