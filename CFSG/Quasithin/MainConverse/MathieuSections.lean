module

public import CFSG.Quasithin.MainConverse.MathieuSections.Reduction
public import CFSG.Quasithin.Models
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SimpleSections

/-!
# Simple sections of the concrete Mathieu carriers

Source: Aschbacher–Smith, Theorem 0.1.2(5), condition K, printed pp. 4 and
482. The required conclusion concerns every simple quotient of every
subgroup of every proper subgroup of M11, M12, M22, M23 and M24.

This module currently proves the whole-carrier quotient case, with
simplicity inherited from the caller, and exports the solvable-layer and
cross-universe assembly reductions. For the concrete M23 heptad stabilizer,
its nonsolvable simple sections are proved to be exactly those of A7.
The remaining proper-subgroup cases still require the Mathieu subgroup
classifications. In particular this module does not yet assert proper K.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

/-- A nontrivial quotient of an inherited simple Mathieu model is isomorphic
to the same concrete Mathieu carrier. This handles whole-model numerators
when a smaller Mathieu group occurs inside a larger one. -/
public theorem mathieu_simple_quotient_constructed
    {G S : Type*} [Group G] [IsSimpleGroup G]
    [Group S] [Nontrivial S] (hG : IsMathieuModel G)
    (f : G →* S) (hf : Function.Surjective f) : IsConstructedCarrier S := by
  apply MathieuSections.constructed_simple_quotient_of_simple (f := f) ?_ hf
  apply IsConstructedCarrier.sporadic
  rcases hG with h | h | h | h | h
  · exact ⟨.m11, h⟩
  · exact ⟨.m12, h⟩
  · exact ⟨.m22, h⟩
  · exact ⟨.m23, h⟩
  · exact ⟨.m24, h⟩

end CFSG.Quasithin.MainConverse
