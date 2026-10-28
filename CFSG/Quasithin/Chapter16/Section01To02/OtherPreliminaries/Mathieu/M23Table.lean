module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerQuotient

/-!
# The M23 centralizer table: exact transport and component exclusion

The actual seven-point action of the representative involution centralizer
has an elementary abelian kernel of order sixteen. Exhaustive involution
fusion and centerlessness transport this exact sequence to every inner
involutory automorphism. Its genuine self-centralizing kernel also excludes
all components, independently of the quotient identification.

The table assembly uses the proved innerness of M₂₃ automorphisms and the
actual equivalence from the seven-point image to PSL₃(2). It also supplies the
arbitrary-two-element Sylow-centralizing innerness required in 16.1.6.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.5(6)
and 16.1.6–8, printed pp.1171–1173.
-/

public section

open Subgroup Sporadic.Mathieu Theory.GroupTheory
open Sporadic.Mathieu.M23Geometry.InvolutionCentralizer
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu

/-- The exact source extension follows from innerness and the concrete quotient identification. -/
theorem m23_involution_alternative_of_inner_and_quotient (r : MulAut M23)
    (hr : orderOf r = 2) (hi : ∃ g, r = MulAut.conj g)
    (q : action.range ≃* L3Two) : M23InvolutionAlternative r := by
  obtain ⟨e⟩ := fixedSubgroup_equiv_representative_of_inner r hr hi
  exact ⟨hi, ⟨extensionOfEquiv e q⟩⟩

/-- Every involutory automorphism has the exact source centralizer shape. -/
theorem m23_involution_alternative (r : MulAut M23)
    (hr : orderOf r = 2) : M23InvolutionAlternative r := by
  exact m23_involution_alternative_of_inner_and_quotient r hr
    (m23_involution_automorphism_inner r hr) actionEquivPSL

/-- Every two-element automorphism fixing a Sylow two-subgroup pointwise is inner. -/
theorem m23_sylow_centralizing_two_automorphisms :
    HasInnerSylowCentralizingTwoAutomorphisms M23 := by
  intro r n S hr hS
  exact m23_sylow_centralizing_two_automorphism_inner r n S hr hS

/-- The inner M23 branch has no components, using its actual faithful kernel action. -/
theorem m23_involution_no_component_of_inner (r : MulAut M23)
    (hr : orderOf r = 2) (hi : ∃ g, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup) : ¬ IsComponent r.fixedSubgroup K :=
  fixedSubgroup_no_component_of_inner r hr hi K

end CFSG.Quasithin.Chapter16.OtherPreliminaries.Mathieu
