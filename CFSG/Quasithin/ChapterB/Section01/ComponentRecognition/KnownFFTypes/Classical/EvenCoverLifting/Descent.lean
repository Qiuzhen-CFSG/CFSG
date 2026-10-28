module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.Models
public import Theory.GroupTheory.CoveringPGroupDescent

/-!
# Concrete classical outputs from two-primary covering comparisons

A commuting comparison from a universal cover to SL or SU, with two-group
kernel, descends onto any covering group with trivial two-core. The result
is an actual central quotient of that same matrix group. If the entire
universal kernel is a two-group, the covering group is the projective model.
The field, dimension, Hermitian form and Frobenius conjugation remain visible
in the linear and unitary applications.

These are conditional adapters for the finite multiplier computations, not
the assertion that those computations have been completed. Keeping them
below the family assembly permits the independent families to import them
without a cycle.

Source: Aschbacher–Smith, B.1.13 and B.4.4; GLS3, Section 6.1,
Theorem 6.1.4 and Corollary 6.1.5.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
universe u v w
variable {L : Type u} [Group L] [Finite L] [IsQuasisimple L]

section UniversalDescent
variable {S : Type v} {U : Type w} {H : Type*}
  [Group S] [Finite S] [IsQuasisimple S]
  [Group U] [Finite U] [IsQuasisimple U]
  [Group H] [Finite H] [IsQuasisimple H]

/-- A concrete covering presents its target as an actual central quotient. -/
theorem isCentralQuotient_of_covering (k : Covering H L) : IsCentralQuotient L H :=
  ⟨k.toMonoidHom.ker, inferInstance, k.ker_le_center,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective k.toMonoidHom k.surjective).symm⟩⟩

/-- A universal cover whose comparison to the concrete model has two-group
kernel gives the required central quotient when the target has trivial two-core.
The model comparison and its commuting triangle remain explicit. -/
theorem isCentralQuotient_of_universal_two_kernel (hcore : pCore 2 L = ⊥)
    (c : Covering U S) (hc : Covering.IsUniversal.{v,w,u} c)
    (a : Covering U H) (f : Covering H S) (hfac : f.comp a = c)
    (ha : IsPGroup 2 a.toMonoidHom.ker) (e : L ⧸ center L ≃* S) :
    IsCentralQuotient L H := by
  let g : Covering L S :=
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  obtain ⟨k, _⟩ := hc.exists_covering_of_pGroup_kernel a f hfac ha g hcore
  exact isCentralQuotient_of_covering k

/-- A two-group universal kernel forces the actual component-to-model map
itself to be bijective. This is the projective symplectic/orthogonal route. -/
theorem nonempty_mulEquiv_of_universal_two_kernel (hcore : pCore 2 L = ⊥)
    (c : Covering U S) (hc : Covering.IsUniversal.{v,w,u} c)
    (hk : IsPGroup 2 c.toMonoidHom.ker) (e : L ⧸ center L ≃* S) :
    Nonempty (L ≃* S) := by
  let g : Covering L S :=
    { toMonoidHom := e.toMonoidHom.comp (QuotientGroup.mk' (center L))
      surjective := e.surjective.comp (QuotientGroup.mk'_surjective _) }
  exact ⟨MulEquiv.ofBijective g.toMonoidHom
    ⟨hc.injective_of_pGroup_kernel hk g hcore, g.surjective⟩⟩
end UniversalDescent


section LinearUnitary
variable {U : Type v} [Group U] [Finite U] [IsQuasisimple U]

/-- Apply two-primary descent to the same linear field and dimension appearing
in the catalogue. The supplied maps retain the actual SL and PSL carriers. -/
theorem isEvenLieGroup_of_linear_two_kernel (hcore : pCore 2 L = ⊥)
    {n q : ℕ} (hp : KnownSimple.LinearParameters n q) (he : Even q)
    (F : Type) [Field F] [Finite F] (hcard : Nat.card F = q)
    [IsQuasisimple SL(n, F)] [IsQuasisimple PSL(n, F)]
    (c : Covering U PSL(n, F)) (hc : Covering.IsUniversal.{0,v,u} c)
    (a : Covering U SL(n, F)) (f : Covering SL(n, F) PSL(n, F))
    (hfac : f.comp a = c) (ha : IsPGroup 2 a.toMonoidHom.ker)
    (e : L ⧸ center L ≃* PSL(n, F)) : IsEvenLieGroup L :=
  .classical (.linear n q hp he F hcard
    (isCentralQuotient_of_universal_two_kernel hcore c hc a f hfac ha e))

/-- Apply the same descent to the actual special unitary group, retaining the
quadratic coefficient field, Hermitian form and Frobenius conjugation. -/
theorem isEvenLieGroup_of_unitary_two_kernel (hcore : pCore 2 L = ⊥)
    {n q : ℕ} (hp : KnownSimple.UnitaryParameters n q) (he : Even q)
    (F : Type) [Field F] [Finite F] (J : BenderSuzuki.MatrixGroups.HermitianForm n F)
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
    [IsQuasisimple J.specialSubgroup]
    [IsQuasisimple (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)]
    (c : Covering U (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (hc : Covering.IsUniversal.{0,v,u} c)
    (a : Covering U J.specialSubgroup)
    (f : Covering J.specialSubgroup
      (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J))
    (hfac : f.comp a = c) (ha : IsPGroup 2 a.toMonoidHom.ker)
    (e : L ⧸ center L ≃* BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :
    IsEvenLieGroup L :=
  .classical (.unitary n q hp he F J hcard hconj
    (isCentralQuotient_of_universal_two_kernel hcore c hc a f hfac ha e))
end LinearUnitary

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical
