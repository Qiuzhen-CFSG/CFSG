module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.FieldTransport
public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors

/-!
# Assembly of the trivial SU₃(5) principal-series calculation

Trivial induction is identified with the actual coset permutation module,
Borel-preserving field transport reduces the matrix field to GF(25), and
the constant and augmentation factors are supplied over the original
coefficient field. The checked canonical middle flag supplies simple factors
of dimensions 104 and 20 over that same field. Together they construct the
literal induction filtration with successive degrees 1, 104, 20 and 1,
proving `trivial_principal_series_filtrations` without additional premises.

Source motivation: Guralnick–Malle, *Classification of 2F-modules I*,
Proposition 4.3, p.10; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

open scoped MonoidAlgebra
open BenderSuzuki.MatrixGroups

namespace Representation.SU3.FiveSmallModules.Degrees
open TrivialCalculation
universe v

/-- The concrete middle flag, together with Borel-preserving matrix-field
transport, yields the literal trivial principal-series filtration. Neither
remaining premise is asserted by this conditional assembly. -/
theorem trivial_principal_series_filtrations_of_middleFlags
    (hp : BorelFieldTransport) (hm : CanonicalMiddleFlags.{v}) :
    TrivialPrincipalSeriesFiltrations.{0, v} := by
  intro F _ _ J hF hc K _ _ _
  obtain ⟨e, he⟩ := hp F J hF hc
  let a := inductionCosetEquiv (K := K) (standardBorel J)
  let b := cosetModuleEquiv (K := K) (standardBorel J) canonicalBorel e he
  let c := functionEquiv (K := K) (Ω := CanonicalPoints)
  let E := a.trans (b.trans c)
  have hE : ∀ g v,
      E (ind (standardBorel J).subtype (scalarCharacter (1 : standardBorel J →* Kˣ)) g v) =
        functionAction (e g) (E v) := by
    intro g v
    change c (b (a (ind (standardBorel J).subtype
      (scalarCharacter (1 : standardBorel J →* Kˣ)) g v))) = _
    rw [inductionCosetEquiv_equivariant, cosetModuleEquiv_equivariant,
      functionEquiv_equivariant]
    rfl
  apply (filtration_of_middleFlag (hm K)).transport e.symm.toMonoidHom e.symm.surjective
    _ E.symm
  intro g v
  apply E.injective
  rw [E.apply_symm_apply, hE]
  change functionAction g v = functionAction (e (e.symm g)) (E (E.symm v))
  rw [e.apply_symm_apply, E.apply_symm_apply]
/-- Field transport is discharged; only the two concrete middle factors remain. -/
theorem trivial_principal_series_filtrations_of_canonicalMiddleFlags
    (h : CanonicalMiddleFlags.{v}) : TrivialPrincipalSeriesFiltrations.{0, v} :=
  trivial_principal_series_filtrations_of_middleFlags borel_field_transport h

/-- The actual trivial-character principal series has simple successive
quotients of degrees in `{1, 20, 104}` over every finite characteristic-two
coefficient field. Borel-preserving field transport and the canonical middle
flag discharge all premises of the filtration construction. -/
theorem trivial_principal_series_filtrations : TrivialPrincipalSeriesFiltrations.{0, v} :=
  trivial_principal_series_filtrations_of_canonicalMiddleFlags canonical_middle_flags

end Representation.SU3.FiveSmallModules.Degrees
