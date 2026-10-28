module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support12
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support012
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support13
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support013
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support23
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support023
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support123
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End0Support0123
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support01
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support02
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support12
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support012
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support013
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support023
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support123
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Radical.Codimension.End1Support0123

/-!
# Codimension nine for the two binary SL₅ end-root groups

For each end and each support with at least two active nodes away from that
end, nine vectors have independent images in the quotient by the common
fixed space of the four marked radical roots. Fourteen cases use permutation
translates of the local highest vector. The two opposite end-adjacent cases
also use root differences of translates. In every case, triangular extracting
operators begin with a radical difference and thus factor through that exact
quotient. All root action and commutation identities are checked in Lean.

This proves the codimension input to radical maximization, without assuming
cubicity of the whole radical, absolute irreducibility, a degree cutoff or a
classification of modules. Faithfulness and irreducibility are not needed for
the stronger local statement; the requested interface retains them.

Source application: Guralnick–Malle, Classification of 2F-modules II,
Proposition 4.7 step 1, pp.25–26; Aschbacher–Smith K.3.2, printed pp.454–455.
-/

public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
open Representation Representation.BinaryOffender
open SL5TenDimensional.Classification

private theorem support_cases_0 (J : Finset (Fin 4))
    (h : 2 ≤ (J.erase 0).card) :
    J = {1, 2} ∨ J = {0, 1, 2} ∨ J = {1, 3} ∨ J = {0, 1, 3} ∨ J = {2, 3} ∨ J = {0, 2, 3} ∨ J = {1, 2, 3} ∨ J = {0, 1, 2, 3} := by
  revert J
  decide +kernel

private theorem support_cases_1 (J : Finset (Fin 4))
    (h : 2 ≤ (J.erase 3).card) :
    J = {0, 1} ∨ J = {0, 2} ∨ J = {1, 2} ∨ J = {0, 1, 2} ∨ J = {0, 1, 3} ∨ J = {0, 2, 3} ∨ J = {1, 2, 3} ∨ J = {0, 1, 2, 3} := by
  revert J
  decide +kernel

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (σ : Representation (ZMod 2) SL5TenDimensional.Group V)

/-- Local root relations alone imply the common-fixed-space codimension bound. -/
theorem root_codimension_estimate_of_local_highest [FiniteDimensional (ZMod 2) V] :
    RootCodimensionEstimate σ := by
  intro e J v hv hhighest hsupport
  fin_cases e
  · change 2 ≤ (J.erase 0).card at hsupport
    rcases support_cases_0 J hsupport with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Codimension.End0Support12.nine_le_fixedCodim hhighest hv
    · exact Codimension.End0Support012.nine_le_fixedCodim hhighest hv
    · exact Codimension.End0Support13.nine_le_fixedCodim hhighest hv
    · exact Codimension.End0Support013.nine_le_fixedCodim hhighest hv
    · exact Codimension.End0Support23.nine_le_fixedCodim hhighest hv
    · exact Codimension.End0Support023.nine_le_fixedCodim hhighest hv
    · exact Codimension.End0Support123.nine_le_fixedCodim hhighest hv
    · exact Codimension.End0Support0123.nine_le_fixedCodim hhighest hv
  · change 2 ≤ (J.erase 3).card at hsupport
    rcases support_cases_1 J hsupport with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Codimension.End1Support01.nine_le_fixedCodim hhighest hv
    · exact Codimension.End1Support02.nine_le_fixedCodim hhighest hv
    · exact Codimension.End1Support12.nine_le_fixedCodim hhighest hv
    · exact Codimension.End1Support012.nine_le_fixedCodim hhighest hv
    · exact Codimension.End1Support013.nine_le_fixedCodim hhighest hv
    · exact Codimension.End1Support023.nine_le_fixedCodim hhighest hv
    · exact Codimension.End1Support123.nine_le_fixedCodim hhighest hv
    · exact Codimension.End1Support0123.nine_le_fixedCodim hhighest hv

/-- The root codimension estimate in the faithful irreducible source interface. -/
theorem root_codimension_estimate [FiniteDimensional (ZMod 2) V]
    (_hfaithful : Function.Injective σ) (_hirreducible : Representation.IsIrreducible σ) :
    RootCodimensionEstimate σ :=
  root_codimension_estimate_of_local_highest σ

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode
