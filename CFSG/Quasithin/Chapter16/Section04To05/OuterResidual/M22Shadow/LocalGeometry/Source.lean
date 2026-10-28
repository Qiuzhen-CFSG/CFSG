module

public import CFSG.Quasithin.Chapter16.Section04To05.OuterResidual.M22Shadow.Reductions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements

/-!
# The marked outer M₂₂ case

The hypothesis of Lemma 16.4.7 concerns the action of the given element r
on L/Z(L). We transport that action along an actual equivalence with the
Witt-design M₂₂. Its fixed group is an extension with elementary kernel
of order sixteen and quotient the Suzuki matrix group Sz(2). The slash in
the source does not assert that the extension splits.

This file specifies the contrary case, not its exclusion or its local
geometry. In particular it makes no assumption about Q, R₀, or V.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 16.4.7, printed p.1186, and 16.1.5(5), printed p.1171.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow

open Subgroup

variable {G : Type*} [Group G]

/-- Conjugation by r on the actual central quotient, transported to M₂₂. -/
noncomputable def quotientModelAction (L : Subgroup G) (r : G)
    (hn : r ∈ normalizer (L : Set G))
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M22) : MulAut Sporadic.Mathieu.M22 :=
  MulAut.congr e ((center L).quotientAut (L.normalizerMonoidHom ⟨r, hn⟩))

/-- The model action intertwines the quotient of ambient conjugation. -/
theorem quotientModelAction_apply (L : Subgroup G) (r : G)
    (hn : r ∈ normalizer (L : Set G))
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M22) (x : L) :
    quotientModelAction L r hn e (e (QuotientGroup.mk' (center L) x)) =
      e (QuotientGroup.mk' (center L) (L.normalizerMonoidHom ⟨r, hn⟩ x)) := by
  change e ((center L).quotientAut _ (e.symm (e _))) = _
  rw [e.symm_apply_apply, quotientAut_apply_mk]

/-- The exact contrary case in 16.4.7, using genuine carriers and the
given element's action. This is an input specification, not a source theorem. -/
structure OuterFixedModel (L : Subgroup G) (r : G) where
  involution : orderOf r = 2
  normalizes : r ∈ normalizer (L : Set G)
  quotientEquiv : (L ⧸ center L) ≃* Sporadic.Mathieu.M22
  outer : L.normalizerMonoidHom ⟨r, normalizes⟩ ∉ MulAut.innerSubgroup L
  fixedExtension : GroupExtension (OtherPreliminaries.Mathieu.Elementary 4)
    (quotientModelAction L r normalizes quotientEquiv).fixedSubgroup
    OtherPreliminaries.Mathieu.SzTwo

end CFSG.Quasithin.Chapter16.Intersections.OuterResidual.M22Shadow
