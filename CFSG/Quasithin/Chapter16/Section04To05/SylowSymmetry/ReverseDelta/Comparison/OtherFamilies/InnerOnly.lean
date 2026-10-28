module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.InnerOnly
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Mathieu.Statements

/-!
# Inner-only sporadic rows in reverse Δ₀

The contrary action on L′ is an actual outer involution. Transport to the
simple quotient detects innerness, so the inner-only rows are impossible.
The complete nine-name (E2)(iii) catalogue consequently leaves M₁₂, M₂₂,
J₂ and HS, each through an actual central-quotient isomorphism.

M₁₁ uses its proved automorphism theorem. The remaining consumed clauses
of the earlier table are explicit in `InnerOnlySporadicRows`. In particular,
no normalizer-square result is used as a substitute for J₄ innerness.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.5(3),(6),(7),(9),(11) and the proof of 16.4.11(2), pp.1171–1172 and 1193.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
open Subgroup Theory.GroupTheory LiePreliminaries
open OtherPreliminaries.Mathieu

/-- The consumed innerness clauses of 16.1.5(6),(7),(9),(11). The Mathieu
 fields retain the full existing source rows; the last two fields concern
 actual automorphisms of the specified matrix carriers. These are explicit
 earlier table inputs, not results about arbitrary family labels. -/
structure InnerOnlySporadicRows : Prop where
  m23 : ∀ a : MulAut Sporadic.Mathieu.M23, orderOf a = 2 → M23InvolutionAlternative a
  m24 : ∀ a : MulAut Sporadic.Mathieu.M24, orderOf a = 2 → M24InvolutionAlternative a
  j4 : ∀ a : MulAut Janko4.Model, orderOf a = 2 → ∃ x, a = MulAut.conj x
  ru : ∀ a : MulAut Rudvalis.Model, orderOf a = 2 → ∃ x, a = MulAut.conj x

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- The complete nine-name sporadic catalogue reduces to the four families
 with outer involutions. The quotient by O₂(L) is transported canonically
 to L/Z(L), using (E1), rather than silently changing the convention. -/
theorem sporadic_remaining (d : Contrary T z L g R r) (rows : InnerOnlySporadicRows)
    (h : IsEvenTypeSporadicQuotient (L ⧸ pCore 2 L)) :
    Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M12) ∨
    Nonempty ((L ⧸ center L) ≃* Sporadic.Mathieu.M22) ∨
    Nonempty ((L ⧸ center L) ≃* Sporadic.LeechRelated.J2.Carrier) ∨
    Nonempty ((L ⧸ center L) ≃* Sporadic.LeechRelated.HS.Carrier) := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  obtain ⟨name, hj3, hhe, ⟨e⟩⟩ := h
  let eZ := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  cases name with
  | m11 => exact (not_m11_quotient d eZ).elim
  | m12 => exact Or.inl ⟨eZ⟩
  | m22 => exact Or.inr (Or.inl ⟨eZ⟩)
  | m23 =>
    exact (not_quotient_model_of_inner_involutions d eZ (fun a ha => (rows.m23 a ha).1)).elim
  | m24 =>
    exact (not_quotient_model_of_inner_involutions d eZ (fun a ha => (rows.m24 a ha).1)).elim
  | j2 => exact Or.inr (Or.inr (Or.inl ⟨eZ⟩))
  | j3 => exact (hj3 rfl).elim
  | j4 => exact (not_quotient_model_of_inner_involutions d eZ rows.j4).elim
  | hs => exact Or.inr (Or.inr (Or.inr ⟨eZ⟩))
  | he => exact (hhe rfl).elim
  | ru => exact (not_quotient_model_of_inner_involutions d eZ rows.ru).elim
end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies
