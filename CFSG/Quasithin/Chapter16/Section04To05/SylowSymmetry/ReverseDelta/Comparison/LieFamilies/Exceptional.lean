module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.InnerOnly
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.FieldComparison
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Exceptional.BinaryComparison

/-!
# Exceptional characteristic-two residual comparisons

The five exceptional constructors of Theorem C are excluded under the exact
earlier inputs in `Exceptional.Rows`. G₂ and genuine triality use odd-order
divisibility through both central kernels; G₂(2)′ uses actual relative
normality and the orders 24 and 12. The G₂(4) covering kernel is retained.

For positive Ree parameters the odd field period kills the outer class of
an involution with an inner--field expression. The Tits endpoint instead
uses the full binary Ree action and its involution coverage. In particular
no odd-order claim about Out(Tits) is made.

These are conditional family exclusions. The earlier table clauses,
the precise triality divisor, the binary G₂ centerless clause, and the
Tits coverage inputs must be discharged by the source assembly owner.
This module does not assert the completed source theorem 16.4.11.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
16.1.2--4, printed pp.1170--1171, and proof of 16.4.11(2), p.1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory LiePreliminaries Exceptional
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- Positive Ree parameters have no outer involution once the exact
inner--field expression from the earlier table is supplied. -/
theorem not_ree_f4_quotient (d : Contrary T z L g R r) (table : ReeInvolutionTable)
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* ReeF4.Model m) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  apply not_quotient_model_of_inner_involutions d
    ((centerQuotientEquivTwoCore (component_oddCore d)).trans e)
  intro a ha
  obtain ⟨x, k, hx⟩ := table m hm a ha
  obtain ⟨y, hy⟩ := ReeF4.Parabolics.OuterLocal.inner_of_twoPower_of_inner_field
    m a x k 1 hx (by simpa only [pow_one, ha] using pow_orderOf_eq_one a)
  exact ⟨y, hy.symm⟩

/-- The separate Tits endpoint. Bijective binary derived action and coverage
of the actual full Ree involutions imply innerness, without an outer-order premise. -/
theorem not_tits_quotient (d : Contrary T z L g R r) (rows : TitsInvolutionInputs)
    (e : (L ⧸ pCore 2 L) ≃* Tits.ParrottGroup) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  apply not_quotient_model_of_inner_involutions d
    ((centerQuotientEquivTwoCore (component_oddCore d)).trans e)
  intro a ha
  obtain ⟨x, hx, _⟩ := Tits.InvolutionRootGeometry.involution_inner_root_of_binary_coverage
    rows.derived_action rows.involutions a
    (by simpa only [ha] using pow_orderOf_eq_one a)
    (by intro he; simp [he] at ha)
  exact ⟨x, hx⟩

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
