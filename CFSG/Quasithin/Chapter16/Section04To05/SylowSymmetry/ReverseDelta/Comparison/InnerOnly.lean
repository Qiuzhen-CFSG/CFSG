module
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section01To02.LiePreliminaries.RankOne
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers

/-!
# Excluding quotients whose involutions act innerly

Transport the contrary outer action to the actual simple-quotient model.
Faithfulness of the action on a perfect central quotient preserves order
two and detects innerness. This excludes M₁₁ and every permitted Suzuki
model, using their proved automorphism results, including central covers.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
16.1.4(4), 16.1.5(3), and proof of 16.4.11(2), printed pp.1171 and 1193.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
open Subgroup Theory.GroupTheory LiePreliminaries
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

/-- A model with only inner involutory automorphisms cannot occur. -/
theorem not_quotient_model_of_inner_involutions (d : Contrary T z L g R r)
    {S : Type*} [Group S] (e : (L ⧸ center L) ≃* S)
    (hS : ∀ a : MulAut S, orderOf a = 2 → ∃ x : S, a = MulAut.conj x) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let ec : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  let : IsQuasisimple (L.conjBy g) := IsQuasisimple.of_mulEquiv ec
  let eM := (centralQuotientCongr ec).symm.trans e
  let b := MulAut.centralQuotientAction eM (action d.z_normalizes)
  have hb : orderOf b = 2 :=
    (orderOf_injective (MulAut.centralQuotientAction eM)
      (MulAut.centralQuotientAction_injective eM) _).trans d.outer_action_order
  exact d.outer_action ((MulAut.centralQuotientAction_inner_iff eM _).mp (hS b hb))

/-- M₁₁ is excluded without an assumed table row. -/
theorem not_m11_quotient (d : Contrary T z L g R r)
    (e : (L ⧸ center L) ≃* Sporadic.Mathieu.M11) : False := by
  apply not_quotient_model_of_inner_involutions d e
  intro a _
  exact Sporadic.Mathieu.automorphism_inner_of_equiv_m11 (MulEquiv.refl _) a

/-- Every permitted Suzuki quotient is excluded, including Sz(8) covers. -/
theorem not_suzuki_quotient (d : Contrary T z L g R r) {m : ℕ} (hm : 1 ≤ m)
    (e : (L ⧸ center L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : False := by
  apply not_quotient_model_of_inner_involutions d e
  intro a ha
  apply MulAut.inner_of_two_pow_eq_one_of_odd_index
    (BenderSuzuki.MatrixGroups.suzuki_odd_outer_index m hm) a (k := 1)
  simpa only [pow_one, ha] using pow_orderOf_eq_one a

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison
