module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BTwoExceptionalFieldBound
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderFiveQuadraticAction
public import Theory.GroupTheory.PGroup.SmallFrattiniLinearForms
public import Theory.SpecificGroups.MinusExtraspecial.Recognition

/-!
# The field-four beta core in the exceptional Chapter 10 branch

The field-four row of (10.9) has a beta core of order thirty-two and a
Frattini quotient of order sixteen.  An order-five element in the literal
Frattini action makes the center image invariant and fixed-point-free; the
five-point orbit calculation therefore forces the center to be the Frattini
subgroup.  This gives the actual extraspecial beta core.  With the source
rank-two bound, the existing order-thirty-two recognition identifies it with
the minus extraspecial model used by the Janko branch.

The order-five actor and rank bound remain explicit inputs here.  They are
the precise source premises still needed before the full J₂ endpoint and path
argument; no ambient parabolic equivalence is inferred by this module.
Source: DGS, Groups and Graphs (1985), proof of (10.9), printed pp.163--164.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
open Theory.GroupTheory

variable {Q : Type*} [Group Q] [Finite Q]

/-- A nonabelian order-thirty-two beta core with an order-five Frattini actor
is extraspecial. -/
theorem field_four_beta_extraspecial
    (hQ : IsPGroup 2 Q) (hnon : ¬ IsMulCommutative Q)
    (hphi : Nat.card (frattini Q) = 2)
    (hquot : Nat.card (Q ⧸ frattini Q) = 16)
    (a : MulAut Q)
    (ha : orderOf (quotientAut (frattini Q) a) = 5) :
    IsExtraspecial 2 Q := by
  let V := Q ⧸ frattini Q
  let q := QuotientGroup.mk' (frattini Q)
  let R := (center Q).map q
  let b := quotientAut (frattini Q) a
  let A := zpowers b
  have hA : Nat.card A = 5 := (Nat.card_zpowers b).trans ha
  have hstable (u : A) (x : V) (hx : x ∈ R) : u • x ∈ R := by
    obtain ⟨n, hn⟩ := u.property
    obtain ⟨z, hz, rfl⟩ := hx
    have he : (u : MulAut V) = quotientAut (frattini Q) (a ^ n) := by
      rw [map_zpow]
      exact hn.symm
    change (u : MulAut V) (q z) ∈ R
    rw [he, quotientAut_apply_mk]
    exact mem_map_of_mem q
      (characteristic_iff_le_comap.mp inferInstance (a ^ n) hz)
  let : IsInvariant A V R := ⟨fun u x =>
    ⟨hstable u x, by simpa only [inv_smul_smul] using hstable u⁻¹ (u • x)⟩⟩
  have hR : R = ⊥ := by
    rcases invariant_eq_bot_or_top_of_five_actor hA hquot
      (SmallNonabelianTwoGroup.order_five_actor_fixed_subgroup_eq_bot hquot A hA) R with
      hz | ht
    · exact hz
    · have hh := congrArg (comap q) ht
      change ((center Q).map q).comap q = (⊤ : Subgroup V).comap q at hh
      rw [comap_map_eq, QuotientGroup.ker_mk', comap_top] at hh
      exact (hnon (center_eq_top_iff.mp (frattini_nongenerating hh))).elim
  have hcenter : center Q = frattini Q := le_antisymm
    (by
      have hh := (map_eq_bot_iff (center Q)).mp hR
      change center Q ≤ frattini Q
      simpa [q] using hh)
    (central_of_normal_card_two _ hphi)
  refine ⟨by rw [hcenter, hphi], ?_, ?_⟩
  · exact SmallFrattini.centralElementary hQ hphi
  · apply QuotientGroup.nontrivial_iff.mpr
    exact fun ht => hnon (center_eq_top_iff.mp ht)

/-- Add the source rank-two bound to obtain the concrete minus extraspecial
model required by the field-four Janko row. -/
theorem field_four_beta_minus_model
    (hQ : IsPGroup 2 Q) (hnon : ¬ IsMulCommutative Q)
    (hphi : Nat.card (frattini Q) = 2)
    (hquot : Nat.card (Q ⧸ frattini Q) = 16)
    (a : MulAut Q)
    (ha : orderOf (quotientAut (frattini Q) a) = 5)
    (hrank : ∀ E : Subgroup Q, IsElementaryAbelian 2 E → Nat.card E < 8) :
    Nonempty (Q ≃* MinusExtraspecial.Model) := by
  let _ : IsExtraspecial 2 Q := field_four_beta_extraspecial hQ hnon hphi hquot a ha
  have hcard : Nat.card Q = 32 := by
    have hh := (frattini Q).index_mul_card
    change Nat.card (Q ⧸ frattini Q) * Nat.card (frattini Q) = Nat.card Q at hh
    rw [hquot, hphi] at hh
    exact hh.symm
  exact IsExtraspecial.exists_mulEquiv_minusExtraspecial_model hrank hcard

end CFSG.Quasithin.ChapterF.Source.DGS85.NoncommutingProfile
