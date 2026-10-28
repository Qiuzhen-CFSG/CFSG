module
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Linarith

/-!
# The index of a core intersection enlarged by a span

If [Q:Q ∩ M] = q and [M:M ∩ R] = q², restriction and the index tower
bound [Q:Q ∩ R] by q³. A subgroup V ≤ Q with [V:V ∩ R] = q then
reduces the index of (Q ∩ R)V to at most q². The join formulation does
not require the set product to be a subgroup or any ambient normality.

This is the geometric index step used in DGS85 (12.6), printed p.183;
SuzukiSeedFixedIndex supplies its literal core/span application and proves
its premises from the marked common Sylows and (12.3)(a).
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A span with q cosets removes one q-factor from the three-step core index. -/
theorem core_span_index_bound (Q M R V : Subgroup G) [Finite Q] [Finite M]
    {q : ℕ} (hq : 0 < q) (hVQ : V ≤ Q)
    (hQM : M.relIndex Q = q) (hMR : R.relIndex M = q^2)
    (hVR : R.relIndex V = q) : ((Q ⊓ R) ⊔ V).relIndex Q ≤ q^2 := by
  let I := Q ⊓ R
  let H := I ⊔ V
  have hHQ : H ≤ Q := sup_le inf_le_left hVQ
  let : Finite H := Finite.of_injective (inclusion hHQ) (inclusion_injective _)
  have htriple : (R ⊓ M).relIndex Q ≤ q^2*q := by
    rw [←relIndex_inf_mul_relIndex,hQM]
    exact Nat.mul_le_mul_right q ((relIndex_le_of_le_right inf_le_left
      (show (R.subgroupOf M).index ≠ 0 from index_ne_zero_of_finite)).trans_eq hMR)
  have hQR : I.relIndex Q ≤ q^2*q := by
    rw [show I = Q ⊓ R from rfl,inf_relIndex_left]
    exact (relIndex_le_of_le_left inf_le_left (show ((R ⊓ M).subgroupOf Q).index ≠ 0 from index_ne_zero_of_finite)).trans htriple
  have hIV : I.relIndex V = q := by
    have he : I.subgroupOf V = R.subgroupOf V := by
      ext x
      exact ⟨fun hx => hx.2, fun hx => ⟨hVQ x.property,hx⟩⟩
    change (I.subgroupOf V).index = q
    rw [he]
    exact hVR
  have hIH : q ≤ I.relIndex H := by
    rw [←hIV]
    exact relIndex_le_of_le_right le_sup_right (show (I.subgroupOf H).index ≠ 0 from index_ne_zero_of_finite)
  have hm := relIndex_mul_relIndex I H Q le_sup_left hHQ
  have hh : q * H.relIndex Q ≤ q^2*q :=
    (Nat.mul_le_mul_right (H.relIndex Q) hIH).trans (hm ▸ hQR)
  change H.relIndex Q ≤ q^2
  nlinarith

end Subgroup

