module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions.TailFamily.Algebra
public import Stellmacher.ElementaryAbelianMaxDihedral

/-!
# Large elementary subgroups in the cyclic tail

The product R⟨w⟩ has elementary subgroups of order eight. In the faithful
alternative, ⟨y,w⟩ has index two in the full tail. An elementary subgroup
of order at least eight intersects it in at least four elements; the rotation
calculation puts that intersection in ⟨z,w⟩, which has order four. Thus it
contains w, and centralizing w puts the whole elementary subgroup in R⟨w⟩.

The internal direct-product family theorem and the general dihedral generation
calculation identify both the maximum family and its generated product subgroup.
No assertion about all involutions in the full tail is used.

Source: Aschbacher--Smith, 16.3.12, printed p.1182 / PDF p.1199,
combined manuscript of 1 March 2004.
-/

public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
open Subgroup Stellmacher
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z t : G} {L : Subgroup G}
namespace TailFamily

omit [Finite G] in
theorem R_candidate_commute (d : Prepared T z t L) (a : ActionData d) :
    a.R ≤ centralizer (zpowers a.w : Set G) :=
  le_centralizer_iff.mpr (zpowers_le.mpr (a.centralizes_R d))

omit [Finite G] in
theorem candidate_elementary (d : Prepared T z t L) (a : ActionData d) :
    IsElementaryAbelian 2 (zpowers a.w) :=
  IsElementaryAbelian.zpowers_of_pow_eq_one
    (by simpa only [a.involution] using pow_orderOf_eq_one a.w)

theorem product_maxFamily (d : Prepared T z t L) (a : ActionData d) (E : Subgroup G) :
    E ∈ elementaryAbelianMaxSubgroups (a.R ⊔ zpowers a.w) ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups a.R, E = B ⊔ zpowers a.w := by
  rw [maxFamily_sup_iff_of_disjoint_of_commuting _ _
    ((candidate_disjoint d a).mono_left a.R_le) (R_candidate_commute d a) E]
  have hW : zpowers a.w ∈ elementaryAbelianMaxSubgroups (zpowers a.w) :=
    ⟨le_rfl, candidate_elementary d a, fun F hF _ => card_le_of_le hF⟩
  constructor
  · rintro ⟨B, hB, C, hC, hE⟩
    have hCW : C = zpowers a.w := eq_of_le_of_card_ge hC.1
      (hC.2.2 _ le_rfl (candidate_elementary d a))
    exact ⟨B, hB, hCW ▸ hE⟩
  · rintro ⟨B, hB, hE⟩
    exact ⟨B, hB, _, hW, hE⟩

theorem product_maxJ (d : Prepared T z t L) (a : ActionData d) :
    elementaryAbelianMaxJ (a.R ⊔ zpowers a.w) = a.R ⊔ zpowers a.w := by
  obtain ⟨n, hn, ⟨e⟩⟩ := a.dihedral
  have hW : elementaryAbelianMaxJ (zpowers a.w) = zpowers a.w := by
    apply le_antisymm (sSup_le fun E hE => hE.1)
    exact le_sSup ⟨le_rfl, candidate_elementary d a, fun F hF _ => card_le_of_le hF⟩
  rw [elementaryAbelianMaxJ_sup_of_disjoint_of_commuting _ _
    ((candidate_disjoint d a).mono_left a.R_le) (R_candidate_commute d a),
    dihedral_maxJ a.R hn e, hW]

theorem maxFamily_card_ge_eight (d : Prepared T z t L) (a : ActionData d)
    {E : Subgroup G} (hE : E ∈ elementaryAbelianMaxSubgroups
      (commutingSylow T L ⊔ zpowers a.w)) : 8 ≤ Nat.card E := by
  obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty a.R
  obtain ⟨n, hn, ⟨e⟩⟩ := a.dihedral
  have hcB := ((dihedral_maxFamily_iff a.R hn e B).mp hB).2.2
  have hBW := (product_maxFamily d a (B ⊔ zpowers a.w)).mpr ⟨B, hB, rfl⟩
  have hc : Nat.card (B ⊔ zpowers a.w : Subgroup G) = 8 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((le_centralizer_iff.mp (hB.1.trans (R_candidate_commute d a))).trans
        (Subgroup.centralizer_le_normalizer _))
      ((candidate_disjoint d a).mono_left (hB.1.trans a.R_le)),
      hcB, Nat.card_zpowers, a.involution]
  exact hc ▸ hE.2.2 _ (hBW.1.trans (sup_le_sup_right a.R_le _)) hBW.2.1

/-- In the faithful alternative the rotation extension has index two in the tail. -/
theorem rotation_extension_index (d : Prepared T z t L) (a : ActionData d) :
    (zpowers a.y ⊔ zpowers a.w).relIndex (commutingSylow T L ⊔ zpowers a.w) = 2 := by
  have hC : Nat.card (commutingSylow T L) = Nat.card (zpowers a.y) * 2 := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup G) (zpowers a.y)
      (commutingSylow T L) bot_le a.rotation_le
    simpa only [relIndex_bot_left, a.rotation_index] using h.symm
  have hQ : Nat.card (commutingSylow T L ⊔ zpowers a.w : Subgroup G) =
      Nat.card (commutingSylow T L) * 2 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((zpowers_le.mpr (candidate_mem_and_centralizes d a.candidate).1).trans
        (sylow_normalizes_commutingSylow d)) (candidate_disjoint d a),
      Nat.card_zpowers, a.involution]
  have hD : Nat.card (zpowers a.y ⊔ zpowers a.w : Subgroup G) =
      Nat.card (zpowers a.y) * 2 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((zpowers_le.mpr (candidate_mem_and_centralizes d a.candidate).1).trans
        (rotation_normalized d a)) ((candidate_disjoint d a).mono_left a.rotation_le),
      Nat.card_zpowers a.w, a.involution]
  have h := relIndex_mul_relIndex (⊥ : Subgroup G) (zpowers a.y ⊔ zpowers a.w)
    (commutingSylow T L ⊔ zpowers a.w) bot_le (sup_le_sup_right a.rotation_le _)
  rw [relIndex_bot_left, relIndex_bot_left, hQ, hC, hD] at h
  have hp := Nat.card_pos (α := zpowers a.y)
  nlinarith

/-- An elementary subgroup of the tail with order at least eight must contain
w in the faithful alternative. The intersection with the index-two rotation
extension is the whole four-group generated by z and w. -/
theorem faithful_large_contains_candidate (d : Prepared T z t L) (a : ActionData d)
    (hlarge : 4 < orderOf a.y) (hy : a.w⁻¹ * a.y * a.w = a.y * z)
    (E : Subgroup G) (hEQ : E ≤ commutingSylow T L ⊔ zpowers a.w)
    (hE : IsElementaryAbelian 2 E) (hcard : 8 ≤ Nat.card E) : a.w ∈ E := by
  let := hE
  let D := zpowers a.y ⊔ zpowers a.w
  let I := E ⊓ D
  let W := zpowers z ⊔ zpowers a.w
  have hIW : I ≤ W := by
    intro x hx
    exact faithful_rotation_extension_involutions d a hlarge hy hx.2
      (elemPow_eq_one_of_isElementaryAbelian x hx.1)
  have hi : D.relIndex E ≤ 2 := by
    have hidx : D.relIndex (commutingSylow T L ⊔ zpowers a.w) = 2 :=
      rotation_extension_index d a
    exact hidx ▸ relIndex_le_of_le_right hEQ (by rw [hidx]; decide)
  have hcI : 4 ≤ Nat.card I := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup G) I E bot_le inf_le_left
    rw [relIndex_bot_left, relIndex_bot_left] at hm
    have hIe : I.relIndex E = D.relIndex E := inf_relIndex_left _ _
    rw [hIe] at hm
    nlinarith
  have hcW : Nat.card W = 4 := by
    have hzC := a.rotation_le (faithful_z_rotation d a hy)
    have hzR : z ∈ a.R := by
      have hzA : z ∈ ambientCenter a.R := by
        rw [a.center_eq]
        exact mem_zpowers z
      exact (map_subtype_le (center a.R)) hzA
    have hwz : a.w ∈ centralizer (zpowers z : Set G) := by
      exact centralizer_le (zpowers_le.mpr hzR) (a.centralizes_R d)
    change Nat.card (zpowers z ⊔ zpowers a.w : Subgroup G) = 4
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((zpowers_le.mpr hwz).trans (Subgroup.centralizer_le_normalizer _))
      ((candidate_disjoint d a).mono_left (zpowers_le.mpr hzC)),
      Nat.card_zpowers, Nat.card_zpowers, d.counterexample.localSetup.involution, a.involution]
  have hWI : I = W := eq_of_le_of_card_ge hIW (hcW ▸ hcI)
  have hwI : a.w ∈ I := hWI.symm ▸ mem_sup_right (mem_zpowers a.w)
  exact hwI.1

/-- Every maximum tail subgroup belongs to the dihedral product in the
faithful alternative; elementary subgroups outside it have order less than eight. -/
theorem faithful_large_le (d : Prepared T z t L) (a : ActionData d)
    (hlarge : 4 < orderOf a.y) (hy : a.w⁻¹ * a.y * a.w = a.y * z)
    (hR : a.R = zpowers (a.y ^ 2) ⊔ zpowers t)
    (E : Subgroup G) (hEQ : E ≤ commutingSylow T L ⊔ zpowers a.w)
    (hE : IsElementaryAbelian 2 E) (hcard : 8 ≤ Nat.card E) :
    E ≤ a.R ⊔ zpowers a.w := by
  let := hE
  have hw := faithful_large_contains_candidate d a hlarge hy E hEQ hE hcard
  intro x hx
  exact faithful_centralizer_le d a hy hR
    ⟨hEQ hx, mem_centralizer_singleton_iff.mpr (E.le_centralizer hx a.w hw).symm⟩

end TailFamily
end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
