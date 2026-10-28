module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.RankOnePlane.UnitaryExclusion.ModelCore.Coordinates
public import Theory.SpecificGroups.SU3.EvenFourCore.SylowStructure
public import Theory.ElementaryAbelian.Quotient

/-!
# Central quotient structure of a marked PSU₃(4) Sylow subgroup

The genuine model, basis change and Sylow conjugation identify the specified
Sylow subgroup with the actual projective Hermitian root range. Transporting
the root calculation through that equivalence gives its elementary central
quotient of order sixteen and the identity P′ = Z(P). The quotient transport
uses the full intrinsic centers of these two groups.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the unitary
inference in 15.3.40, printed p.1138; Huppert II.10.12 for the root structure.
This supplies the structural premise in `fiveCoreControl_of_sylow_action`;
the normalizer's five-action is an independent input to that assembly.
-/

public section

open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.External

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
open CFSG.Quasithin.ChapterF.Source.Unitary

/-- Every marked Sylow two-subgroup of a genuine PSU₃(4) model has central
quotient E₁₆ and derived subgroup equal to its center. -/
theorem unitary_four_sylow_structure
    {H : Type*} [Group H] [Finite H] (hm : ClassicalGroup.IsPSU H 3 4)
    (P : Sylow 2 H) :
    IsElementaryAbelian 2 (P ⧸ center P) ∧
      Nat.card (P ⧸ center P) = 16 ∧ _root_.commutator P = center P := by
  obtain ⟨F, _, _, J, hJ, hcard, hconj, e, he⟩ := unitary_four_sylow_coordinates hm P
  let : CharP F 2 := charP_two 2 (by decide) hcard
  have hfixed : Nat.card {x : F // J.conj x = x} = 4 :=
    fixed_card J 2 (by decide) hcard hconj
  let R := (hermitianUnipotentPSU J hJ).range
  let ep : P ≃* R :=
    ((P : Subgroup H).equivMapOfInjective e.toMonoidHom e.injective).trans
      (MulEquiv.subgroupCongr he)
  obtain ⟨hel, hquot, hcomm⟩ := SU3.EvenFourCore.four_root_structure J hJ hcard hfixed
  let : IsElementaryAbelian 2 (R ⧸ center R) := hel
  have hZ : (center R).map ep.symm.toMonoidHom = center P := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (centerCongr ep.symm ⟨y, hy⟩).property
    · intro hx
      exact ⟨ep x, (centerCongr ep ⟨x, hx⟩).property, ep.symm_apply_apply x⟩
  let eq := QuotientGroup.congr (center R) (center P) ep.symm hZ
  refine ⟨IsElementaryAbelian.of_surjective eq.toMonoidHom eq.surjective,
    (Nat.card_congr eq.symm.toEquiv).trans hquot, ?_⟩
  have hd := congrArg (fun N : Subgroup R => N.map ep.symm.toMonoidHom) hcomm
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr ep.symm.surjective] at hd
  exact hd.trans hZ

end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane.UnitaryExclusion
