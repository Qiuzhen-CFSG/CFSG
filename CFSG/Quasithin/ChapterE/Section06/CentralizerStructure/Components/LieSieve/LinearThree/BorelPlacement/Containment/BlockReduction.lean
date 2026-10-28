module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts
public import Theory.AtlasPort.LinearGroups.SL2Order

/-!
# Solvable E.6.7 decompositions

A solvable short group has core quotient of order three: the quasisimple
alternative would give a nontrivial perfect solvable group. The actual
quotient models therefore exclude the L₂-even and A₅ types. Thus only A₃
blocks can occur in a solvable E.6.7 decomposition. Excluding these relatively
subnormal blocks forces the whole intermediate subgroup into M.

This is a conditional reduction of the Borel step of Aschbacher–Smith E.6.8,
printed p.248. It does not assert the remaining intrinsic A₃ exclusion, and
uses no claim about the rank of an A₃-block Sylow-center quotient.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
variable {J : Type*} [Group J] [Group.IsSolvable J]

theorem short_quotient_card_three (h : ChapterC.IsShort J) :
    Nat.card (J ⧸ pCore 2 J) = 3 := by
  rcases h.quotient with hq | hc
  · let := hq
    let : IsSimpleGroup ((J ⧸ pCore 2 J) ⧸ center (J ⧸ pCore 2 J)) := IsQuasisimple.simple
    let : Nontrivial (J ⧸ pCore 2 J) :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center (J ⧸ pCore 2 J)))
    exact (Group.IsPerfect.not_isSolvable (J ⧸ pCore 2 J) inferInstance).elim
  · exact hc

theorem alternatingThree_of_solvable_chiZero (h : ChapterC.IsChiZeroBlock J) :
    ChapterC.IsAlternatingBlock J 3 := by
  have hc := short_quotient_card_three h.chi.short
  rcases h with ⟨n, hn, hshort, F, hfield, hfinite, hF, _, hm⟩ | h3 | h5
  · let := hfield
    let := hfinite
    obtain ⟨e⟩ := hm.quotient_iso
    have he := Nat.card_congr e.toEquiv
    rw [hc, Atlas.card_sl_two, hF] at he
    have hfour : 4 ≤ 2 ^ n := by
      have := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (show 2 ≤ n by omega)
      exact this
    have hp : 1 ≤ (2 ^ n) ^ 2 - 1 := by nlinarith
    have hh := Nat.mul_le_mul_left (2 ^ n) hp
    omega
  · exact h3
  · obtain ⟨e⟩ := h5.2.2.quotient_iso
    have he := Nat.card_congr e.toEquiv
    rw [hc, nat_card_alternatingGroup] at he
    norm_num at he
end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
variable {G : Type*} [Group G] {Q M V U H : Subgroup G}

/-- The solvable E.6.7 case reduces precisely to exclusion of A₃ blocks. -/
theorem le_of_solvable_decomposition_no_alternatingThree
    (d : InvariantSubspaces.BlockSelection.E67Decomposition Q M V U H)
    (hs : Group.IsSolvable H)
    (hno : ∀ B : Subgroup G, B ≤ H → (B.subgroupOf H).IsSubnormal →
      ¬ ChapterC.IsAlternatingBlock B 3) : H ≤ M := by
  have hempty (i : Fin d.count) : False := by
    let := hs
    let : Group.IsSolvable (d.block i) := Group.isSolvable_of_isSolvable_injective
      (f := inclusion (d.le i)) (inclusion_injective (d.le i))
    exact hno (d.block i) (d.le i) (d.subnormal i)
      (alternatingThree_of_solvable_chiZero (d.type i))
  rw [d.generated]
  exact sup_le inf_le_right (iSup_le fun i => (hempty i).elim)
end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
