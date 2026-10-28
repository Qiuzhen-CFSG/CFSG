module
public import Theory.SpecificGroups.OrthogonalFourBinary.SylowGeometry.PointGeometry
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.ElementaryAbelian.Injective

/-!
# Small two-subgroups without a four-group

Every Sylow two-subgroup of the concrete O₄⁺(2) fixes a singular point.
Its intersection with the actual Ω-subgroup is an elementary four-group;
the finite coordinate count supplies its order. Consequently a two-subgroup
containing no elementary four-group has order at most four.

Source application: Aschbacher–Smith 15.1.2(5), printed p.1086.
-/

public section
open Subgroup
namespace OrthogonalFourBinary.SylowGeometry
open TerminalLines
set_option synthInstance.maxSize 10000

private theorem point_omega_count : ∀ x : Space, x ≠ 0 → q x = 0 →
    Fintype.card {k : Code // eval k x = x ∧ k.1.2 = k.2.1.2} = 4 := by
  decide +kernel

theorem point_omega_card (x : Space) (hx : x ≠ 0) (hq : form x = 0) :
    Nat.card (MulAction.stabilizer Actor x ⊓ omega : Subgroup Actor) = 4 := by
  let e : {k : Code // eval k x = x ∧ k.1.2 = k.2.1.2} ≃
      (MulAction.stabilizer Actor x ⊓ omega : Subgroup Actor) :=
    codeEquiv.subtypeEquiv (fun k => by
      change (eval k x = x ∧ _) ↔ (candidate k x = x ∧ codeMap k ∈ omega)
      rw [candidate_eval, codeMap_mem_omega])
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact point_omega_count x hx hq

theorem sylow_contains_elementary_four (S : Sylow 2 Actor) :
    ∃ A : Subgroup Actor, A ≤ S ∧ IsElementaryAbelian 2 A ∧ Nat.card A = 4 := by
  obtain ⟨x,hx,hq,hs⟩ := sylow_eq_point_stabilizer S
  let A : Subgroup Actor := MulAction.stabilizer Actor x ⊓ omega
  have ha : Nat.card A = 4 := point_omega_card x hx hq
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour A := ⟨ha,(Monoid.exponent_eq_prime_iff Nat.prime_two).mpr (fun (a : A) hne =>
    orderOf_eq_prime (Subtype.ext (point_omega_square x hx hq a a.property)) hne)⟩
  refine ⟨A,hs ▸ inf_le_left,?_,ha⟩
  exact { toIsMulCommutative := IsKleinFour.isMulCommutative
          exponent_dvd_p := by simp }

theorem two_subgroup_no_four_card_le_four (L : Subgroup Actor) (hL : IsPGroup 2 L)
    (hno : ∀ A : Subgroup L, IsElementaryAbelian 2 A → Nat.card A ≠ 4) :
    Nat.card L ≤ 4 := by
  obtain ⟨S,hLS⟩ := hL.exists_le_sylow
  have hS : Nat.card S = 8 := by
    obtain ⟨x,hx,hq,hs⟩ := sylow_eq_point_stabilizer S
    simpa only [hs] using IndexTwoNormalizer.singular_stabilizer_card x hx hq
  have hd : Nat.card L ∣ 8 := hS ▸ card_dvd_of_le hLS
  by_contra! hn
  have hc : Nat.card L = 8 := by
    have hh2 : Nat.card L ≤ 8 := Nat.le_of_dvd (by decide) hd
    interval_cases h : Nat.card L
    all_goals first | rfl | norm_num at hd
  have he : L = S := eq_of_le_of_card_ge hLS (by rw [hc,hS])
  obtain ⟨A,hAS,hA,hAc⟩ := sylow_contains_elementary_four S
  let B := A.subgroupOf L
  let : IsElementaryAbelian 2 A := hA
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe (show A ≤ L from he.symm ▸ hAS)).toMonoidHom
    (subgroupOfEquivOfLe _).injective
  apply hno B inferInstance
  exact (Nat.card_congr (subgroupOfEquivOfLe (he.symm ▸ hAS)).toEquiv).trans hAc

end OrthogonalFourBinary.SylowGeometry
