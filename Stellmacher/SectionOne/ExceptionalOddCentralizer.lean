module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Defs
public import Theory.GroupAction.OddCommutingFixedLine
public import Theory.GroupAction.NormalizingActor
public import Theory.GroupTheory.SubgroupConjugation

/-!
# The odd Sylow centralizer in the exceptional action

Suppose `S` is a two-group and both `S` and `C_W(S)` normalize a subgroup
`F`. If `U=[V,F]` has exactly two `S`-fixed elements and `C_W(U)=1`,
then `C_W(S)=1`.

Restrict the action to `S C_W(S)` on `U`, using its canonical invariance
proof. The two actors commute, and the odd actor fixes the fixed subgroup
of order two. The `P × Q` lemma makes its whole action trivial, and the
given odd-core action kernel then eliminates it. Fixed points and actor
subgroups are transported explicitly through the same restricted action.

This supplies a needed transfer before making the whole odd core act on
the exceptional module in Stellmacher (1.6), journal p.18;
see `refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionOne

universe u

public theorem oddCore_centralizer_eq_bot_of_fixed_card_two
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S F : Subgroup G) (hS : IsPGroup 2 S)
    (hnorm : S ⊔ (oddCore G ⊓ Subgroup.centralizer (S : Set G)) ≤
      Subgroup.normalizer (F : Set G))
    (hfixed : Nat.card (commutatorAction F V ⊓ FixedPoints.subgroup S V : Subgroup V) = 2)
    (hkernel : oddCore G ⊓ fixingSubgroup G (commutatorAction F V : Set V) = ⊥) :
    oddCore G ⊓ Subgroup.centralizer (S : Set G) = ⊥ := by
  let C := oddCore G ⊓ Subgroup.centralizer (S : Set G)
  let H := S ⊔ C
  let U := commutatorAction F V
  let P := S.subgroupOf H
  let Q := C.subgroupOf H
  let _ : IsInvariant H V U := commutatorAction_isInvariant_of_normalizing_actor H F hnorm
  let _ : IsElementaryAbelian 2 U := RankOneThreeGroupAssembly.isElementaryAbelian_subgroup U
  have hSp : IsPGroup 2 P := hS.of_equiv
    (Subgroup.subgroupOfEquivOfLe (show S ≤ H from le_sup_left)).symm
  have hCodd : Nat.Coprime 2 (Nat.card C) :=
    (pPrimeCore_coprime_card (G := G) (p := 2)).of_dvd_right
      (Subgroup.card_dvd_of_le (show C ≤ oddCore G from inf_le_left))
  have hQodd : Nat.Coprime 2 (Nat.card Q) := by
    have hc : Nat.card Q = Nat.card C := Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show C ≤ H from le_sup_right)).toEquiv
    rw [hc]
    exact hCodd
  have hSC : ⁅S, C⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr inf_le_right
  have hPQ : ⁅P, Q⁆ = ⊥ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_bot, commutator_subgroupOf_map_eq H C S le_sup_right le_sup_left]
    exact hSC
  have hPfixed : Nat.card (FixedPoints.subgroup P U) = 2 := by
    let e : FixedPoints.subgroup P U ≃ ↥(U ⊓ FixedPoints.subgroup S V : Subgroup V) :=
      { toFun := fun x => ⟨((x : U) : V), ⟨(x : U).property, by
          intro s
          have hp := x.property (⟨⟨s, (le_sup_left : S ≤ H) s.property⟩, s.property⟩ : P)
          exact congrArg Subtype.val hp⟩⟩
        invFun := fun x => ⟨⟨x, x.property.1⟩, by
          intro p
          apply Subtype.ext
          exact x.property.2 ⟨p, p.property⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro x; rfl }
    exact (Nat.card_congr e).trans hfixed
  have hQfix : Q ≤ fixingSubgroup H (Set.univ : Set U) :=
    odd_commuting_subgroup_fixes_all_of_fixed_card_two P Q hSp hQodd hPQ hPfixed
  apply le_antisymm _ bot_le
  intro c hc
  have hcU : c ∈ fixingSubgroup G (U : Set V) := by
    rw [mem_fixingSubgroup_iff]
    intro v hv
    have hcin : (⟨c, (le_sup_right : C ≤ H) hc⟩ : H) ∈ Q := hc
    have hvfix := (mem_fixingSubgroup_iff (M := H) (s := (Set.univ : Set U))).mp
      (hQfix hcin) (⟨v, hv⟩ : U) (Set.mem_univ _)
    exact congrArg Subtype.val hvfix
  have hcW : c ∈ oddCore G := hc.1
  have hcKer : c ∈ oddCore G ⊓ fixingSubgroup G (U : Set V) := ⟨hcW, hcU⟩
  rw [hkernel] at hcKer
  exact hcKer

end Stellmacher.SectionOne

