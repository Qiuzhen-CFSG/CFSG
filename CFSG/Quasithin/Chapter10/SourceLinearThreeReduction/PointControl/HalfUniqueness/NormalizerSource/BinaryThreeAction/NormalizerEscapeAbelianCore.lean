module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.HalfUniqueness.NormalizerSource.BinaryThreeAction.NormalizerEscapeMovedCenter
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The original natural factor excludes the abelian core of order sixteen

The genuine MS input leaves abelian full cores of orders eight, sixteen
or sixty-four. The original selected natural factor has order eight and
is invariant under the original component. In a core of order sixteen
its quotient would have order two and hence trivial component action,
contrary to full movement of the core. A core of order eight is exactly
the original factor. The sixty-four-element branch remains separate.
Source: Aschbacher--Smith 10.2.5 and C.1.34, pp.748 and136--137.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
open Chapter3.Section02 ChapterC.BinaryMS
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- On the original normalizer-escape source, an abelian full MS core is
the original selected natural factor or has order sixty-four. -/
theorem normalizerEscape_abelian_core_eq_or_card
    (s : NaturalData D)
    (hout : ¬ normalizer ((T : Subgroup G) ⊓ normalizer (L : Set G) : Set G) ≤
      D.maximalLocal)
    (hc : IsMulCommutative (commutatorCore
      (L.subgroupOf (L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G)))))) :
    let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
    let C := (commutatorCore (L.subgroupOf J)).map J.subtype
    C = ⁅D.fullModule,L⁆ ∨ Nat.card C = 64 := by
  let J := L ⊔ ((T : Subgroup G) ⊓ normalizer (L : Set G))
  let A := L.subgroupOf J
  let C := (commutatorCore A).map J.subtype
  let W := ⁅D.fullModule,L⁆
  let h := normalizerEscapeBinaryInput D (selected_nonnormal s) hout s.quotient
  change C = W ∨ Nat.card C = 64
  have hWC : W ≤ C :=
    (normalizerEscape_moved_le_core_center D (selected_nonnormal s) hout s.quotient).trans
      (map_mono (map_subtype_le _))
  have hWcard : Nat.card W = 8 := moved_card s s.fixed_zero
  have hmove : ⁅C,L⁆ = C := by
    have hh := congrArg (map J.subtype) h.commutatorCore_idempotent
    change (⁅commutatorCore A,A⁆).map J.subtype = C at hh
    rw [map_commutator] at hh
    have hA : A.map J.subtype = L := map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left)
    rw [hA] at hh
    exact hh
  have hnot : Nat.card C ≠ 16 := by
    intro hCcard
    have hindex : W.relIndex C = 2 := by
      have hh := relIndex_mul_relIndex (⊥ : Subgroup G) W C bot_le hWC
      rw [relIndex_bot_left,relIndex_bot_left,hWcard,hCcard] at hh
      omega
    have hCW : C ≤ W := by
      rw [←hmove]
      exact commutator_le_of_normalized_index_two C W L hWC hindex
        (le_normalizer_iff_commutator_le_left.mpr hmove.le)
        (normalizer_commutator_ge_right _ _)
    have hh := congrArg (fun U : Subgroup G => Nat.card U) (le_antisymm hCW hWC)
    rw [hCcard,hWcard] at hh
    omega
  obtain ⟨d,hd,⟨e⟩⟩ := h.abelianCore_model hc
  have hcard : Nat.card C = 2 ^ d := by
    rw [card_map_of_injective J.subtype_injective,Nat.card_congr e.toEquiv]
    change Nat.card (Fin d → ZMod 2) = 2 ^ d
    simp only [Nat.card_fun,Nat.card_fin,Nat.card_zmod]
  rcases hd with rfl | rfl | rfl
  · left
    exact (eq_of_le_of_card_ge hWC (by rw [hWcard,hcard]; decide)).symm
  · exact (hnot (by simpa using hcard)).elim
  · right
    simpa using hcard

end CFSG.Quasithin.Chapter10.PointControl.HalfUniqueness.BinaryThreeAction
