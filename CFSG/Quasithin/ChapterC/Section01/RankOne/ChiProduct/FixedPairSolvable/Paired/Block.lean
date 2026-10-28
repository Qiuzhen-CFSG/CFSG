module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Paired.Canonical
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Solvable
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Solvable.Source.Transport
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicMovement

/-!
# Fixed-pair block extraction on the canonical conjugate span

The same original universal pair applies to N=⟨Baum(T)^L⟩. Its escaping
residual is subnormal in the original group by the canonical normalizer
argument. Thus the intrinsic block is an actual ambient block even though
N need not contain the full original Sylow subgroup. Solvability makes it
an A₃ block. Original Thompson movement on the original module commutator
then gives exact movement and support.

The factor geometry must still prove local-class membership and movement;
neither is assumed to descend to arbitrary cubic-line preimages.
Source: Aschbacher--Smith C.1.26--28, printed pp.132--134.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Paired
open ChapterB GlaubermanNiles
universe u
variable {G : Type u} [Group G] [Finite G]

theorem canonical_alternatingThree_of_fixed_pair_escape [Group.IsSolvable G]
    (T : Sylow 2 G) (L : Subgroup G)
    (hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) (hL : L.IsSubnormal)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hlocal : InLocalClass (inclusion (le_conjugateSpanBy (baumann (T : Subgroup G)) L)))
    (hout : ¬ conjugateSpanBy (baumann (T : Subgroup G)) L ≤ control T D) :
    let N := conjugateSpanBy (baumann (T : Subgroup G)) L
    let K := (pResidual 2 N).map N.subtype
    IsBlock K ∧ IsAlternatingBlock K 3 := by
  let N := conjugateSpanBy (baumann (T : Subgroup G)) L
  let K := (pResidual 2 N).map N.subtype
  have hb : BlockAlternative N := by
    apply FixedPair.fixed_pair_block_of_escape T D hD ⊤ N le_top (le_conjugateSpanBy _ _) hlocal
    simpa only [control,top_inf_eq] using hout
  let e : pResidual 2 N ≃* K := (pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective
  have ha : IsAlternatingBlock K 3 := by
    rcases hb.2 with ⟨n,hn⟩ | ha
    · exact hn.not_solvable.elim
    · exact RankOne.Solvable.isAlternatingBlock_of_equiv e ha
  exact ⟨⟨inferInstance,ha.2.1,canonical_residual_subnormal T L hBL hL⟩,ha⟩

/-- Literal original-Sylow movement and original-module support of the same block. -/
theorem canonical_moving_alternatingThree_of_fixed_pair_escape [Group.IsSolvable G]
    (T : Sylow 2 G) (L : Subgroup G)
    (hBL : baumann (T : Subgroup G) ≤ normalizer (L : Set G)) (hL : L.IsSubnormal)
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hlocal : InLocalClass (inclusion (le_conjugateSpanBy (baumann (T : Subgroup G)) L)))
    (hout : ¬ conjugateSpanBy (baumann (T : Subgroup G)) L ≤ control T D)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hmove : let N := conjugateSpanBy (baumann (T : Subgroup G)) L
      let K := (pResidual 2 N).map N.subtype
      ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer ((⁅U,K⁆ : Subgroup G) : Set G)) :
    let N := conjugateSpanBy (baumann (T : Subgroup G)) L
    let K := (pResidual 2 N).map N.subtype
    IsBlock K ∧ IsAlternatingBlock K 3 ∧
      K = ⁅K,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU K).map K.subtype = ⁅U,K⁆ ∧ ⁅U,K⁆ ≠ ⊥ := by
  let N := conjugateSpanBy (baumann (T : Subgroup G)) L
  let K := (pResidual 2 N).map N.subtype
  obtain ⟨hb,ha⟩ := canonical_alternatingThree_of_fixed_pair_escape T L hBL hL D hD hlocal hout
  have hne : ⁅U,K⁆ ≠ ⊥ := by
    intro he
    apply hmove
    rw [he]
    intro j _ x hx
    rw [mem_bot.mp hx]
    simp
  have hu := SelectedRankOne.blockU_eq_nontrivial_normal_module_commutator K U hb hne
  have hJnorm : elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (elementaryAbelianMaxJ_le_baumann _).trans
      (le_sup_right.trans (embedded_residual_conjugateSpanBy_normalized (p := 2) _ L))
  have hcard : Nat.card (K ⧸ pCore 2 K) = 3 := by
    obtain ⟨a⟩ := ha.2.2.quotient_iso
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  refine ⟨hb,ha,hb.eq_commutator_of_cubic_movement hcard
    (T.isPGroup'.to_le (sSup_le fun _ hA => hA.1)) hJnorm ?_,hu,hne⟩
  rwa [hu]
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairSolvable.Paired
