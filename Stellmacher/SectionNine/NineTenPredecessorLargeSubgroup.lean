module

public import Stellmacher.SectionNine.NineTenPredecessorTerminalTransfer
public import Stellmacher.SectionNine.NineTenGeneratingCriticalPair
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Theory.GroupAction.FixedCommutatorLargeSubgroup

/-!
# The actual large predecessor subgroup for (9.4)

Assume the actual predecessor centralizes the penultimate center and has
its commutator with the retained terminal neighbor center inside R joined
with the terminal center. If R lies in both terminal V and first V, then for
the supplied actor in that neighbor center there is a subgroup of at least
half the predecessor order whose cyclic-actor commutator lies in first V.

The initial neighborhood is abelian, so the predecessor centralizes R.
Its assumed penultimate-center commutation makes it centralize the terminal
center, which has order two. The predecessor acts on the elementary terminal
module by the proved stabilizer transfer. Apply the fixed-displacement kernel
construction to the same supplied actor. Its half-order bound is exactly
what the strengthened (9.7) intersection obstruction needs.

This is the coatom step in Stellmacher (9.10), printed p.57, in the sufficient
index-at-most-two form. It includes a trivial displacement without selecting
an arbitrary coatom. No new extraction, normalization or actor is chosen;
the actual (9.4) hypotheses still have to be assembled separately.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_predecessor_large_subgroup
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (predecessor neighbor : ctx.Γ.Vertex)
    (hpredecessor : ctx.Γ.adjacent ctx.criticalPath.a predecessor)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hmodules : ⁅VAt ctx.Γ predecessor,
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ = ⊥)
    (R : Subgroup G) (hRU : R ≤ VAt ctx.Γ ctx.criticalPath.a')
    (hRfirst : R ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hbound : ⁅VAt ctx.Γ predecessor, ZAt ctx.Γ neighbor⁆ ≤ R ⊔ ZAt ctx.Γ ctx.criticalPath.a')
    (actor : G) (hactor : actor ∈ ZAt ctx.Γ neighbor) :
    ∃ A0 : Subgroup G, A0 ≤ VAt ctx.Γ predecessor ∧
      Nat.card (VAt ctx.Γ predecessor) ≤ 2 * Nat.card A0 ∧
      ⁅A0, Subgroup.zpowers actor⁆ ≤ VAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let K := VAt Γ predecessor
  let U := VAt Γ cp.a'
  let Z := ZAt Γ cp.a'
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let initialJoin := GeneratedNeighborhoodV Γ cp.a
  have hshort : 1 < cp.length := by change 4 < cp.length at hb; omega
  have hKP : K ≤ GAt Γ cp.a' := nine_ten_predecessor_le_terminal_of_centralizing ctx hb
    predecessor hpredecessor hmodules
  have hKU : K ≤ Subgroup.normalizer (U : Set G) :=
    hKP.trans (stabilizer_le_normalizer_v Γ cp.a')
  have hWabelian : IsMulCommutative initialJoin :=
    nine_eight_neighborhood_abelian ctx.toLocalContext hb cp.a
  have hWcentral : initialJoin ≤ Subgroup.centralizer (initialJoin : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hWabelian
  have hKW : K ≤ initialJoin := nine_eight_v_le_generated_neighborhood Γ
    ((mem_neighborhood_iff_adjacent Γ).mpr hpredecessor)
  have hfirstW : VAt Γ cp.firstStep ≤ initialJoin :=
    nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj)
  have hKR : K ≤ Subgroup.centralizer (R : Set G) :=
    hKW.trans (hWcentral.trans (Subgroup.centralizer_le (hRfirst.trans hfirstW)))
  obtain ⟨alignment, hpenultimate, hterminal⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpen := (nine_three_initial_extraction_inputs ctx.toLocalContext hshort).1
  change penultimate ∈ neighborhood Γ cp.a' at hpen
  have hterminalNeighbor : cp.a' ∈ neighborhood Γ penultimate :=
    (mem_neighborhood_iff_adjacent Γ).mpr
      (Γ.adjacent_symm ((mem_neighborhood_iff_adjacent Γ).mp hpen))
  have hZpen : Z ≤ ZAt Γ penultimate :=
    ((nine_seven_center_join ctx penultimate ⟨alignment, hpenultimate⟩).2
      cp.a' hterminalNeighbor).2
  have hpenU : ZAt Γ penultimate ≤ U := by
    change ZAt Γ penultimate ≤ VAt Γ cp.a'
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨penultimate, hpen, rfl⟩
  have hZU : Z ≤ U := hZpen.trans hpenU
  have hKZ : K ≤ Subgroup.centralizer (Z : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmodules).trans
      (Subgroup.centralizer_le hZpen)
  have hfixed : K ≤ Subgroup.centralizer ((R ⊔ Z : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr (sup_le
      (Subgroup.le_centralizer_iff.mp hKR) (Subgroup.le_centralizer_iff.mp hKZ))
  have hfour := (lemma_nine_three_ambient ctx hshort cp.a ⟨1, Γ.act_one _⟩).2
  have hZcard : Nat.card Z = 2 :=
    (nine_next_center_and_commutator_of_initial_four ctx.toLocalContext hfour
      cp.a' ⟨alignment, hterminal⟩).1
  let _ : IsElementaryAbelian 2 U :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hshort).2.2.1
  have hneighborU : ZAt Γ neighbor ≤ U := by
    change ZAt Γ neighbor ≤ VAt Γ cp.a'
    rw [VAt, v, Γ.vAt_def]
    exact le_sSup ⟨neighbor, hneighbor, rfl⟩
  have hactorPow : actor ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian actor (hneighborU hactor)
  have hactorBound : ⁅K, Subgroup.zpowers actor⁆ ≤ R ⊔ Z :=
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hactor)).trans hbound
  obtain ⟨A0, hAK, hcard, hcomm⟩ :=
    Subgroup.exists_large_subgroup_commutator_le_of_central_bound K U R Z hKU hRU hZU
      hZcard hfixed actor (hneighborU hactor) hactorPow hactorBound
  exact ⟨A0, hAK, hcard, hcomm.trans hRfirst⟩

end Stellmacher.SectionNine
