module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBlockExclusion
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ResidualCore
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The whole left two-core is the intrinsic block layer

In the surviving left-block case, squares in the ambient two-core
centralize the block. The trivial Sylow fixed subgroup makes that core
elementary. Characteristic two makes it self-centralizing, hence reduced,
so the original universal Input may be reselected on this entire core.

The original escaping cubic then has no nontrivial fixed point on the core.
Coprime decomposition makes the core fully moved by the cubic. The block
commutator theorem identifies it with the intrinsic U-layer. This removes
the extra-core ambiguity in the degree-two order bound; that bound and
the remaining left-block exclusion still require proof.

Source: Aschbacher–Smith C.1.11–13 and 5.1.13, printed pp.124–125,638,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
/-- The full ambient left core is an admissible reduced module under the original Input. -/
theorem LocalA7Configuration.left_core_input
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    Input KnownSimple.IsKnownSimple T L ((L ⊔ (T : Subgroup G)).pCoreIn 2) n := by
  let M := L ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let R := L.subgroupOf M
  let Q := pCore 2 M
  have hb : ChapterC.IsBlock R := (a.left_block h hH hgen c d).1
  have hres : pResidual 2 M = R := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left)]
    exact h.local_residual_eq
  have hQP : Q ≤ (P : Subgroup M) := pCore_isPGroup.le_sylow_of_normal P
  have hfix : Q ⊓ centralizer (pResidual 2 M : Set M) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh : x.val ∈ (T : Subgroup G) ⊓ centralizer (L : Set G) := by
      refine ⟨hQP hx.1,?_⟩
      intro l hl
      exact congrArg M.subtype (hx.2 (⟨l,(show L ≤ M from le_sup_left) hl⟩ : M) (hres.symm ▸ hl))
    exact Subtype.ext (mem_bot.mp ((a.left_fixed_eq_bot h hH hgen c d).1.le hh))
  let : IsElementaryAbelian 2 Q := hb.ambient_core_elementary_of_residual hres hfix
  have hself : centralizer (Q : Set M) ≤ Q :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T)
      ⟨h.maximal_local.1.2.2,fun _ hx => (le_sup_right : (T : Subgroup G) ≤ M) hx⟩)
  have hcent : centralizer (Q : Set M) = Q := by
    apply le_antisymm hself
    intro x hx y hy
    exact congrArg Q.subtype (mul_comm (⟨y,hy⟩ : Q) ⟨x,hx⟩)
  have hsub : (Q.map M.subtype).subgroupOf M = Q :=
    comap_map_eq_self_of_injective M.subtype_injective Q
  have hr : IsPReduced 2 Q := ⟨inferInstance,inferInstance,by
    let e := QuotientGroup.quotientMulEquivOfEq hcent
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [pCore_map_iso,Subgroup.map_bot]
    exact pCore_quotient_pCore_eq_bot 2⟩
  have hr' : IsPReduced 2 ((Q.map M.subtype).subgroupOf M) := hsub.symm ▸ hr
  have hred : Q.map M.subtype ∈ reducedFamily M :=
    ⟨map_subtype_le Q,IsElementaryAbelian.map M.subtype,hr'.normal,hr'.quotient_pCore_eq_bot⟩
  have hWQ : W ≤ Q.map M.subtype := by
    have hh := map_mono (f := M.subtype) h.reduced_internal.le_pCore
    rwa [map_subgroupOf_eq_of_le h.reduced.1] at hh
  exact { h with
    reduced := hred
    noncentral := by
      intro he
      exact h.noncentral (bot_unique ((commutator_mono hWQ le_rfl).trans_eq he)) }

/-- Reselecting the elementary ambient core through the universal Input
makes it fully moved by the original cubic, hence equal to the left block layer. -/
theorem LocalA7Configuration.left_core_block_layer
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 =
      (ChapterC.blockU (L.subgroupOf (L ⊔ (T : Subgroup G)))).map
        ((L ⊔ (T : Subgroup G)).subtype.comp (L.subgroupOf (L ⊔ (T : Subgroup G))).subtype) := by
  let M := L ⊔ (T : Subgroup G)
  let Q := M.pCoreIn 2
  have hQ := a.left_core_input h hH hgen c d
  have hfixed : Q ⊓ centralizer (D : Set G) = ⊥ :=
    (a.cubic_fixed_eq_bot hQ hH hgen c d).1
  have hDL : D ≤ L := ((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_left
  have hDM : D ≤ M := hDL.trans le_sup_left
  have hQN : M ≤ normalizer (Q : Set G) := by
    change M ≤ normalizer ((pCore 2 M).map M.subtype : Set G)
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using
      ((pCore 2 M).le_normalizer_map M.subtype)
  have hn : D ≤ normalizer (Q : Set G) := hDM.trans hQN
  let := hQ.reduced.2.1
  have hcop : Nat.Coprime (Nat.card D) (Nat.card Q) := by
    obtain ⟨k,hk⟩ := (isPGroup_pCoreIn 2 M).exists_card_eq
    rw [d.cubic_card,hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hm : Q = ⁅Q,D⁆ := by
    have hh := eq_commutator_sup_centralizer_of_solvable_coprime Q D hn inferInstance hcop
    simpa only [hfixed,sup_bot_eq] using hh
  have hfull : ⁅Q,L⁆ = Q := le_antisymm
    (le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans hQN))
    (hm.trans_le (commutator_mono le_rfl hDL))
  have hb := (a.left_block h hH hgen c d).1.ambient_core_commutator
  have hh := congrArg (map M.subtype) hb
  rw [map_commutator,map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left),map_map] at hh
  exact hfull.symm.trans hh
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
