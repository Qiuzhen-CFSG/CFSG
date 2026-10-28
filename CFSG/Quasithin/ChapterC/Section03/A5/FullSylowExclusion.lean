module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedCenter
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.CarrierSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.SporadicSieve
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedMathieu
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedM24
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedJ4
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedHeld
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveDeletedRu
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingTerminal.LieRows
public import Theory.GroupTheory.SylowLocalCore

/-!
# The ordinary-component exclusion for a full-Sylow A₅ block

The actual deleted-five block survives the central quotient of its containing
quasisimple group. Its characteristic elementary layer has order sixteen.
The full-Sylow local-component sieve excludes the alternating, higher binary
linear and rank-one carriers. In rank two the same block has an invariant
parabolic escape; restriction to the original Sylow intersection contradicts
the native local obstruction. The normalized elementary layer leaves six
sporadic carriers, each excluded by its actual local block geometry.

Thus the A₅ specialization needs neither a full ambient component-normalizer
identity nor the general C.3.1 marked-pair classification. The final theorem
restricts the original Sylow and local block to an ordinary component.
Source: Aschbacher--Smith C.3.1, printed pp.149--151, and the A₅ case of
4.3.6, printed pp.614--615, using A.3.11--14 and the native 2.4.25 calculations.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

private theorem no_invariant_parabolic_escape
    (S : Sylow 2 G) (B N : Subgroup G)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G)) (hBN : B ≤ N)
    (hi : ∀ a : MulAut G, ((blockU B).map B.subtype).map a.toMonoidHom =
      (blockU B).map B.subtype → N.map a.toMonoidHom = N)
    (hbad : ∀ P : Sylow 2 N, B.subgroupOf N ∉ localCComponents P) : False := by
  have hSN : (S : Subgroup G) ≤ normalizer (N : Set G) := by
    intro s hs
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply hi
    exact mem_normalizer_iff_map_conj_eq.mp
      ((hn.trans (normalizer_le_normalizer_characteristic_image B (blockU B))) hs)
  let J := N ⊔ (S : Subgroup G)
  obtain ⟨P,hP⟩ := (S.subtype (show (S : Subgroup G) ≤ J from le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
    (show N ≤ J from le_sup_left) (sup_le N.le_normalizer hSN)
  have hPS : (P : Subgroup N) = (S : Subgroup G).subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [hP,subgroupOf_map_subtype]
    have he : ((S.subtype (show (S : Subgroup G) ≤ J from le_sup_right) : Sylow 2 J) :
        Subgroup J).map J.subtype = S := map_subgroupOf_eq_of_le le_sup_right
    rw [he,inf_comm]
  exact hbad P (hPS.symm ▸ local_restrict hl hBN)

/-- Exhaust the actual simple carriers while retaining the original block and full Sylow. -/
theorem no_simple_alternatingFive_full_sylow [IsSimpleGroup G] [IsQuasisimple G]
    (S : Sylow 2 G) (B : Subgroup G) (hb : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hne : B ≠ ⊤) (hm : ChapterA.Section02.IsTheoremCModel G) : False := by
  let U := (blockU B).map B.subtype
  let := hb.2.1.elementary
  have hU : IsElementaryAbelian 2 U := IsElementaryAbelian.map B.subtype
  have hc : Nat.card U = 16 := (card_map_of_injective B.subtype_injective).trans hb.blockU_card
  have hnU : (S : Subgroup G) ≤ normalizer (U : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image B (blockU B))
  obtain ⟨eB⟩ := hb.2.2.quotient_iso
  rcases FiveLocalFF.CarrierSieve.rank_two_or_sporadic S B hl hne eB U hU hc.ge hm with
    ⟨f,hr⟩ | hs
  · have hr' : Chapter1.Section02.LocalModels.RankTwoTheoremC G := by
      cases hr with
      | linear hf hm => exact .linear f hf hm
      | symplectic hf hm => exact .symplectic f hf hm
      | g2 hf hm => exact .g2 f hf hm
      | triality hf hm => exact .triality f hf hm
      | ree_f4 m hm _ he =>
        exact (no_alternatingFive_of_reeF4_equiv hm he.some B hb hc).elim
      | symplectic_derived _ he => exact .symplectic_derived he
      | g2_derived _ he => exact .g2_derived he
      | tits _ he => exact .tits he
    obtain ⟨N,_,hBN,hi,hbad⟩ :=
      Chapter2.AlternatingTerminal.rank_two_invariant_obstruction hr' B hb hc
    exact no_invariant_parabolic_escape S B N hl hn hBN hi hbad
  · obtain ⟨name,hname,⟨e⟩⟩ := FiveLocalFF.SporadicSieve.six_carriers S U hU hnU hc.ge hs
    rcases hname with h | h | h | h | h | h <;> subst name
    · exact alternatingFiveDeleted_not_m22 e S B hb hl hn
    · exact alternatingFiveDeleted_not_m23 e S B hb hl hn
    · exact alternatingFiveDeleted_not_m24 e S B hb hl hn
    · exact alternatingFiveDeleted_not_j4 e S B hb hl hn
    · exact alternatingFiveDeleted_not_held e S B hb hn
    · exact alternatingFiveDeleted_not_ru e S B hb hn

/-- A proper local deleted-five block cannot be normalized by a full Sylow
of a quasisimple SQTK group. No bound on that Sylow or central disjointness is assumed. -/
theorem no_quasisimple_alternatingFive_full_sylow [IsQuasisimple G]
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) (B : Subgroup G) (hb : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hne : B ≠ ⊤) : False := by
  let : IsSimpleGroup (G ⧸ center G) := IsQuasisimple.simple
  let : IsQuasisimple (G ⧸ center G) := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (center G)) (QuotientGroup.mk'_surjective (center G))
  obtain ⟨hl',hn',hb',hne'⟩ := alternatingFive_block_center_image S hl hn hb hne
  exact no_simple_alternatingFive_full_sylow
    (S.mapSurjective (QuotientGroup.mk'_surjective (center G))) _ hb' hl' hn' hne'
    (quasisimple_center_quotient_theoremC_model hG)

/-- Restrict the same local block and full Sylow to its containing ordinary
component. Escape supplies precisely the required properness. -/
theorem no_ordinary_component_containing_alternatingFive
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (S : Sylow 2 G) (B : Subgroup G) (hb : IsAlternatingBlock B 5)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (K : Subgroup G) (hK : IsComponent G K) (hBK : B ≤ K)
    (hout : ¬ K ≤ normalizer (B : Set G)) : False := by
  let := hK.2
  obtain ⟨P,hP,hl'⟩ := exists_local_sylow_restriction S hl hBK hK.1
  have hb' : IsAlternatingBlock (B.subgroupOf K) 5 :=
    RankOne.Solvable.isAlternatingBlock_of_equiv (subgroupOfEquivOfLe hBK).symm hb
  have hn' : (P : Subgroup K) ≤ normalizer (B.subgroupOf K : Set K) := by
    rw [hP,←subgroupOf_normalizer_eq hBK]
    exact comap_mono hn
  have hne : B.subgroupOf K ≠ ⊤ :=
    fun he => hout ((subgroupOf_eq_top.mp he).trans B.le_normalizer)
  exact no_quasisimple_alternatingFive_full_sylow (hG.subgroup K) P _ hb' hl' hn' hne

end CFSG.Quasithin.ChapterC
