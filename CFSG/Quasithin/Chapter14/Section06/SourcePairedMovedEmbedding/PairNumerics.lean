module
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Centralizer
public import Theory.GroupTheory.CentralKernelSubgroupEmbedding
public import Theory.GroupTheory.PrimeRankProduct

/-!
# Numerical invariants of the actual moved alternating-five pair

The source equality O₂(B)=U(B) removes the possible central two-extension:
the short-group centralizer formula and the trivial fixed layer make B
centerless, and the actual quotient by its order-sixteen layer has order
sixty. Two commuting such blocks embed as a direct product of order
960². Every homomorphism with central kernel remains injective on that
product. Its two elementary layers give two-rank at least eight.

These statements retain the actual embeddings and quotient homomorphism.
The companion source adapter derives the core equality on the original
paired C.5 blocks. Source: Aschbacher--Smith 14.6.9, printed p.1026.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
open ChapterC
variable {A G H : Type*} [Group A] [Group G] [Group H]

/-- The exact source core equality removes the entire block center. -/
theorem block_center_eq_bot (hB : IsAlternatingBlock A 5)
    (hcore : pCore 2 A = blockU A) : center A = ⊥ := by
  have hcu : center A ≤ blockU A := by
    rw [←hcore,←hB.2.1.centralizer_blockU]
    exact center_le_centralizer _
  have hz : blockU A ⊓ center A = ⊥ := by
    rw [←blockFixed_map,hB.blockFixed_eq_bot,Subgroup.map_bot]
  exact bot_unique ((le_inf hcu le_rfl).trans hz.le)

/-- The actual block has order sixteen times sixty. -/
theorem block_card_eq_960 (hB : IsAlternatingBlock A 5)
    (hcore : pCore 2 A = blockU A) : Nat.card A = 960 := by
  let : Finite A := hB.2.1.finite
  obtain ⟨e⟩ := hB.2.2.quotient_iso
  have hq : Nat.card (A ⧸ pCore 2 A) = 60 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  rw [←(pCore 2 A).card_mul_index,index_eq_card,hq,hcore,hB.blockU_card]

/-- The cardinality formulation recovers the exact intrinsic core equality. -/
theorem block_core_eq_blockU_of_card_sixteen (hB : IsAlternatingBlock A 5)
    (hcard : Nat.card (pCore 2 A) = 16) : pCore 2 A = blockU A := by
  let : Finite A := hB.2.1.finite
  exact (eq_of_le_of_card_ge blockU_le_core (by rw [hcard,hB.blockU_card])).symm

/-- A central ambient kernel meets the original block trivially. -/
theorem block_comp_injective_of_central_ker (B : Subgroup G) (hB : IsAlternatingBlock B 5)
    (hcore : pCore 2 B = blockU B) (f : G →* H) (hk : f.ker ≤ center G) :
    Function.Injective (f.comp B.subtype) := by
  intro x y he
  apply f.subgroupMap_injective_of_ker_le_center hk B (block_center_eq_bot hB hcore)
  exact Subtype.ext he

/-- Multiplication embeds both original blocks through any central-kernel map. -/
theorem pair_map_injective_of_central_ker (B C : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hC : IsAlternatingBlock C 5)
    (hcoreB : pCore 2 B = blockU B) (hcoreC : pCore 2 C = blockU C)
    (hc : B ≤ centralizer (C : Set G)) (f : G →* H) (hk : f.ker ≤ center G) :
    Function.Injective ((f.comp B.subtype).noncommCoprod (f.comp C.subtype)
      (fun x y => Commute.map (show Commute (x : G) (y : G) from (hc x.property y y.property).symm) f)) := by
  have hiB := block_comp_injective_of_central_ker B hB hcoreB f hk
  have hiC := block_comp_injective_of_central_ker C hC hcoreC f hk
  apply (MonoidHom.noncommCoprod_injective _ _ _).mpr
  refine ⟨hiB,hiC,disjoint_def.mpr ?_⟩
  rintro x ⟨b,rfl⟩ ⟨c,he⟩
  have hb : b ∈ center B := by
    apply mem_center_iff.mpr
    intro w
    apply hiB
    have hh := Commute.map (show Commute (w : G) (c : G) from (hc w.property c c.property).symm) f
    change Commute ((f.comp B.subtype) w) ((f.comp C.subtype) c) at hh
    rw [he] at hh
    simpa only [map_mul] using hh.eq
  have hb1 : b = 1 := mem_bot.mp ((block_center_eq_bot hB hcoreB) ▸ hb)
  rw [hb1,map_one]

/-- The original elementary layer supplies four independent involutions. -/
theorem block_rank_ge_four [Finite A] (hB : IsAlternatingBlock A 5) :
    4 ≤ primeRank 2 A := by
  let : IsElementaryAbelian 2 (blockU A) := hB.2.1.elementary
  exact IsElementaryAbelian.primeRank_ge_of_card (blockU A) (by simpa using hB.blockU_card)

/-- The actual quotient target retains the full pair order and elementary rank. -/
theorem paired_numerics_of_central_ker [Finite G] [Finite H] (B C : Subgroup G)
    (hB : IsAlternatingBlock B 5) (hC : IsAlternatingBlock C 5)
    (hcoreB : pCore 2 B = blockU B) (hcoreC : pCore 2 C = blockU C)
    (hc : B ≤ centralizer (C : Set G)) (f : G →* H) (hk : f.ker ≤ center G) :
    8 ≤ primeRank 2 H ∧ 25 ∣ Nat.card H ∧ 921600 ∣ Nat.card H := by
  let g := (f.comp B.subtype).noncommCoprod (f.comp C.subtype)
      (fun x y => Commute.map (show Commute (x : G) (y : G) from (hc x.property y y.property).symm) f)
  have hi : Function.Injective g := pair_map_injective_of_central_ker B C hB hC hcoreB hcoreC hc f hk
  have hcard : 921600 ∣ Nat.card H := by
    have hh := Subgroup.card_dvd_of_injective g hi
    rwa [Nat.card_prod,block_card_eq_960 hB hcoreB,block_card_eq_960 hC hcoreC] at hh
  refine ⟨?_,(by decide : 25 ∣ 921600).trans hcard,hcard⟩
  have hr := primeRank_le_of_injective 2 g hi
  rw [primeRank_prod_eq_add] at hr
  have hb := block_rank_ge_four hB
  have hc := block_rank_ge_four hC
  omega
end CFSG.Quasithin.Chapter14.Section06.SourcePairedMovedEmbedding
