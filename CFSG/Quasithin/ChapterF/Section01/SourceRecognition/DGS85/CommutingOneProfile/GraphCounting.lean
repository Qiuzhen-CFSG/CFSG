module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.GraphSeeds
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Counting the actual Chapter 11 graph seeds

Local transitivity supplies the conjugate seed, and the neighboring core
normalizes it by the source graph. The relative-index product formula gives
|Zα ∩ Qβ| = qα qβ and |V| = qα² qβ. If V is the actual beta core and
S = Zα Qβ, it gives |S| = qα² qβ². A matching upper bound on the core
already forces V = Qβ by inclusion. No finiteness of the completion is
assumed, and no arbitrary conjugator or normalization premise is needed.

The seed order, index and intersection remain (11.3)--(11.6) inputs.
Source: Delgado--Goldschmidt--Stellmacher, *Groups and Graphs* (1985),
(11.3), (11.6), (11.7)(c) and the Suzuki case in (11.8), pp.168--176.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

private theorem local_product_card (A C : Subgroup G)
    (hn : C ≤ normalizer (A : Set G)) :
    Nat.card A * Nat.card C = Nat.card (A ⊓ C : Subgroup G) * Nat.card (A ⊔ C : Subgroup G) := by
  let H := A ⊔ C
  let : (A.subgroupOf H).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le A.le_normalizer hn)
  have he := relIndex_sup_left (C.subgroupOf H) (A.subgroupOf H)
  rw [←subgroupOf_sup le_sup_left le_sup_right,relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at he
  have hi : A.relIndex H = (A ⊓ C).relIndex C :=
    he.trans (inf_relIndex_right A C).symm
  have hH := relIndex_mul_relIndex (⊥ : Subgroup G) A H bot_le le_sup_left
  have hC := relIndex_mul_relIndex (⊥ : Subgroup G) (A ⊓ C) C bot_le inf_le_right
  simp only [relIndex_bot_left] at hH hC
  rw [hi] at hH
  rw [←hC,←hH]
  ac_rfl

/-- The two neighboring seeds have the source orders on the literal graph. -/
theorem source_pairSpan_card (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (qα qβ : ℕ) (hqβ : 0 < qβ)
    (hZ : Nat.card (Z (family P) a) = qα * qβ ^ 2)
    (hindex : (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = qβ)
    (hinter : Nat.card ((Z (family P) a ⊓ Q (family P) b) ⊓
      (Z (family P) c ⊓ Q (family P) b) : Subgroup G) = qβ) :
    Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) = qα * qβ ∧
      Nat.card (pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b)) =
        qα ^ 2 * qβ := by
  have hcount := relIndex_mul_relIndex (⊥ : Subgroup G)
    (Z (family P) a ⊓ Q (family P) b) (Z (family P) a) bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,hindex,hZ] at hcount
  have hseed : Nat.card (Z (family P) a ⊓ Q (family P) b : Subgroup G) = qα * qβ := by
    apply Nat.eq_of_mul_eq_mul_right hqβ
    exact hcount.trans (by ring)
  obtain ⟨g,_,_,_,hg⟩ := source_neighbor_conjugate h hab hbc
  have hseed' : Nat.card (Z (family P) c ⊓ Q (family P) b : Subgroup G) = qα * qβ := by
    rw [←hg,card_map_of_injective (MulAut.conj g).injective]
    exact hseed
  have hn : Q (family P) b ≤ normalizer
      (Z (family P) a ⊓ Q (family P) b : Subgroup G) :=
    (le_inf (source_adjacent_core_normalizes_center h hab) (Q (family P) b).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hprod := local_product_card (Z (family P) a ⊓ Q (family P) b)
    (Z (family P) c ⊓ Q (family P) b) (inf_le_right.trans hn)
  rw [hseed,hseed',hinter] at hprod
  refine ⟨hseed,?_⟩
  apply Nat.eq_of_mul_eq_mul_left hqβ
  exact hprod.symm.trans (by ring)

/-- The Suzuki core bound forces equality with the actual two-seed subgroup. -/
theorem source_core_eq_pairSpan_of_small_order (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c)
    (qα qβ : ℕ) (hqβ : 0 < qβ)
    (hZ : Nat.card (Z (family P) a) = qα * qβ ^ 2)
    (hindex : (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = qβ)
    (hinter : Nat.card ((Z (family P) a ⊓ Q (family P) b) ⊓
      (Z (family P) c ⊓ Q (family P) b) : Subgroup G) = qβ)
    (hsmall : Nat.card (Q (family P) b) ≤ qα ^ 2 * qβ) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) := by
  let := finite_endpoints h
  let : Finite (Q (family P) b) := Finite.of_injective
    (inclusion (Q_le_stabilizer _ b)) (inclusion_injective _)
  have hc := (source_pairSpan_card h hab hbc qα qβ hqβ hZ hindex hinter).2
  exact (eq_of_le_of_card_ge (pairSpan_le_core _ _ _) (hsmall.trans hc.ge)).symm

/-- The order formula of (11.7)(c), conditional on the earlier seed geometry. -/
theorem source_sylow_card_of_pair_core (h : LocallyRankOneTriple P B)
    {a b c : Vertex (family P)} (hab : (graph (family P)).Adj a b)
    (hbc : (graph (family P)).Adj b c) (S : Subgroup G)
    (hcore : Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b))
    (hS : S = Z (family P) a ⊔ Q (family P) b)
    (qα qβ : ℕ) (hqα : 0 < qα) (hqβ : 0 < qβ)
    (hZ : Nat.card (Z (family P) a) = qα * qβ ^ 2)
    (hindex : (Z (family P) a ⊓ Q (family P) b).relIndex (Z (family P) a) = qβ)
    (hinter : Nat.card ((Z (family P) a ⊓ Q (family P) b) ⊓
      (Z (family P) c ⊓ Q (family P) b) : Subgroup G) = qβ) :
    Nat.card S = qα ^ 2 * qβ ^ 2 := by
  obtain ⟨hseed,hpair⟩ := source_pairSpan_card h hab hbc qα qβ hqβ hZ hindex hinter
  have hQ : Nat.card (Q (family P) b) = qα ^ 2 * qβ :=
    (congrArg (fun A : Subgroup G => Nat.card A) hcore).trans hpair
  have hprod := local_product_card (Z (family P) a) (Q (family P) b)
    (source_adjacent_core_normalizes_center h hab)
  rw [hZ,hQ,hseed,←hS] at hprod
  apply Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hqα hqβ)
  exact hprod.symm.trans (by ring)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
