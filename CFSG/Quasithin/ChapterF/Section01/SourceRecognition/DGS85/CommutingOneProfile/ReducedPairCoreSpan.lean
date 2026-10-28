module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.PairCoreDescent
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedOppositeSeedOmega
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ReducedElementaryProfile

/-!
# Source-path applications of the general Chapter 11 core span

The actual DGS 6.7 path product supplies the supplement used in the
(11.3)(h) proof. Transport through the reduced-group inclusion retains the
original endpoint quotient markings, both core intersections and the
corrected Chapter 11 seed span. The completion may be infinite.

The elementary-profile consumer now derives its core-span input. It still
requires the independent (11.4) edge-core product and the literal elementary
S/Q_beta branch. Neither alpha nor beta is preselected as linear. The
earlier local data, actual path and its transitivity remain source inputs;
full original assembly must discharge them with their existing producers.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.3)(h)--(11.7), printed pp.170--174; (6.7), p.123.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

open SimpleGraph SimpleGraph.PathTransitivePolygon

/-- Source (11.3)(h) with the earlier path-product premise discharged by
6.7. Every alpha and beta rank-one row is retained. -/
theorem source_rankOne_pair_core_span_on_path
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a b c : Vertex (family P)} (hc : IsCriticalPair (family P) a b)
    (hb : DGS85.b (family P) = 1) (hbc : (graph (family P)).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    Q (family P) b = pairSpan (Z (family P) a) (Z (family P) c) (Q (family P) b) ⊔
      (Q (family P) a ⊓ Q (family P) b) := by
  exact source_rankOne_pair_core_span_of_supplement h hB d hc hb hbc hac Ma Mb
    (source_opposite_seed_path_supplement h hB ht p hp (source_critical_one_adjacent hc hb) ha hb' hc')


section Original
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The (11.3)(h) identity on the original core and seed images, retaining
both original quotient markings and the source path. -/
theorem original_reduced_pair_core_span_on_path
    (h : HypothesisF11 L₀ S₀) (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel ((d.localGroup a).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup a).map (G₀).subtype)))
    (Mb : IsRankOneModel ((d.localGroup b).map (G₀).subtype ⧸
      pCore 2 ((d.localGroup b).map (G₀).subtype)))
    {v : Vertex F₀} {n : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (n+1))
    (p : BasedWalk (graph F₀) (n+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    let j := (G₀).subtype
    (Q F₀ b).map j =
      (pairSpan (Z F₀ a) (Z F₀ c) (Q F₀ b)).map j ⊔
        ((Q F₀ a).map j ⊓ (Q F₀ b).map j) := by
  let ea := (d.localGroup a).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hs := source_rankOne_pair_core_span_on_path (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      ht p hp ha hb' hc'
  have hm := congrArg (Subgroup.map (G₀).subtype) hs
  rw [Subgroup.map_sup,Subgroup.map_inf _ _ _ (G₀).subtype_injective] at hm
  exact hm

/-- The elementary-profile consumer no longer assumes (11.3)(h). Its
remaining core-product input is precisely source (11.4), and the branch
hypothesis is still the literal S/Q_beta elementary quotient. -/
theorem reduced_elementary_profile_on_path (h : HypothesisF11 L₀ S₀)
    (d : EarlierLocalTheorems F₀)
    {a b c : Vertex F₀} (hc : IsCriticalPair F₀ a b)
    (hb : DGS85.b F₀ = 1) (hcomm : ⁅Z F₀ a,Z F₀ b⁆ = ⊥)
    (hbc : (graph F₀).Adj b c) (hac : a ≠ c)
    (Ma : IsRankOneModel (d.localGroup a ⧸ pCore 2 (d.localGroup a)))
    (Mb : IsRankOneModel (d.localGroup b ⧸ pCore 2 (d.localGroup b)))
    (hproduct : (stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2 = Q F₀ a ⊔ Q F₀ b)
    (helem : ∃ hN : ((Q F₀ b).subgroupOf
        ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) ⧸
        (Q F₀ b).subgroupOf ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2)))
    {v : Vertex F₀} {r : ℕ}
    (ht : RootPathTransitive (graph F₀) G₀ v (r+1))
    (p : BasedWalk (graph F₀) (r+1) v) (hp : p.Nonbacktracking)
    (ha : a ∈ p.vertices) (hb' : b ∈ p.vertices) (hc' : c ∈ p.vertices) :
    ∃ n m, 1 < n ∧ 0 < m ∧
      ClassicalGroup.IsPSL (d.localGroup a ⧸ pCore 2 (d.localGroup a)) 2 (2^n) ∧
      ClassicalGroup.IsPSL (d.localGroup b ⧸ pCore 2 (d.localGroup b)) 2 (2^m) ∧
      n = 2*m ∧ Q F₀ a = Z F₀ a ∧ betaSpan (stabilizer F₀ b) (Z F₀ a) = Q F₀ b ∧
      Nat.card (Z F₀ b) = 2^m ∧ Nat.card (Z F₀ a) = (2^n)^2 ∧
      Nat.card (Q F₀ b) = (2^n)^2 * 2^m ∧
      Nat.card ((stabilizer F₀ a ⊓ stabilizer F₀ b).pCoreIn 2) = (2^n)^2 * (2^m)^2 := by
  exact reduced_elementary_profile_of_core_identities h d hc hb hcomm hbc hac Ma Mb hproduct
    (source_rankOne_pair_core_span_on_path (Reduction.reduced_triple h)
      (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac Ma Mb ht p hp ha hb' hc') helem
end Original

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
