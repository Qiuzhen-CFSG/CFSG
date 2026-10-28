module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.OppositeSeedOmega
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.RankOnePaths

/-!
# Source-path and original-completion applications of the opposite omega seed

DGS 6.7 expresses each edge stabilizer as its path fixer times the edge
two-core. On a path containing alpha, beta and the opposite alpha vertex,
this supplies the full normalizer invariance used by OppositeSeedOmega.
The resulting equality concerns precisely Q_beta/(Q_alpha intersect Q_beta).

The original application pulls back both original endpoint model markings,
then transports the quotient, relative normality and opposite-seed image
through the reduced-group inclusion. The completion need not be finite.
The earlier local data and path-transitivity input to 6.7 remain explicit;
there is no extra omega or Cartan-invariance premise. PairCoreDescent and
ReducedPairCoreSpan apply this equality to eliminate the complementary
factor. The (11.4) core product and final profiles remain with this owner.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
6.7, printed p.123; (11.3)(c,h), pp.169--171; reduction, pp.95--96.
-/

public noncomputable section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Subgroup.CosetGeometry.RankTwo CommutingNontrivial Theory.GroupTheory.AmalgamGraph
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

open SimpleGraph SimpleGraph.PathTransitivePolygon

/-- The earlier source path product supplies exactly the invariance premise
for the opposite-seed calculation. No independent Cartan or omega premise is added. -/
theorem source_opposite_seed_path_supplement
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v a b c : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (hab : (graph (family P)).Adj a b)
    (ha : a ∈ p.vertices) (hb : b ∈ p.vertices) (hc : c ∈ p.vertices) :
    (stabilizer (family P) a ⊓ stabilizer (family P) b).pCoreIn 2 ⊔
      ((stabilizer (family P) a ⊓ stabilizer (family P) b) ⊓ stabilizer (family P) c) =
        stabilizer (family P) a ⊓ stabilizer (family P) b := by
  have hprod := source_path_edge_product h hB (source_rankOne_branching h) ht p hp hab ha hb
  apply le_antisymm (sup_le (pCoreIn_le 2 _) inf_le_left)
  intro x hx
  change x ∈ ((stabilizer (family P) a ⊓ stabilizer (family P) b : Subgroup G) : Set G) at hx
  rw [hprod] at hx
  obtain ⟨k,hk,s,hs,rfl⟩ := hx
  exact mul_mem (mem_sup_right ⟨pathStabilizer_le_edge (family P) p ha hb hk,hk c hc⟩)
    (mem_sup_left hs)

/-- On the actual source path, the further beta quotient has precisely the
opposite-seed omega subgroup, with every rank-one alternative retained. -/
theorem source_opposite_seed_omega_on_path
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
    let Qb := Q (family P) b
    let I := Q (family P) a ⊓ Qb
    ∃ hN : (I.subgroupOf Qb).Normal, letI := hN
      omegaOneAmbient (⊤ : Subgroup (Qb ⧸ I.subgroupOf Qb)) =
        ((Z (family P) c ⊓ Qb).subgroupOf Qb).map (QuotientGroup.mk' (I.subgroupOf Qb)) := by
  exact source_opposite_seed_omega_quotient_of_supplement h hB d hc hb hbc hac Ma Mb
    (source_opposite_seed_path_supplement h hB ht p hp (source_critical_one_adjacent hc hb) ha hb' hc')


section Original
variable {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- The source opposite-seed omega identity on the literal original images.
The full original endpoint markings and the source path action are retained. -/
theorem original_reduced_opposite_seed_omega_on_path
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
    let Q₁ := (Q F₀ b).map j
    let I₁ := (Q F₀ a).map j ⊓ Q₁
    ∃ hN : (I₁.subgroupOf Q₁).Normal, letI := hN
      omegaOneAmbient (⊤ : Subgroup (Q₁ ⧸ I₁.subgroupOf Q₁)) =
        (((Z F₀ c).map j ⊓ Q₁).subgroupOf Q₁).map (QuotientGroup.mk' (I₁.subgroupOf Q₁)) := by
  let j := (G₀).subtype
  let Q₀ := Q F₀ b
  let I := Q F₀ a ⊓ Q₀
  let Q₁ := Q₀.map j
  let I₁ := (Q F₀ a).map j ⊓ Q₁
  have hImap : I.map j = I₁ := map_inf _ _ _ (G₀).subtype_injective
  have hn : Q₀ ≤ normalizer (I : Set G₀) :=
    (le_inf (source_adjacent_core_normalizes_core (Reduction.reduced_triple h)
      (source_critical_one_adjacent hc hb).symm) Q₀.le_normalizer).trans
        inf_normalizer_le_normalizer_inf
  let hN : (I₁.subgroupOf Q₁).Normal := normal_subgroupOf_of_le_normalizer (by
    change Q₀.map j ≤ normalizer (I₁ : Set G)
    rw [←hImap]
    exact (map_mono hn).trans (le_normalizer_map j))
  let π := QuotientGroup.mk' (I₁.subgroupOf Q₁)
  let eq := Q₀.equivMapOfInjective j (G₀).subtype_injective
  let f := π.comp eq.toMonoidHom
  have hf : Function.Surjective f := (QuotientGroup.mk'_surjective _).comp eq.surjective
  have hk : f.ker = I.subgroupOf Q₀ := by
    ext x
    change π (eq x) = 1 ↔ x.val ∈ I
    change eq x ∈ π.ker ↔ _
    have hkπ : π.ker = I₁.subgroupOf Q₁ := QuotientGroup.ker_mk' _
    rw [hkπ]
    change j x.val ∈ I₁ ↔ _
    rw [←hImap]
    constructor
    · rintro ⟨z,hz,he⟩
      exact (G₀).subtype_injective he ▸ hz
    · exact mem_map_of_mem j
  have hm (A : Subgroup G₀) (hAQ : A ≤ Q₀) :
      (A.subgroupOf Q₀).map f = ((A.map j).subgroupOf Q₁).map π := by
    rw [show f = π.comp eq.toMonoidHom from rfl,←Subgroup.map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact mem_map_of_mem j hw
    · rintro ⟨w,hw,he⟩
      refine ⟨⟨w,hAQ hw⟩,hw,?_⟩
      exact Subtype.ext he
  let ea := (d.localGroup a).equivMapOfInjective j (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup b).equivMapOfInjective j (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have hcover := source_opposite_seed_path_supplement (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) ht p hp (source_critical_one_adjacent hc hb) ha hb' hc'
  have hs := source_opposite_seed_omega_image_of_supplement (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) d hc hb hbc hac (Ma.of_equiv eqa) (Mb.of_equiv eqb)
      hcover f hk
  change omegaOneAmbient f.range = ((Z F₀ c ⊓ Q₀).subgroupOf Q₀).map f at hs
  rw [MonoidHom.range_eq_top.mpr hf,hm _ inf_le_right,
    map_inf _ _ _ (G₀).subtype_injective] at hs
  exact ⟨hN,hs⟩
end Original

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
