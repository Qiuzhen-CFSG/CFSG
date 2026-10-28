module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Valence
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.PathExistence
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# Full-catalogue branching and the source path complement

The original product P = G* B identifies the full endpoint's Borel index
with the normalizer index of its marked Sylow in G*/O₂(G*). The concrete
catalogue therefore supplies two-power branching in both vertex orbits,
including Suzuki, special and projective unitary, and dihedral endpoints.
This discharges the model premise in the literal path product of DGS 6.7.
No classification of the enlarged local actor is required for this step.

For the reduced F1.11 graph, finite stabilizers construct a first
nonregular path and its transitivity. Schur--Zassenhaus then constructs
a path-fixing complement whose image supplements O₂ of the original full
Borel inside B₀. The completion need not be finite or a tree, and the
original S is not identified with that two-core. The first nonregular
length r is not identified with the book's possibly larger parameter s;
the endpoint-core and length assertions of 6.8 remain separate.

Source: DGS, Groups and Graphs (1985), 3.4, pp.73--74, reduction pp.95--96,
and 6.7--6.8, p.123; Aschbacher--Smith, F.1.9, printed pp.261--262.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
open SimpleGraph SimpleGraph.PathTransitivePolygon Theory.GroupAction.CubicTree
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.Source.DGS85
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- The full endpoint and its original starred quotient have the same Borel index. -/
theorem source_borel_index_eq_starred_quotient {R : Subgroup G}
    (d : LocalRankOneData R B) :
    (B.subgroupOf R).index =
      (normalizer (((d.sylow : Subgroup d.Pstar).map
        (QuotientGroup.mk' (pCore 2 d.Pstar))) : Set (d.Pstar ⧸ pCore 2 d.Pstar))).index := by
  let := d.finite_P
  have hBR : B ≤ R := le_sup_right.trans d.supplement.le
  let : Finite B := Finite.of_injective (inclusion hBR) (inclusion_injective _)
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  have he := relIndex_sup_of_normalizes d.Pstar B
    (hBR.trans ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal))
  rw [d.supplement] at he
  change B.relIndex R = _
  rw [he]
  change (B.subgroupOf d.Pstar).index = _
  have hn := quotientSylow_normalizer_comap d.sylow
  simp only [Sylow.coe_coe] at hn
  rw [source_star_borel d,←hn,index_comap_of_surjective _ (QuotientGroup.mk'_surjective _)]
  rfl

/-- Every source endpoint has two-power forward branching, with all catalogue rows retained. -/
theorem source_borel_branching {R : Subgroup G} (d : LocalRankOneData R B) :
    ∃ k : ℕ, (B.subgroupOf R).index - 1 = 2^k := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  rw [source_borel_index_eq_starred_quotient d]
  exact d.quotient.sylow_normalizer_branching (quotientSylow d.sylow)

/-- Both vertex orbits of the actual source coset graph have two-power branching. -/
theorem source_rankOne_branching (h : LocallyRankOneTriple P B) :
    ∀ i, ∃ k : ℕ, ((family P (!i)).subgroupOf (family P i)).index - 1 = 2^k := by
  intro i
  have he : (family P (!i)).subgroupOf (family P i) = B.subgroupOf (family P i) := by
    rw [←inf_subgroupOf_right]
    have hi : family P (!i) ⊓ family P i = B := by
      cases i
      · exact (inf_comm _ _).trans h.intersection
      · exact h.intersection
    rw [hi]
  rw [he]
  cases i
  · exact source_borel_branching (Classical.choice (h.local_data 0))
  · exact source_borel_branching (Classical.choice (h.local_data 1))

/-- DGS 6.7 on every transitive path length, with model branching discharged. -/
theorem source_rankOne_path_borel_product (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    {v : Vertex (family P)} {n : ℕ}
    (ht : RootPathTransitive (graph (family P)) G v (n+1))
    (p : BasedWalk (graph (family P)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (family P) false ∈ p.vertices) (hb : base (family P) true ∈ p.vertices) :
    (B : Set G) = ((B ⊓ pathStabilizer (family P) p : Subgroup G) : Set G) *
      (B.pCoreIn 2 : Set G) :=
  source_path_borel_product h hB (source_rankOne_branching h) ht p hp ha hb

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The reduced graph retains every original local model and needs no enlargement recognition. -/
theorem reduced_rankOne_branching (h : HypothesisF11 L S) :
    ∀ i, ∃ k : ℕ,
      ((reducedFamily L S (!i)).subgroupOf (reducedFamily L S i)).index - 1 = 2^k :=
  source_rankOne_branching (reduced_triple h)

/-- Source 6.7 in the original completion, with its full Borel core and literal inclusion. -/
theorem reduced_rankOne_path_original_product (h : HypothesisF11 L S)
    {v : Vertex (reducedFamily L S)} {n : ℕ}
    (ht : RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v (n+1))
    (p : BasedWalk (graph (reducedFamily L S)) (n+1) v) (hp : p.Nonbacktracking)
    (ha : base (reducedFamily L S) false ∈ p.vertices)
    (hb : base (reducedFamily L S) true ∈ p.vertices) :
    (B₀ L S : Set G) =
      ((B₀ L S ⊓ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype :
        Subgroup G) : Set G) * ((commonBorel L S).pCoreIn 2 : Set G) :=
  reduced_path_original_product h (reduced_rankOne_branching h) ht p hp ha hb

/-- A first nonregular path and its full-Borel complement for the complete catalogue.
The completion can be infinite, and the construction assumes no chosen path or transitivity. -/
theorem reduced_rankOne_nonregular_path_complement (h : HypothesisF11 L S) :
    ∃ n : ℕ,
      (∀ k < n+1, ∀ v : Vertex (reducedFamily L S),
        ∀ p : BasedWalk (graph (reducedFamily L S)) k v,
          p.Nonbacktracking → Regular (A := G₀ L S) p) ∧
      (∀ v : Vertex (reducedFamily L S), ∀ k ≤ n+1,
        RootPathTransitive (graph (reducedFamily L S)) (G₀ L S) v k) ∧
      ∃ i : Bool,
      ∃ p : BasedWalk (graph (reducedFamily L S)) (n+1) (base (reducedFamily L S) i),
        p.Nonbacktracking ∧ ¬ RightRegular (A := G₀ L S) p ∧
        base (reducedFamily L S) false ∈ p.vertices ∧
        base (reducedFamily L S) true ∈ p.vertices ∧
        ∃ K : Subgroup G,
          K ≤ B₀ L S ⊓ (pathStabilizer (reducedFamily L S) p).map (G₀ L S).subtype ∧
          Disjoint K ((commonBorel L S).pCoreIn 2) ∧
          K ⊔ (commonBorel L S).pCoreIn 2 = B₀ L S ∧ Nat.Coprime 2 (Nat.card K) := by
  obtain ⟨n,hs,ht,i,p,hp,hn,ha,hb⟩ := reduced_first_nonregular_path h
  exact ⟨n,hs,ht,i,p,hp,hn,ha,hb,reduced_path_original_complement h
    (reduced_rankOne_branching h) (ht _ _ le_rfl) p hp ha hb⟩
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
