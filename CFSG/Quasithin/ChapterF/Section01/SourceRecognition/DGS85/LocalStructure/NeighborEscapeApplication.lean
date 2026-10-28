module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.NeighborEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LinearOddTransport
/-!
# The literal reduced F1.11 escaping-center configuration

The noncentral linear 6.5 branch gives escape of the closed radius-one
span from O₂(X), and then an actual neighboring vertex whose center is in
Q_delta but outside O₂(X). When the original delta quotient is also linear,
the proved odd-order local transport moves the original neighbor to this
one. It fixes Q_delta and carries O₂(X) to the corresponding distinct core.

The transporter embeds in the original starred endpoint enlarged by the
original full Borel's two-core. Both order assertions and the precise
conjugation of the closure cores are retained. The two original field
markings may have different sizes; no equality is imposed.

Source: DGS, Groups and Graphs (1985), 6.5, printed p.122. Relative normality,
noncentrality and the displayed local linear markings remain hypotheses.
The central case, general model selection and the final contradiction from
the Frattini quotient's two maximal elementary subgroups are not asserted.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The literal closed radius-one span escapes and supplies an actual neighboring center outside the closure core. -/
theorem source_linear_escaping_neighbor (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (hS : ∀ i, ∃ T : Sylow 2 (P i), (T : Subgroup (P i)).map (P i).subtype ≤ B)
    (j : Bool) (d : LocalRankOneData (family P (!j)) B)
    (hn : localEnlargement d ≤ normalizer
      (↑((family P j).pCoreIn 2 ⊓ (family P (!j)).pCoreIn 2) : Set G))
    (q : localEnlargement d →* SL(2,F)) (hq : Function.Surjective q)
    (hk : q.ker = pCore 2 (localEnlargement d))
    (hnc : ¬ sylowCenterSpan (family P (!j)) ≤ centralizer
      (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j)) : Set G)) :
    let X := conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))
    (¬ V (family P) (base (family P) j) 1 ≤ X.pCoreIn 2) ∧
    ∃ mu : Vertex (family P), (graph (family P)).Adj (base (family P) j) mu ∧
      Z (family P) mu ≤ Q (family P) (base (family P) j) ∧
      ¬ Z (family P) mu ≤ X.pCoreIn 2 := by
  let := finite_endpoints h
  have hball : ¬ V (family P) (base (family P) j) 1 ≤
      (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))).pCoreIn 2 := by
    rw [source_base_radius_one_eq_span h hB hS]
    cases j
    · exact source_linear_neighbor_span_escape h hB hS 0 d hn q hq hk hnc
    · exact source_linear_neighbor_span_escape h hB hS 1 d hn q hq hk hnc
  refine ⟨hball,?_⟩
  have he : ∃ g ∈ family P j,
      (sylowCenterSpan (family P (!j))).map (MulAut.conj g).toMonoidHom ≤ (family P j).pCoreIn 2 ∧
      ¬ (sylowCenterSpan (family P (!j))).map (MulAut.conj g).toMonoidHom ≤
        (conjugateSpanBy ((family P j).pCoreIn 2) (family P (!j))).pCoreIn 2 := by
    cases j
    · exact source_linear_escaping_conjugate h hB hS 0 d hn q hq hk hnc
    · exact source_linear_escaping_conjugate h hB hS 1 d hn q hq hk hnc
  obtain ⟨g,hg,hgQ,hgout⟩ := he
  have hst (j : Bool) : stabilizer (family P) (base (family P) j) = family P j :=
    Subgroup.CosetGeometry.stabilizer_base _ _
  have hfix : g • base (family P) j = base (family P) j :=
    (show g ∈ stabilizer (family P) (base (family P) j) from (hst j).symm ▸ hg)
  have hadj : (graph (family P)).Adj (base (family P) j) (base (family P) (!j)) :=
    ⟨by cases j <;> exact Bool.noConfusion,Subgroup.CosetGeometry.incident_base _ _ _⟩
  refine ⟨g • base (family P) (!j),?_,?_,?_⟩
  · have hh := (Subgroup.CosetGeometry.translationGraphIso (family P) g).map_adj_iff.mpr hadj
    change (graph (family P)).Adj (g • base (family P) j) (g • base (family P) (!j)) at hh
    rwa [hfix] at hh
  · rw [Z_translate]
    simpa only [Z,Q,hst] using hgQ
  · rw [Z_translate]
    simpa only [Z,hst] using hgout

namespace Reduction
variable {L : Fin 2 → Subgroup G} {S : Subgroup G}
/-- The original F1.11 marking supplies the escape configuration in its actual reduced completion. -/
theorem reduced_linear_escaping_neighbor (h : HypothesisF11 L S) (j : Bool)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data
      (other (if j then 1 else 0)))) ≤ normalizer
      (↑(((P₀ L S (if j then 1 else 0)).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other (if j then 1 else 0))).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) ≃* PSL(2,F))
    (hnc : ¬ Z (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ centralizer
      (conjugateSpanBy (Q (reducedFamily L S) (base (reducedFamily L S) j))
        (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S))) :
    let X := conjugateSpanBy (Q (reducedFamily L S) (base (reducedFamily L S) j))
      (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j)))
    (¬ V (reducedFamily L S) (base (reducedFamily L S) j) 1 ≤ X.pCoreIn 2) ∧
    ∃ mu : Vertex (reducedFamily L S), (graph (reducedFamily L S)).Adj (base (reducedFamily L S) j) mu ∧
      Z (reducedFamily L S) mu ≤ Q (reducedFamily L S) (base (reducedFamily L S) j) ∧
      ¬ Z (reducedFamily L S) mu ≤ X.pCoreIn 2 := by
  let i : Fin 2 := if j then 1 else 0
  let P : Fin 2 → Subgroup (G₀ L S) := fun k => (P₀ L S k).subgroupOf (G₀ L S)
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  let f := reduced_linearEnlargementQuotient h (other i) d e
  let q := f.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (localEnlargement d)))
  have hq : Function.Surjective q := f.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 (localEnlargement d) := by
    rw [MonoidHom.ker_comp_of_injective _ _ f.injective,QuotientGroup.ker_mk']
  have hst (k : Bool) : stabilizer (reducedFamily L S) (base (reducedFamily L S) k) = family P k :=
    Subgroup.CosetGeometry.stabilizer_base _ _
  dsimp only
  simp only [Q,hst] at hnc ⊢
  simp only [Z,hst] at hnc
  cases j
  · have hr := source_linear_escaping_neighbor (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) false d hn q hq hk hnc
    simpa only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base,reducedFamily,P] using hr
  · have hr := source_linear_escaping_neighbor (reduced_triple h) (reduced_borel_core_sylow h)
      (reduced_vertex_sylow h) true d hn q hq hk hnc
    simpa only [Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base,reducedFamily,P] using hr

variable {K : Type*} [Field K] [Finite K] [CharP K 2]
/-- The reduced noncentral linear branch constructs an odd-order mover of the actual closure core, retaining its original endpoint inclusion. -/
theorem reduced_linear_noncentral_core_pair (h : HypothesisF11 L S) (j : Bool)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data
      (other (if j then 1 else 0)))) ≤ normalizer
      (↑(((P₀ L S (if j then 1 else 0)).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other (if j then 1 else 0))).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (e : (L (other (if j then 1 else 0)) ⧸ pCore 2 (L (other (if j then 1 else 0)))) ≃* PSL(2,F))
    (eδ : (family L j ⧸ pCore 2 (family L j)) ≃* PSL(2,K))
    (hnc : ¬ Z (reducedFamily L S) (base (reducedFamily L S) (!j)) ≤ centralizer
      (conjugateSpanBy (Q (reducedFamily L S) (base (reducedFamily L S) j))
        (stabilizer (reducedFamily L S) (base (reducedFamily L S) (!j))) : Set (G₀ L S))) :
    let Δ := reducedFamily L S
    let δ := base Δ j
    let lam := base Δ (!j)
    let X := conjugateSpanBy (Q Δ δ) (stabilizer Δ lam)
    (¬ V Δ δ 1 ≤ X.pCoreIn 2) ∧
    ∃ (mu : Vertex Δ) (x : G₀ L S),
      (graph Δ).Adj δ mu ∧
      x ∈ graphLocalGroup Δ δ ∧ Odd (orderOf x) ∧ x • lam = mu ∧
      (x : G) ∈ family (enlargedEndpoint L S) j ∧ Odd (orderOf (x : G)) ∧
      Z Δ mu ≤ Q Δ δ ∧ ¬ Z Δ mu ≤ X.pCoreIn 2 ∧
      (Q Δ δ).map (MulAut.conj x).toMonoidHom = Q Δ δ ∧
      (X.pCoreIn 2).map (MulAut.conj x).toMonoidHom =
        (conjugateSpanBy (Q Δ δ) (stabilizer Δ mu)).pCoreIn 2 ∧
      (X.pCoreIn 2).map (MulAut.conj x).toMonoidHom ≠ X.pCoreIn 2 := by
  let : ∀ k, Finite (reducedFamily L S k) := finite_endpoints (reduced_triple h)
  let Δ := reducedFamily L S
  let δ := base Δ j
  let lam := base Δ (!j)
  let X := conjugateSpanBy (Q Δ δ) (stabilizer Δ lam)
  obtain ⟨hball,mu,hm,hQ,hout⟩ := reduced_linear_escaping_neighbor h j hn e hnc
  have hadj : (graph Δ).Adj δ lam :=
    ⟨by cases j <;> exact Bool.noConfusion,Subgroup.CosetGeometry.incident_base _ _ _⟩
  obtain ⟨x,hx,hodd,hxm⟩ := reduced_linear_odd_neighbor_transport h j eδ hadj hm
  have hxδ : x • δ = δ := sylowGenerated_le (stabilizer Δ δ) hx
  have hQx : (Q Δ δ).map (MulAut.conj x).toMonoidHom = Q Δ δ := by
    rw [←Q_translate, hxδ]
  have hXx : X.map (MulAut.conj x).toMonoidHom =
      conjugateSpanBy (Q Δ δ) (stabilizer Δ mu) := by
    rw [map_conjugateSpanBy,hQx,←stabilizer_translate,hxm]
  have hxorig : (x : G) ∈ family (enlargedEndpoint L S) j := by
    rw [←reduced_graphLocalGroup_image h j]
    exact mem_map_of_mem (G₀ L S).subtype hx
  have hood : Odd (orderOf (x : G)) := by
    change Odd (orderOf ((G₀ L S).subtype x))
    rw [orderOf_injective (G₀ L S).subtype (G₀ L S).subtype_injective x]
    exact hodd
  have hZC : Z Δ lam ≤ X.pCoreIn 2 := by
    simp only [X,lam,δ,Δ,Z,Q,stabilizer,Subgroup.CosetGeometry.stabilizer_base]
    cases j
    · exact (source_center_le_closure_core_omega (reduced_triple h)
        (reduced_borel_core_sylow h) (reduced_vertex_sylow h) 0).trans (map_subtype_le _)
    · exact (source_center_le_closure_core_omega (reduced_triple h)
        (reduced_borel_core_sylow h) (reduced_vertex_sylow h) 1).trans (map_subtype_le _)
  refine ⟨hball,mu,x,hm,hx,hodd,hxm,hxorig,hood,hQ,hout,hQx,?_,?_⟩
  · rw [←Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective 2
      (MulAut.conj x).toMonoidHom (MulAut.conj x).injective,hXx]
  · intro he
    apply hout
    rw [←hxm,Z_translate]
    exact (map_mono hZC).trans he.le
end Reduction
end CFSG.Quasithin.ChapterF.Source.DGS85
