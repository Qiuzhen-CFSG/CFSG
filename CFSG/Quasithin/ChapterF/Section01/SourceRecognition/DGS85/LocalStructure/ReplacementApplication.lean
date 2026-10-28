module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementOffender
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.ReplacementAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.BinaryObstructionApplication
public import Theory.GroupTheory.AmalgamGraph.SylowCenterEmbedding

/-!
# The original F1.11 application of the replacement construction

The actual reduced triple supplies the noncentral replacement module and
its escaping quadratic actor. Their inclusion in the original completion
preserves the Sylow-center seed, the original parabolic cores, the closure
under the full neighboring endpoint, and the centralizer index. The relative
normality premise concerns the actual enlarged endpoint. The original full
Borel and original S retain their distinct meanings.

The reduced graph also supplies a faithful action of the literal centralizer
quotient on this very module, without a module-realization assumption.
The central branch, identification of the action kernel with O_2(X), the
rank-one catalogue marking and corrected Sylow fixed generation remain
open. This is a noncentral 6.4 construction, not the full 6.5 obstruction.

Source: DGS, Groups and Graphs (1985), reduction p.95 and 6.4, pp.120--121;
Aschbacher--Smith F.1.9, printed pp.261--262.
-/

public noncomputable section
open Subgroup Theory.GroupTheory.AmalgamGraph
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

private theorem endpoint_le (i : Fin 2) : P₀ L S i ≤ G₀ L S := by
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

private theorem core_image (h : HypothesisF11 L S) (i : Fin 2) :
    (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2).map (G₀ L S).subtype =
      (parabolic L S i).pCoreIn 2 := by
  rw [map_pCoreIn_of_injective 2 _ _ (G₀ L S).subtype_injective,
    map_subgroupOf_eq_of_le (endpoint_le i),P₀_core h i]

private theorem center_image (h : HypothesisF11 L S) (i : Fin 2) :
    (sylowCenterSpan ((P₀ L S i).subgroupOf (G₀ L S))).map (G₀ L S).subtype =
      sylowCenterSpan (P₀ L S i) := by
  let := (Classical.choice ((reduced_triple h).local_data i)).finite_P
  rw [←sylowCenterSpan_map_of_injective _ (G₀ L S).subtype_injective _,
    map_subgroupOf_eq_of_le (endpoint_le i)]

/-- The replacement span retains the original completion inclusion, the
reduced seed and closure under the original full endpoint. -/
theorem reduced_replacement_span_image (h : HypothesisF11 L S) (i : Fin 2) :
    (conjugateSpanBy (sylowCenterSpan ((P₀ L S i).subgroupOf (G₀ L S)))
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)))).map (G₀ L S).subtype =
      conjugateSpanBy (sylowCenterSpan (P₀ L S i))
        (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))) := by
  rw [map_conjugateSpanBy,center_image h i,reduced_core_closure_full_image h i]

/-- The original F1.11 noncentral replacement step, including its original
core intersection, escaping maximum abelian actor and precise index bound. -/
theorem original_replacement_quadratic_offender (h : HypothesisF11 L S) (i : Fin 2)
    (hn : enlargedEndpoint L S (other i) ≤ normalizer
      (↑((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) : Set G))
    (hnc : ¬ sylowCenterSpan (P₀ L S (other i)) ≤ centralizer
      (conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i)) : Set G)) :
    let X := conjugateSpanBy ((parabolic L S i).pCoreIn 2) (parabolic L S (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P₀ L S i)) X
    V ≤ omegaCenterIn ((parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2) ∧
      ∃ A : Subgroup G, A ∈ thompsonAbelianSubgroups ((parabolic L S i).pCoreIn 2) ∧
        ¬ A ≤ (parabolic L S (other i)).pCoreIn 2 ∧ ¬ A ≤ X.pCoreIn 2 ∧
        ⁅⁅V,A⁆,A⁆ = ⊥ ∧ (V ⊓ centralizer (A : Set G)).relIndex V ≤
          ((parabolic L S (other i)).pCoreIn 2).relIndex A := by
  let P := fun j => (P₀ L S j).subgroupOf (G₀ L S)
  let f := (G₀ L S).subtype
  let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
  let V := conjugateSpanBy (sylowCenterSpan (P i)) X
  let d := Classical.choice ((reduced_triple h).local_data (other i))
  have hD : ((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2).map f =
      (parabolic L S i).pCoreIn 2 ⊓ (parabolic L S (other i)).pCoreIn 2 := by
    rw [map_inf _ _ _ (G₀ L S).subtype_injective,core_image h i,core_image h (other i)]
  have hn0 : P (other i) ≤ normalizer (↑((P i).pCoreIn 2 ⊓ (P (other i)).pCoreIn 2) : Set (G₀ L S)) := by
    apply (inter_core_local_normal_iff (reduced_triple h) i d).mp
    intro x hx
    have hxf : f x ∈ enlargedEndpoint L S (other i) := by
      rw [←reduced_localEnlargement_image h (other i) d]
      exact mem_map_of_mem f hx
    have hh := le_normalizer_comap f (hn hxf)
    rwa [←hD,comap_map_eq_self_of_injective (G₀ L S).subtype_injective] at hh
  have hnc0 : ¬ sylowCenterSpan (P (other i)) ≤ centralizer (X : Set (G₀ L S)) := by
    intro hc
    apply hnc
    intro z hz x hx
    obtain ⟨z',hz',rfl⟩ := (center_image h (other i)).symm ▸ hz
    obtain ⟨x',hx',rfl⟩ := (reduced_core_closure_full_image h i).symm ▸ hx
    exact congrArg f (hc hz' x' hx')
  have hV := reduced_replacement_span_image h i
  have hX := reduced_core_closure_full_image h i
  constructor
  · have hh := map_mono (f := f) (source_replacement_span_le_inter_omega
      (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i hn0 hnc0)
    rwa [NilesRankOneKernel.omegaCenterIn_map_injective _ (G₀ L S).subtype_injective,hD,hV] at hh
  · obtain ⟨A,hA,hout,houtX,hquad,hbound⟩ := source_replacement_quadratic_offender
      (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h) i hn0 hnc0
    refine ⟨A.map f,?_,?_,?_,?_,?_⟩
    · have hh := Glauberman.maximum_abelian_map_of_injective f (G₀ L S).subtype_injective hA
      rwa [core_image h i] at hh
    · intro ha
      apply hout
      intro a ha'
      have hh := ha (mem_map_of_mem f ha')
      rw [←core_image h (other i)] at hh
      obtain ⟨a',ha',he⟩ := hh
      exact (G₀ L S).subtype_injective he ▸ ha'
    · intro ha
      apply houtX
      intro a ha'
      have hh := ha (mem_map_of_mem f ha')
      rw [←hX,←map_pCoreIn_of_injective 2 X f (G₀ L S).subtype_injective] at hh
      obtain ⟨a',ha',he⟩ := hh
      exact (G₀ L S).subtype_injective he ▸ ha'
    · have hh := congrArg (Subgroup.map f) hquad
      rwa [map_commutator,map_commutator,hV,Subgroup.map_bot] at hh
    · have hc := map_inf_centralizer_of_injective f (G₀ L S).subtype_injective V A
      rw [hV] at hc
      rw [←relIndex_map_map_of_injective (V ⊓ centralizer (A : Set (G₀ L S))) V
        (G₀ L S).subtype_injective,
        ←relIndex_map_map_of_injective ((P (other i)).pCoreIn 2) A (G₀ L S).subtype_injective,
        ←hc,hV,core_image h (other i)] at hbound
      exact hbound


/-- The actual reduced F1.11 replacement action retains its literal
centralizer quotient and coordinates; no core-kernel identification is assumed. -/
theorem reduced_replacement_faithful_action (h : HypothesisF11 L S) (i : Fin 2)
    (hn : localEnlargement (Classical.choice ((reduced_triple h).local_data (other i))) ≤
      normalizer (↑(((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2 ⊓
        ((P₀ L S (other i)).subgroupOf (G₀ L S)).pCoreIn 2) : Set (G₀ L S)))
    (hnc : ¬ sylowCenterSpan ((P₀ L S (other i)).subgroupOf (G₀ L S)) ≤ centralizer
      (conjugateSpanBy (((P₀ L S i).subgroupOf (G₀ L S)).pCoreIn 2)
        ((P₀ L S (other i)).subgroupOf (G₀ L S)) : Set (G₀ L S))) :
    let P := fun j => (P₀ L S j).subgroupOf (G₀ L S)
    let X := conjugateSpanBy ((P i).pCoreIn 2) (P (other i))
    let V := conjugateSpanBy (sylowCenterSpan (P i)) X
    ∃ hE : IsElementaryAbelian 2 (V.subgroupOf X),
      letI := hE
      ∃ (K : Subgroup X) (hK : K.Normal),
        letI := hK
        ∃ σ : Representation (ZMod 2) (X ⧸ K) (Additive (V.subgroupOf X)),
          K = (centralizer (V : Set (G₀ L S))).subgroupOf X ∧ Function.Injective σ ∧
            Nonempty (Representation.BinaryConjugationSection X V ⊥
              (σ.comp (QuotientGroup.mk' K))) := by
  exact source_replacement_faithful_action (reduced_triple h) (reduced_borel_core_sylow h)
    (reduced_vertex_sylow h) i
    ((inter_core_local_normal_iff (reduced_triple h) i _).mp hn) hnc

end CFSG.Quasithin.ChapterF.Source.DGS85.Reduction
