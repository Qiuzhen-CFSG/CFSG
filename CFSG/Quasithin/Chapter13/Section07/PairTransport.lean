module

public import CFSG.Quasithin.Chapter13.Section07.PairCoreFactors

/-!
# Preserving all source markings under internal conjugacy

The nonabelian full span has Frattini subgroup equal to the original line.
Its normalizer inside LT therefore fixes that line and lies in H. Thus the
internal pair conjugator differs from the original g by an element of H.
It consequently carries every H-normalized subgroup to its original
conjugate, including the seed span and the local two-core.

This prevents a loss of markings when applying the natural S₃ section to
13.7.10(4)–(7). The final consumer retains the three literal source groups.
Source: Aschbacher–Smith, 13.7.9–10, printed pp.941–942.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The original point recovers the local normalizer of the full span. -/
theorem span_normalizer_in_LT_le_H
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    (L⊔(T:Subgroup G))⊓normalizer (Section08.Source.VH H V:Set G)≤H := by
  have hf: (frattini (Section08.Source.VH H V)).map (Section08.Source.VH H V).subtype=V₁:=
    (abelian_or_frattini_eq_point d h hU).resolve_left hV
  have hn:normalizer (Section08.Source.VH H V:Set G)≤normalizer (V₁:Set G) := by
    rw [←hf]
    exact normalizer_le_normalizer_characteristic_image _ _
  intro y hy
  exact h.local_le (h.normalizer_point_LT_eq ▸ (show y∈(L⊔(T:Subgroup G))⊓normalizer (V₁:Set G) from ⟨hy.1,hn hy.2⟩))

/-- An internal conjugator can be chosen in the same right H-coset as g⁻¹. -/
theorem pair_internal_H_coset
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    ∃x:(Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G):Subgroup G),
      (g:G)*(x:G)∈H := by
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  have hAX:A≤X:=(VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hBX:B≤X := by
    rintro _ ⟨a,ha,rfl⟩
    change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact mul_mem (mul_mem (X.inv_mem g.property) (hAX ha)) g.property
  have hIX:I≤X:=sup_le hAX hBX
  obtain ⟨x,hx⟩:=pair_internal_conjugator d h hU hV g hout
  refine ⟨x,span_normalizer_in_LT_le_H d h hU hV ⟨mul_mem g.property (hIX x.property),?_⟩⟩
  change (g:G)*(x:G)∈normalizer (A:Set G)
  rw [mem_normalizer_iff_map_conj_eq]
  change A.conjBy ((g:G)*(x:G))=A
  rw [conjBy_mul,←hx]
  exact conjBy_inv' A (g:G)

omit d [Finite G] in
private theorem pair_transport_of_coset (K H:Subgroup G) (hn:H≤normalizer (K:Set G))
    (g x:G) (hmem:g*x∈H) : conjugate K g=K.conjBy x := by
  have he:K.conjBy (g*x)=K:=mem_normalizer_iff_map_conj_eq.mp (hn hmem)
  have hh:=congrArg (fun B:Subgroup G=>B.conjBy g⁻¹) he
  rw [conjBy_conjBy,inv_mul_cancel_left] at hh
  exact hh.symm

/-- One internal conjugator retains every subgroup normalized by H. -/
theorem pair_internal_marked_conjugator
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    ∃x:(Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G):Subgroup G),
      (g:G)*(x:G)∈H ∧
      ∀K:Subgroup G,H≤normalizer (K:Set G)→conjugate K (g:G)=K.conjBy (x:G) := by
  obtain ⟨x,hx⟩:=pair_internal_H_coset d h hU hV g hout
  exact ⟨x,hx,fun K hn=>pair_transport_of_coset K H hn (g:G) (x:G) hx⟩
/-- The literal full span, seed span and two-core are all transported by
one internal conjugator. These are the original 13.7.10 markings. -/
theorem pair_internal_source_subgroups
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    ∃x:(Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G):Subgroup G),
      conjugate (Section08.Source.VH H V) (g:G)=(Section08.Source.VH H V).conjBy (x:G) ∧
      conjugate (Section08.Source.UH H V₃) (g:G)=(Section08.Source.UH H V₃).conjBy (x:G) ∧
      conjugate (H.pCoreIn 2) (g:G)=(H.pCoreIn 2).conjBy (x:G) := by
  obtain ⟨x,_,hx⟩:=pair_internal_marked_conjugator d h hU hV g hout
  exact ⟨x,hx _ (le_normalizer_conjugateSpanBy V H),
    hx _ (le_normalizer_conjugateSpanBy V₃ H),
    hx _ (H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))⟩

end CFSG.Quasithin.Chapter13.Section07
