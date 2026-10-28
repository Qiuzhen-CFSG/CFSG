module

public import CFSG.Quasithin.Chapter13.Section07.PairEIntersections
public import Theory.Representation.BinaryConjugationSection.tensorChief
public import Theory.Representation.BinaryConjugationSection.ImageDimensions
public import Theory.Representation.InvertedCubicTensor.naturalChief
public import Theory.Representation.Quotient
public import Mathlib.Data.Nat.Log

/-!
# Exact chief count on the original natural pair layer

The literal O₂(I)/E tensor gives an actual chief refinement. Its two core
factor images have equal dimensions: the original square-mod-core conjugator
exchanges them while preserving E. Complementarity identifies that common
dimension with the tensor multiplicity. The proved E=V_Hᵍ∩Q_H identity then
identifies it with m(A*), using the actual H/O₂(H) quotient map.

Every chief series between these endpoints has this count. This supplies
the natural-layer contribution in original 13.7.10(8). The additional point
plane and the comparison with the original L₁ remain separate obligations.
Source: Aschbacher--Smith, 13.7.10(8), printed p.942.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement InvertedCubicTensor
open scoped IsMulCommutative TensorProduct
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The actual natural layer contributes exactly m(A*) noncentral chief factors. -/
theorem pair_natural_chief_count
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A := Section08.Source.VH H V
    let B := conjugate A (g:G)
    let I := A⊔B
    let E := A⊓B
    let Q := (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
    let Astar := (((B⊓Q).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
    ∃ s : ChiefSeries I, s.head.val = E.subgroupOf I ∧
      s.last.val = pCore 2 I ∧ s.length = Nat.log 2 (Nat.card Astar) ∧
      s.noncentralTwoCount = Nat.log 2 (Nat.card Astar) := by
  dsimp only
  let F := ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let A := F.VH
  let B := conjugate A (g:G)
  let I := A⊔B
  let E := A⊓B
  let S := I.pCoreIn 2
  let Q := (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let W := A⊓Q
  let Y := B⊓Q
  let Astar := (Y.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))
  obtain ⟨hN,hEA,e,σ,c,hcoord,hfin,hcompl,⟨j,hj⟩,_⟩ := pair_natural_quotient d h hU hV g hout
  let := hN
  let := hEA
  let := hfin
  let π : I →* S₃ := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let τ := (BinaryPermutation.coreRepresentation (Fin 3)).comp π
  let inst : Representation.IsIrreducible τ :=
    (Representation.irreducible_comp_surjective_iff π hπ _).mpr natural_irreducible
  have hτ : ∃ a v, τ a v ≠ v := by
    obtain ⟨a,v,hv⟩ := natural_noncentral
    obtain ⟨a,rfl⟩ := hπ a
    exact ⟨a,v,hv⟩
  have hj' : ∀ a z, j (Representation.tprod (Representation.trivial (ZMod 2) I
      (multiplicitySpace σ)) τ a z) = (σ.comp π) a (j z) := fun a z => hj (π a) z
  obtain ⟨s,h0,h1,hl,hc⟩ := @Representation.BinaryConjugationSection.exists_tensor_chief_refinement _ _ _ _ _ _ _ _ _ c _ _ _ _ _ _ _ τ j hj' inst hτ
  have hS : S=W⊔Y := pair_twoCore_factorization d h hU hV g hout
  have hWS : W≤S := hS.symm ▸ (show W≤W⊔Y from le_sup_left)
  have hYS : Y≤S := hS.symm ▸ (show Y≤W⊔Y from le_sup_right)
  have hEq : E≤Q := (pair_intersection_layer d h hU g hout).2.1.trans
    ((pair_twoCore_quotient d h hU hV g hout).1.le.trans inf_le_right)
  have hgQ : conjugate Q (g:G)=Q := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (Q:Set G)).inv_mem
      (((L⊔(T:Subgroup G)).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image _ (pCore 2 (L⊔(T:Subgroup G):Subgroup G)))) g.property))
  have hWg : conjugate W (g:G)=Y := by
    change (A⊓Q).map (MulAut.conj (g:G)⁻¹).toMonoidHom=B⊓Q
    rw [map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective]
    exact congrArg (B⊓·) hgQ
  have hEg : conjugate E (g:G)=E := by
    change (A⊓B).map (MulAut.conj (g:G)⁻¹).toMonoidHom=A⊓B
    rw [map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective]
    change B⊓conjugate B (g:G)=A⊓B
    have htwice : conjugate B (g:G)=A := h.conjugate_twice_eq_of_square
      (le_normalizer_conjugateSpanBy V H) (h.square_mem_local_of_core_quotient_square g hs)
    rw [htwice,inf_comm]
  have hind : E.relIndex W=E.relIndex Y := by
    have he := relIndex_map_map_of_injective (f := (MulAut.conj (g:G)⁻¹).toMonoidHom) E W (MulAut.conj (g:G)⁻¹).injective
    change (conjugate E (g:G)).relIndex (conjugate W (g:G))=E.relIndex W at he
    rw [hEg,hWg] at he
    exact he.symm
  have hdim : Module.finrank (ZMod 2) (c.imageSpace W)=
      Module.finrank (ZMod 2) (c.imageSpace Y) := by
    have he := (c.imageSpace_card_eq_relIndex W hWS).trans
      (hind.trans (c.imageSpace_card_eq_relIndex Y hYS).symm)
    rw [Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=c.imageSpace W),
      Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=c.imageSpace Y),Nat.card_zmod] at he
    exact Nat.pow_right_injective (by decide : 1<2) he
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  change Module.finrank (ZMod 2) (c.imageSpace W)+Module.finrank (ZMod 2) (c.imageSpace Y)=_ at hsum
  have hfull := j.finrank_eq
  rw [Module.finrank_tensorProduct,natural_finrank] at hfull
  have hmult : Module.finrank (ZMod 2) (multiplicitySpace σ)=
      Module.finrank (ZMod 2) (c.imageSpace Y) := by omega
  have hAH : Y≤H := inf_le_right.trans
    ((h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H)
  have hEY : E=Y⊓F.QH := by
    have he := pair_Eg_eq_intersection d h hU hV g hs hout
    change B⊓F.QH=E at he
    apply le_antisymm
    · exact le_inf (le_inf inf_le_right hEq) (he.symm.le.trans inf_le_right)
    · exact (inf_le_inf inf_le_left le_rfl).trans he.le
  have hcard : Nat.card Astar=E.relIndex Y := by
    rw [hEY,inf_relIndex_left]
    change Nat.card ((Y.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))=F.QH.relIndex Y
    rw [←relIndex_ker,QuotientGroup.ker_mk']
    have he := relIndex_map_map_of_injective (pCore 2 H) (Y.subgroupOf H) H.subtype_injective
    rw [map_subgroupOf_eq_of_le hAH] at he
    exact he.symm
  have hcount : Module.finrank (ZMod 2) (multiplicitySpace σ)=Nat.log 2 (Nat.card Astar) := by
    have he : Nat.card (c.imageSpace Y)=E.relIndex Y := c.imageSpace_card_eq_relIndex Y hYS
    rw [hcard,←he,
      Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=c.imageSpace Y),Nat.card_zmod,Nat.log_pow (by decide)]
    exact hmult
  refine ⟨s,congrArg Subtype.val h0,?_,hl.trans hcount,hc.trans hcount⟩
  change s.last.val=pCore 2 I
  rw [h1]
  change S.subgroupOf I=pCore 2 I
  exact comap_map_eq_self_of_injective I.subtype_injective _

/-- Jordan--Hölder makes the natural-layer count independent of the refinement. -/
theorem pair_natural_chief_count_eq
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃)
    (s : ChiefSeries (Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G):Subgroup G))
    (h0 : s.head.val=(Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G)).subgroupOf
      (Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G)))
    (h1 : s.last.val=pCore 2 (Section08.Source.VH H V⊔conjugate (Section08.Source.VH H V) (g:G):Subgroup G)) :
    s.noncentralTwoCount=Nat.log 2 (Nat.card
      (((conjugate (Section08.Source.VH H V) (g:G)⊓(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)))) := by
  obtain ⟨t,ht0,ht1,_,hc⟩ := pair_natural_chief_count d h hU hV g hs hout
  exact (s.noncentralTwoCount_eq t (Subtype.ext (h0.trans ht0.symm))
    (Subtype.ext (h1.trans ht1.symm))).trans hc

/-- Construct the original conjugator and its exact natural-layer chief count. -/
theorem exists_source_pair_natural_chief_count
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let A := Section08.Source.VH H V
      let B := conjugate A (g:G)
      let I := A⊔B
      let E := A⊓B
      let Q := (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
      let Astar := (((B⊓Q).subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)))
      ∃s:ChiefSeries I,s.head.val=E.subgroupOf I ∧ s.last.val=pCore 2 I ∧
        s.length=Nat.log 2 (Nat.card Astar) ∧ s.noncentralTwoCount=Nat.log 2 (Nat.card Astar) := by
  obtain ⟨g,hs,hspan⟩ := exists_chosen_conjugator d
  have hout := ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,hout,pair_natural_chief_count d h hU hV (inclusion le_sup_left g) hs hout⟩

end CFSG.Quasithin.Chapter13.Section07
