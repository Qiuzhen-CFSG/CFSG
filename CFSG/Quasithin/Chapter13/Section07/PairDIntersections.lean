module

public import CFSG.Quasithin.Chapter13.Section07.PairNatural
public import CFSG.Quasithin.Chapter13.Section07.PairTransport

/-!
# The original D-intersections lie in the elementary intersection

F.9 bounds the commutators of D_H with each generating span by the
appropriate point. Hence its image in O₂(I)/ZI is fixed by I. In the
proved natural section that image belongs to both marked complementary
factor spaces, so it is zero. The source square condition exchanges the
two original D-intersections and preserves ZI, giving the other inclusion.
Normality of ZI then contains both entire I-spans.

This proves the inclusion in 13.7.10(5) needed by the subsequent E-intersection
argument. It does not yet assert the finer product formula of (5). The last
consumer constructs the original g and retains its nonorthogonality marking.
No earlier faithfulness on U_H/C_UH(Q_H), natural-section witness or
intersection-containment conclusion is assumed.
Source: Aschbacher–Smith, 13.7.10(5)–(7), printed pp.941–942.
-/

@[expose] public section

open Subgroup InvertedCubicTensor
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}
  (d : NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

/-- The actual intersection is an elementary invariant layer of the pair. -/
theorem pair_intersection_layer
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let I:=A⊔B
    let E:=A⊓B
    V≤E ∧ E≤I.pCoreIn 2 ∧ I≤normalizer (E:Set G) ∧
      ⁅E,I⁆≤V ∧ IsElementaryAbelian 2 E := by
  dsimp only
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let E:=A⊓B
  let J:ChapterG.Section02.Setup G:=⟨V,V₁,L,T,H⟩
  have hAX:A≤X:=(VH_le_core d h hU).trans (h.QH_le_T.trans le_sup_right)
  have hBX:B≤X := by
    rintro _ ⟨a,ha,rfl⟩
    change (g:G)⁻¹*a*((g:G)⁻¹)⁻¹∈X
    rw [inv_inv]
    exact mul_mem (mul_mem (X.inv_mem g.property) (hAX ha)) g.property
  have hIX:I≤X:=sup_le hAX hBX
  have hp:IsPGroup 2 A:=(pCore_isPGroup.map H.subtype).to_le (VH_le_core d h hU)
  obtain ⟨hVE,hES,hEN,hEI,hEA⟩:=J.rank_one_intersection_layer (g:G) hp
    (frattini_VH_le_point d h hU) (h.point_lt.le.trans h.plus_le)
    (hIX.trans d.normalizes_V) (d.normalizes_V g.property) (chosen_points_disjoint h (g:G) hout)
  exact ⟨hVE,hES,(normal_subgroupOf_iff_le_normalizer
    (show E≤I from inf_le_left.trans le_sup_left)).mp hEN,hEI,hEA⟩

/-- The actual first D-intersection has zero image in the natural pair quotient. -/
theorem pair_D_le_intersection
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).DH (g:G)≤
      Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G) := by
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let X:=L⊔(T:Subgroup G)
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let S:=I.pCoreIn 2
  let E:=A⊓B
  let Q:=X.pCoreIn 2
  let D:=F.DH (g:G)
  have hUA:F.UH≤A:=conjugateSpanBy_mono h.plus_le le_rfl
  have hUQ:F.UH≤Q:=(le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  obtain ⟨hcore,_⟩:=pair_twoCore_quotient d h hU hV g hout
  change S=I⊓Q at hcore
  have hDS:D≤S:=hcore.ge.trans' (le_inf (inf_le_left.trans (hUA.trans le_sup_left)) (inf_le_left.trans hUQ))
  obtain ⟨hVE,_,hnE,_,_⟩:=pair_intersection_layer d h hU g hout
  change V≤E at hVE
  change I≤normalizer (E:Set G) at hnE
  have hgV:conjugate V (g:G)=V:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
  have hlineE:conjugate V₁ (g:G)≤E:=
    (map_mono (h.point_lt.le.trans h.plus_le)).trans (hgV.le.trans hVE)
  obtain ⟨_,_,_,hDgA⟩:=ConjugateIntersections.lemma_13_7_10_six h g hs hUQ hout
    (centralizer_UH_commutator d h)
  have hDB:⁅D,B⁆≤conjugate V₁ (g:G) := by
    have hm:=map_mono (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom) hDgA
    rw [map_commutator] at hm
    change ⁅conjugate (F.DHg (g:G)) (g:G),B⁆≤conjugate V₁ (g:G) at hm
    rw [(h.intersection_exchange_of_core_quotient_square g hs).2.1] at hm
    exact hm
  have hDA:⁅D,A⁆=⊥:=commutator_eq_bot_iff_le_centralizer.mpr
    (le_centralizer_iff.mp (((VH_centralizes_UH d h hU).trans inf_le_right).trans
      (centralizer_le (show D≤F.UH from inf_le_left))))
  have hIE:⁅I,D⁆≤E := by
    have hAa:A≤commutatorPreimage I D E:=le_commutatorPreimage le_sup_left
      (by rw [commutator_comm,hDA];exact bot_le)
    have hBb:B≤commutatorPreimage I D E:=le_commutatorPreimage le_sup_right
      (by rw [commutator_comm];exact hDB.trans hlineE)
    exact (commutator_mono (sup_le hAa hBb) le_rfl).trans
      (commutator_commutatorPreimage_le I D E hnE)
  obtain ⟨x,hx,_,_⟩:=pair_internal_source_subgroups d h hU hV g hout
  obtain ⟨hN,hEA,e,σ,c,_,_,hcompl,_,_⟩:=pair_natural_quotient d h hU hV g hout
  intro z hz
  let zS:S:=⟨z,hDS hz⟩
  have hzW:z∈A⊓Q:=⟨hUA hz.1,hUQ hz.1⟩
  have hzspace:(c.coordinates zS).toAdd∈c.imageSpace (A⊓Q):=
    (c.mem_imageSpace_iff _ _).mpr ⟨zS,hzW,rfl⟩
  have hfix: (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 I)))) x
      (c.coordinates zS).toAdd=(c.coordinates zS).toAdd:=
    c.fixed_on_imageSpace_of_commutator_le I D hIE x x.property _
      ((c.mem_imageSpace_iff _ _).mpr ⟨zS,hz,rfl⟩)
  let yS:S:=⟨(x:G)*z*(x:G)⁻¹,(mem_normalizer_iff.mp (c.normalized x.property) z).mp zS.property⟩
  have hyB:(yS:G)∈B := by
    have hx':B=A.conjBy (x:G):=hx
    rw [hx']
    exact ⟨z,hUA hz.1,rfl⟩
  have hyQ:(yS:G)∈Q:=hcore.le yS.property |>.2
  have hycoord:(c.coordinates yS).toAdd=(c.coordinates zS).toAdd:=
    (c.equivariant x zS).trans hfix
  have hzother:(c.coordinates zS).toAdd∈c.imageSpace (B⊓Q):=
    (c.mem_imageSpace_iff _ _).mpr ⟨yS,⟨hyB,hyQ⟩,hycoord⟩
  have hz0:(c.coordinates zS).toAdd=0:=by
    have hmem:(c.coordinates zS).toAdd∈c.imageSpace (A⊓Q)⊓c.imageSpace (B⊓Q):=⟨hzspace,hzother⟩
    have hb:c.imageSpace (A⊓Q)⊓c.imageSpace (B⊓Q)=⊥:=hcompl.inf_eq_bot
    rw [hb,Submodule.mem_bot] at hmem
    exact hmem
  exact (c.coordinates_eq_one_iff zS).mp (Multiplicative.toAdd.injective hz0)
/-- Both literal D-intersections, and their entire I-spans, lie in ZI.
This is the invariant-intersection conclusion used in 13.7.10(5)–(7). -/
theorem pair_D_spans_le_intersection
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V))
    (g : (L⊔(T:Subgroup G):Subgroup G))
    (hs : (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout : ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let A:=Section08.Source.VH H V
    let B:=conjugate A (g:G)
    let I:=A⊔B
    let E:=A⊓B
    F.DH (g:G)≤E ∧ F.DHg (g:G)≤E ∧
      conjugateSpanBy (F.DH (g:G)) I≤E ∧ conjugateSpanBy (F.DHg (g:G)) I≤E := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let A:=Section08.Source.VH H V
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let E:=A⊓B
  have hD:F.DH (g:G)≤E:=pair_D_le_intersection d h hU hV g hs hout
  have hswap:=h.intersection_exchange_of_core_quotient_square g hs
  have htwice:conjugate B (g:G)=A:=h.conjugate_twice_eq_of_square
    (le_normalizer_conjugateSpanBy V H) (h.square_mem_local_of_core_quotient_square g hs)
  have hEE:conjugate E (g:G)=E := by
    change (A⊓B).map (MulAut.conj (g:G)⁻¹).toMonoidHom=E
    rw [map_inf _ _ _ (MulAut.conj (g:G)⁻¹).injective]
    change B⊓conjugate B (g:G)=A⊓B
    rw [htwice,inf_comm]
  have hDg:F.DHg (g:G)≤E := by
    have hm:=map_mono (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom) hD
    change conjugate (F.DH (g:G)) (g:G)≤conjugate E (g:G) at hm
    rw [hswap.1,hEE] at hm
    exact hm
  have hn:I≤normalizer (E:Set G):=(pair_intersection_layer d h hU g hout).2.2.1
  exact ⟨hD,hDg,conjugateSpanBy_le hD hn,conjugateSpanBy_le hDg hn⟩

/-- A source-constructed g supplies both original D-spans inside ZI. -/
theorem exists_source_pair_D_spans
    (h : (ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU : IsMulCommutative (Section08.Source.UH H V₃))
    (hV : ¬ IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let A:=Section08.Source.VH H V
      let B:=conjugate A (g:G)
      conjugateSpanBy (F.DH (g:G)) (A⊔B)≤A⊓B ∧
      conjugateSpanBy (F.DHg (g:G)) (A⊔B)≤A⊓B := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  exact ⟨g,hs,hspan,(pair_D_spans_le_intersection d h hU hV (inclusion le_sup_left g) hs hout).2.2⟩
end CFSG.Quasithin.Chapter13.Section07
