module

public import CFSG.Quasithin.Chapter13.Section07.PairInternalSquare
public import CFSG.Quasithin.Chapter13.Section07.PairSeedComplement

/-!
# The complete original D-span product

The pair centralizes its elementary intersection modulo the original
point plane. Thus the I-span of DH equals DH times the opposite point.
The marked internal conjugator with square in the core exchanges DH with
DHg and the two points. This proves the full product and intersection
formulas on the original subgroups. Their common elementary overgroup
converts the joins into the literal ordered products.
The final consumer constructs the original g and combines the complete
product with the actual seed complement, retaining every source marking.
Source: Aschbacher--Smith13.7.10(5),(9), printed pp.941--942.
-/

public section

open Subgroup
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d
/-- The finer original13.7.10(5) span formula with both literal D-intersections. -/
theorem pair_D_span_formula
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let I:=F.VH⊔conjugate F.VH (g:G)
    let D:=F.DH (g:G)
    let Dg:=F.DHg (g:G)
    conjugateSpanBy D I=D⊔Dg ∧
      conjugateSpanBy D I=D⊔conjugate V₁ (g:G) ∧
      conjugateSpanBy D I=Dg⊔V₁ ∧
      conjugateSpanBy D I=(V₁⊔conjugate V₁ (g:G))⊔(D⊓Dg) := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let I:=F.VH⊔conjugate F.VH (g:G)
  let E:=F.VH⊓conjugate F.VH (g:G)
  let D:=F.DH (g:G)
  let Dg:=F.DHg (g:G)
  let Zg:=conjugate V₁ (g:G)
  let P:=conjugateSpanBy D I
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  obtain ⟨hDE,hDgE,hPE,_⟩:=pair_D_spans_le_intersection d h hU hV g hs hout
  obtain ⟨hVE,_,_,_,hEA⟩:=pair_intersection_layer d h hU g hout
  let :IsElementaryAbelian 2 E:=hEA
  have hpointU:V₁≤F.UH:=h.point_lt.le.trans (le_conjugateSpanBy V₃ H)
  have hgV:conjugate V (g:G)=V:=mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
  have hVQ:V≤conjugate F.QH (g:G) := by
    have hm:=map_mono (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom)
      ((le_conjugateSpanBy V H).trans (VH_le_core d h hU))
    change conjugate V (g:G)≤conjugate F.QH (g:G) at hm
    rwa [hgV] at hm
  have hpointD:V₁≤D:=le_inf hpointU ((h.point_lt.le.trans h.plus_le).trans hVQ)
  have hpointDg:Zg≤Dg := by
    have hm:=map_mono (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom) hpointD
    change Zg≤conjugate D (g:G) at hm
    rw [(h.intersection_exchange_of_core_quotient_square g hs).1] at hm
    exact hm
  have hPt:V₁≤P:=hpointD.trans (le_conjugateSpanBy D I)
  obtain ⟨x,hxs,hx⟩:=pair_internal_square_conjugator d h hU hV g hout
  have hnQ:H≤normalizer (F.QH:Set G):=
    ChapterF.Section09.Setup.Hypothesis.H_normalizes_QH (D:=F)
  have hnx:I≤normalizer (P:Set G):=le_normalizer_conjugateSpanBy D I
  have hPmap:P.conjBy (x:G)=P:=mem_normalizer_iff_map_conj_eq.mp (hnx x.property)
  have hpointH:H≤normalizer (V₁:Set G):=h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  have hpointx:Zg=V₁.conjBy (x:G):=hx V₁ hpointH
  have hZP:Zg≤P := by
    rw [hpointx]
    have hm:=map_mono (f:=(MulAut.conj (x:G)).toMonoidHom) hPt
    exact hm.trans hPmap.le
  have hupper:P≤D⊔Zg := by
    apply conjugateSpanBy_le le_sup_left
    apply le_normalizer_iff_commutator_le_left.mpr
    have hjoin:D⊔Zg≤E:=sup_le hDE (hpointDg.trans hDgE)
    exact ((commutator_mono hjoin le_rfl).trans
      (chosen_intersection_central_layer d h hU g hs)).trans
      (sup_le (hpointD.trans le_sup_left) le_sup_right)
  have hspan:P=D⊔Zg:=le_antisymm hupper (sup_le (le_conjugateSpanBy D I) hZP)
  have hx2H:(x:G)^2∈H:=h.T_le_H ((h.sylow_centralizer.symm.le.trans inf_le_left) hxs)
  have hcorex:(conjugate F.QH (g:G)).conjBy (x:G)=F.QH := by
    rw [hx F.QH hnQ,conjBy_conjBy,←pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (hnQ hx2H)
  have hswap:D.conjBy (x:G)=Dg := by
    change (F.UH⊓conjugate F.QH (g:G)).map (MulAut.conj (x:G)).toMonoidHom=Dg
    rw [map_inf _ _ _ (MulAut.conj (x:G)).injective]
    change F.UH.conjBy (x:G)⊓(conjugate F.QH (g:G)).conjBy (x:G)=Dg
    rw [←hx F.UH (le_normalizer_conjugateSpanBy V₃ H),hcorex]
    rfl
  have hDgP:Dg≤P := by
    rw [←hswap]
    exact (map_mono (f:=(MulAut.conj (x:G)).toMonoidHom) (le_conjugateSpanBy D I)).trans hPmap.le
  have hDD:P=D⊔Dg:=le_antisymm (hspan.le.trans (sup_le le_sup_left (hpointDg.trans le_sup_right)))
    (sup_le (le_conjugateSpanBy D I) hDgP)
  have hlinex:Zg.conjBy (x:G)=V₁ := by
    rw [hpointx,conjBy_conjBy,←pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (hpointH hx2H)
  have hspan':P=Dg⊔V₁ := by
    have hm:=congrArg (fun K:Subgroup G=>K.conjBy (x:G)) hspan
    change P.conjBy (x:G)=(D⊔Zg).map (MulAut.conj (x:G)).toMonoidHom at hm
    rw [hPmap,Subgroup.map_sup] at hm
    change P=D.conjBy (x:G)⊔Zg.conjBy (x:G) at hm
    rwa [hswap,hlinex] at hm
  have hn:V₁≤normalizer (Dg:Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro z hz y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hDgE hy⟩:E) ⟨z,hDE (hpointD hz)⟩)
  have hDform:D=V₁⊔(D⊓Dg) := by
    apply le_antisymm _ (sup_le hpointD inf_le_left)
    intro z hz
    have hp:z∈Dg⊔V₁:=hspan' ▸ le_conjugateSpanBy D I hz
    change z∈((Dg⊔V₁:Subgroup G):Set G) at hp
    rw [coe_mul_of_right_le_normalizer_left Dg V₁ hn] at hp
    obtain ⟨a,ha,b,hb,hab⟩:=hp
    have haD:a∈D := by
      have he:a=z*b⁻¹:=by rw [←hab];group
      rw [he]
      exact D.mul_mem hz (D.inv_mem (hpointD hb))
    rw [←hab]
    exact (V₁⊔(D⊓Dg)).mul_mem (mem_sup_right ⟨haD,ha⟩) (mem_sup_left hb)
  refine ⟨hDD,hspan,hspan',?_⟩
  change P=(V₁⊔Zg)⊔(D⊓Dg)
  calc
    P=D⊔Zg:=hspan
    _=(V₁⊔(D⊓Dg))⊔Zg:=congrArg (·⊔Zg) hDform
    _=(V₁⊔Zg)⊔(D⊓Dg):=by ac_rfl

/-- The original span identity is also the literal ordered product. -/
theorem pair_D_ordered_products
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
    let I:=F.VH⊔conjugate F.VH (g:G)
    let D:=F.DH (g:G)
    let Dg:=F.DHg (g:G)
    (conjugateSpanBy D I:Set G)=(D:Set G)*(Dg:Set G) ∧
      (conjugateSpanBy D I:Set G)=(V₁:Set G)*(conjugate V₁ (g:G):Set G)*((D⊓Dg:Subgroup G):Set G) := by
  dsimp only
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let E:=F.VH⊓conjugate F.VH (g:G)
  let D:=F.DH (g:G)
  let Dg:=F.DHg (g:G)
  let Zg:=conjugate V₁ (g:G)
  obtain ⟨hD,hDg,_,_⟩:=pair_D_spans_le_intersection d h hU hV g hs hout
  obtain ⟨hVE,_,_,_,hEA⟩:=pair_intersection_layer d h hU g hout
  let :IsElementaryAbelian 2 E:=hEA
  have hp:V₁≤E:=(h.point_lt.le.trans h.plus_le).trans hVE
  have hpg:Zg≤E := by
    have hgV:conjugate V (g:G)=V:=mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (V:Set G)).inv_mem (d.normalizes_V g.property))
    exact (map_mono (h.point_lt.le.trans h.plus_le)).trans (hgV.le.trans hVE)
  have norm (A B:Subgroup G) (ha:A≤E) (hb:B≤E):B≤normalizer (A:Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro b hbb a haa
    exact congrArg Subtype.val (mul_comm (⟨a,ha haa⟩:E) ⟨b,hb hbb⟩)
  obtain ⟨hDD,_,_,hform⟩:=pair_D_span_formula d h hU hV g hs hout
  constructor
  · rw [hDD,coe_mul_of_right_le_normalizer_left _ _ (norm D Dg hD hDg)]
  · rw [hform,coe_mul_of_right_le_normalizer_left _ _ (norm (V₁⊔Zg) (D⊓Dg) (sup_le hp hpg) (inf_le_left.trans hD)),
      coe_mul_of_right_le_normalizer_left _ _ (norm V₁ Zg hp hpg)]

/-- A source-constructed original g supplies the full D-product and seed complement. -/
theorem exists_source_pair_D_product_and_complement
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V)) :
    ∃g:L,
      (QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) (inclusion le_sup_left g))^2=1 ∧
      V≤V₃⊔conjugate V₁ (g:G) ∧
      ¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃ ∧
      let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
      let I:=F.VH⊔conjugate F.VH (g:G)
      let D:=F.DH (g:G)
      let Dg:=F.DHg (g:G)
      let W:=conjugate F.UH (g:G)⊓V₃
      (conjugateSpanBy D I:Set G)=(D:Set G)*(Dg:Set G) ∧
      (conjugateSpanBy D I:Set G)=(V₁:Set G)*(conjugate V₁ (g:G):Set G)*((D⊓Dg:Subgroup G):Set G) ∧
      Disjoint V₁ W ∧ V₁⊔W=V₃ ∧ Nat.card W=4 ∧
      W=conjugate V₃ (g:G)⊓V₃ ∧ V₃≤F.VH⊓conjugate F.VH (g:G) := by
  obtain ⟨g,hs,hspan⟩:=exists_chosen_conjugator d
  have hout:=ConjugateIntersections.lemma_13_7_10_one h (g:G) hspan hU hV
  obtain ⟨hprod,hprod'⟩:=pair_D_ordered_products d h hU hV (inclusion le_sup_left g) hs hout
  exact ⟨g,hs,hspan,hout,hprod,hprod',pair_seed_complement d h hU (inclusion le_sup_left g) hs hout⟩

end CFSG.Quasithin.Chapter13.Section07
