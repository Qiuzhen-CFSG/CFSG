module

public import CFSG.Quasithin.Chapter13.Section07.PairGeneration
public import CFSG.Quasithin.Chapter13.Section07.PairDProduct
public import CFSG.Quasithin.Chapter13.Section07.PairEIntersections
public import Theory.GroupTheory.TwoLocalUniquenessControl

/-!
# The fixed subgroup meets the pair intersection in the original point

The subgroup U₀∩U_H^g is centralized by the original two spans and O₂(H),
and normalized by O₂(LT). The actual pair-generation theorem therefore
makes its full normalizer contain LT. Maximal-local uniqueness and the
component from 13.7.16 exclude a nontrivial intersection. The proved
D-product and E-intersection then give Z_I∩U₀=V₁. Finally [U_H,A] and
V₃ both lie in Z_I, proving the second clause of 13.7.17.

The surviving inputs are genuine earlier maximal-local uniqueness,
13.7.16(2) centralization by the original K, and its 13.3.9 escape from M.
No pair-generation, fixed-intersection or commutator-placement conclusion
is assumed. Source: Aschbacher–Smith 13.7.17, printed p.944.
-/

public section
open Subgroup
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter13.Section07
open Section08.SourceCompletion ChapterF.Section09.Setup
variable {G:Type*} [Group G] [Finite G]
  {T:Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

omit d in
private theorem core_normalizes_conjugate
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (g:(L⊔(T:Subgroup G):Subgroup G)) (A:Subgroup G)
    (hn:H≤normalizer (A:Set G)) :
    (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2≤normalizer (conjugate A (g:G):Set G) := by
  let X:=L⊔(T:Subgroup G)
  let Q:=X.pCoreIn 2
  have hQH:Q≤H:=(h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H
  have hnQ:X≤normalizer (Q:Set G):=X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hq:Q.map (MulAut.conj (g:G)⁻¹).toMonoidHom=Q:=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (Q:Set G)).inv_mem (hnQ g.property))
  have hh:=map_mono (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom) (hQH.trans hn)
  rw [hq,map_normalizer_eq_of_bijective A (MulAut.conj (g:G)⁻¹).bijective] at hh
  exact hh

/-- The first step in 13.7.17: the fixed subgroup and opposite seed span
are disjoint, with the source generation and full normalizer bound proved. -/
theorem pair_fixed_disjoint_conjugate
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hne:⁅V₃,Section08.Source.QH H⁆≠⊥)
    (hunique:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (hK:K≤centralizer ((Section08.Source.UH H V₃⊓centralizer (Section08.Source.QH H:Set G):Subgroup G):Set G))
    (hKM:¬K≤M)
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    (Section08.Source.UH H V₃⊓centralizer (Section08.Source.QH H:Set G))⊓
      conjugate (Section08.Source.UH H V₃) (g:G)=⊥ := by
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let U:=F.UH
  let U₀:=U⊓centralizer (F.QH:Set G)
  let Ug:=conjugate U (g:G)
  let U₁:=U₀⊓Ug
  let A:=F.VH
  let B:=conjugate A (g:G)
  let I:=A⊔B
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  have hQH:Q≤H:=(h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H
  have hHU:H≤normalizer (U:Set G):=le_normalizer_conjugateSpanBy V₃ H
  have hHQ:H≤normalizer (F.QH:Set G):=Hypothesis.H_normalizes_QH (D:=F)
  have hHU₀:H≤normalizer (U₀:Set G):=
    (le_inf hHU (hHQ.trans (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  have hQUg:Q≤normalizer (Ug:Set G):=core_normalizes_conjugate h g U hHU
  have hQU₁:Q≤normalizer (U₁:Set G):=
    (le_inf (hQH.trans hHU₀) hQUg).trans inf_normalizer_le_normalizer_inf
  have hAU:A≤centralizer (U:Set G):=(VH_centralizes_UH d h hU).trans inf_le_right
  have hBUg:B≤centralizer (Ug:Set G) := by
    have hh:=map_mono (f:=(MulAut.conj (g:G)⁻¹).toMonoidHom) hAU
    exact hh.trans (map_centralizer_le_centralizer_image (U:Set G)
      (MulAut.conj (g:G)⁻¹).toMonoidHom)
  have hIU₁:I≤centralizer (U₁:Set G):=sup_le
    (hAU.trans (centralizer_le (inf_le_left.trans inf_le_left)))
    (hBUg.trans (centralizer_le inf_le_right))
  have hQHU₁:F.QH≤centralizer (U₁:Set G):=
    le_centralizer_iff.mp (inf_le_left.trans inf_le_right)
  have hXU₁:L⊔(T:Subgroup G)≤normalizer (U₁:Set G) := by
    rw [←pair_core_generate d h hU hV hne g hout]
    exact sup_le ((sup_le hIU₁ hQHU₁).trans (Subgroup.centralizer_le_normalizer _)) hQU₁
  by_contra hbad
  have hlocal:normalizer (U₁:Set G)≤M:=normalizer_le_of_unique_maximalTwoLocal hunique
    ((isPGroup_pCoreIn 2 H).to_le ((inf_le_left.trans inf_le_left).trans h.UH_le_QH)) hbad hXU₁
  exact hKM (hK.trans ((centralizer_le inf_le_left).trans
    ((Subgroup.centralizer_le_normalizer _).trans hlocal)))

/-- Original 13.7.17(1), on the literal paired intersection and fixed group. -/
theorem pair_intersection_fixed_eq_point
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (hV:¬IsMulCommutative (Section08.Source.VH H V))
    (hne:⁅V₃,Section08.Source.QH H⁆≠⊥)
    (hunique:∀N:Subgroup G,IsMaximalTwoLocal N→L⊔(T:Subgroup G)≤N→N=M)
    (hK:K≤centralizer ((Section08.Source.UH H V₃⊓centralizer (Section08.Source.QH H:Set G):Subgroup G):Set G))
    (hKM:¬K≤M)
    (g:(L⊔(T:Subgroup G):Subgroup G))
    (hs:(QuotientGroup.mk' (pCore 2 (L⊔(T:Subgroup G):Subgroup G)) g)^2=1)
    (hout:¬conjugate V₁ (g:G)≤Section08.Source.UH H V₃) :
    (Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G))⊓
      (Section08.Source.UH H V₃⊓centralizer (Section08.Source.QH H:Set G))=V₁ := by
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let E:=F.VH⊓conjugate F.VH (g:G)
  let D:=F.DH (g:G)
  let Dg:=F.DHg (g:G)
  let U₀:=F.UH⊓centralizer (F.QH:Set G)
  have hpU₀:V₁≤U₀:=le_inf (h.point_lt.le.trans (le_conjugateSpanBy V₃ H))
    (le_centralizer_iff.mp ((pCoreIn_le 2 H).trans h.H_centralizes))
  have hpE:V₁≤E:=(h.point_lt.le.trans h.plus_le).trans (pair_intersection_layer d h hU g hout).1
  have he:F.EH (g:G)=E:=(pair_E_intersections d h hU hV g hs hout).1
  obtain ⟨_,hDgE,_,_⟩:=pair_D_spans_le_intersection d h hU hV g hs hout
  have hEA:IsElementaryAbelian 2 E:=(pair_intersection_layer d h hU g hout).2.2.2.2
  let :IsElementaryAbelian 2 E:=hEA
  have hn:V₁≤normalizer (Dg:Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    intro z hz y hy
    exact congrArg Subtype.val (mul_comm (⟨y,hDgE hy⟩:E) ⟨z,hpE hz⟩)
  have hspan:conjugateSpanBy D (F.VH⊔conjugate F.VH (g:G))=Dg⊔V₁:=
    (pair_D_span_formula d h hU hV g hs hout).2.2.1
  have hdis:=pair_fixed_disjoint_conjugate d h hU hV hne hunique hK hKM g hout
  change U₀⊓conjugate F.UH (g:G)=⊥ at hdis
  apply le_antisymm _ (le_inf hpE hpU₀)
  intro x hx
  have hxD:x∈D := by
    have hxE:x∈F.EH (g:G):=he.symm ▸ hx.1
    exact ⟨hx.2.1,hxE.2⟩
  have hxspan:x∈Dg⊔V₁:=hspan ▸ le_conjugateSpanBy D _ hxD
  change x∈((Dg⊔V₁:Subgroup G):Set G) at hxspan
  rw [coe_mul_of_right_le_normalizer_left _ _ hn] at hxspan
  obtain ⟨a,ha,b,hb,hab⟩:=hxspan
  change a*b=x at hab
  have haU₀:a∈U₀ := by
    have heq:a=x*b⁻¹:=by rw [←hab];group
    rw [heq]
    exact U₀.mul_mem hx.2 (U₀.inv_mem (hpU₀ hb))
  have ha1:a=1 := by
    have hh:a∈U₀⊓conjugate F.UH (g:G):=⟨haU₀,ha.1⟩
    rw [hdis] at hh
    exact hh
  rw [ha1,one_mul] at hab
  exact hab ▸ hb

/-- The actual commutator in 13.7.17(2) already lies in the paired intersection. -/
theorem pair_seed_actor_commutator_le_intersection
    (h:(ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (hU:IsMulCommutative (Section08.Source.UH H V₃))
    (g:(L⊔(T:Subgroup G):Subgroup G)) :
    ⁅Section08.Source.UH H V₃,conjugate (Section08.Source.VH H V) (g:G)⊓
      (L⊔(T:Subgroup G):Subgroup G).pCoreIn 2⁆≤
      Section08.Source.VH H V⊓conjugate (Section08.Source.VH H V) (g:G) := by
  let F:=ConjugateIntersections.sourceSetup T L V V₃ V₁ H
  let Q:=(L⊔(T:Subgroup G):Subgroup G).pCoreIn 2
  let B:=conjugate F.VH (g:G)
  have hUQ:F.UH≤Q:=(le_conjugateSpanBy _ L).trans (span_UH_L_le_core d h hU)
  have hUA:F.UH≤F.VH:=conjugateSpanBy_mono h.plus_le le_rfl
  have hQH:Q≤H:=(h.sylow_centralizer.symm.le.trans inf_le_left).trans h.T_le_H
  have hQA:Q≤normalizer (F.VH:Set G):=hQH.trans (le_normalizer_conjugateSpanBy V H)
  have hQB:Q≤normalizer (B:Set G):=core_normalizes_conjugate h g _ (le_normalizer_conjugateSpanBy V H)
  exact le_inf
    ((commutator_mono hUA inf_le_right).trans (le_normalizer_iff_commutator_le_left.mp hQA))
    ((commutator_mono hUQ inf_le_left).trans (le_normalizer_iff_commutator_le_right.mp hQB))

end CFSG.Quasithin.Chapter13.Section07
