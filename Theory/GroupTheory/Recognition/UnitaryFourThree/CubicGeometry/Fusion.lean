module

public import Theory.GroupTheory.MaximumAbelianFusion
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicLine.MaximumAbelian

/-!
# Original cubic kernel fusion in its normalizer

The same independent cubic axes give the unique maximum-order abelian V
inside the actual Sylow product VD. This makes V weakly closed and gives
literal normalizer fusion of every pair of its subgroups. The extraspecial
odd kernel and Sylow placement are the preceding45.8 source outputs.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G} (h:IsType z)
include h in
theorem cubic_kernel_source_fusion (P:Sylow 3 (centralizer z))
    (actors:QuaternionIndependentCubics h.toCentralizerHypothesis.factorData.leftCore
      h.toCentralizerHypothesis.factorData.rightCore)
    (ha:actors.A=(P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (hsplit:normalizer (zpowers (actors.x:G):Set G)=CubicLine.oddKernel (zpowers (actors.x:G))⊔
      (normalizer (zpowers (actors.x:G):Set G)⊓centralizer z))
    (hD:Nat.card (CubicLine.oddKernel (zpowers (actors.x:G)))=243)
    (he:IsExtraspecial 3 (CubicLine.oddKernel (zpowers (actors.x:G))))
    (T:Sylow 3 G)
    (hT:(T:Subgroup G)=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊔
      CubicLine.oddKernel (zpowers (actors.x:G))) :
    let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
    (∀g:G,V.map (MulAut.conj g).toMonoidHom≤(T:Subgroup G)→g∈normalizer (V:Set G)) ∧
    (normalizer (T:Set G)≤normalizer (V:Set G)) ∧
    ∀B C:Subgroup G,B≤V→C≤V→∀g:G,B.map (MulAut.conj g).toMonoidHom=C→
      ∃n∈normalizer (V:Set G),B.map (MulAut.conj n).toMonoidHom=C := by
  let V:=CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype)
  obtain ⟨hV,hc⟩:=h.original_cubic_kernel_eighty_one P
  let :IsMulCommutative V:=hV.toIsMulCommutative
  have hVT:V≤(T:Subgroup G):=by rw [hT];exact le_sup_left
  have hm (B:Subgroup G) (hB:IsMulCommutative B) (hBT:B≤(T:Subgroup G))
      (hcard:Nat.card V≤Nat.card B):B=V:=by
    apply (h.cubic_line_marked_maximum_abelian P actors ha hsplit hD he B hB (hBT.trans_eq hT)).2
    exact hc ▸ hcard
  have hw:=T.weakly_closed_of_unique_maximum_abelian V hm
  refine ⟨hw,?_,?_⟩
  · intro g hg
    apply hw g
    exact (map_mono hVT).trans_eq (mem_normalizer_iff_map_conj_eq.mp hg)
  · exact T.subgroup_fusion_of_unique_maximum_abelian V hVT hm
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
