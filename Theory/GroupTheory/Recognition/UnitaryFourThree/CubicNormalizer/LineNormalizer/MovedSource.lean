module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Mover
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Opposite
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Complementary
/-!
# The original moved cubic line for45.8

Both reflected fixed lines have the source S4 normalizer quotient. Their
complementarity and the index-three normalizer action produce an actual
conjugate inverted by z. It lies in [V,z], and its full normalizer still
has canonical kernel V of index24. The source marking is chosen before
any subgroup D containing the actual displacement, preserving later axis choices.
Source: Aschbacher, Sporadic Groups (1994),45.7–45.8,pp.245–246.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem reflected_moved_line (R:RootPair z) (h:IsType z)
    (P:Sylow 3 (centralizer z))
    (m:CubicNormalizer.ReflectedMarking z ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (A:Subgroup G) (hA:A≤R.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16) (htA:m.t∈A)
    (ht:m.t∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hs:m.s∈R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype))
    (hTN:R.cubicSylow ((P:Subgroup (centralizer z)).map (centralizer z).subtype)≤normalizer (A:Set G))
    (hlocal:centralizer z⊓normalizer
      ((((P:Subgroup (centralizer z)).map (centralizer z).subtype)⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)=
      centralizer z⊓normalizer ((P:Subgroup (centralizer z)).map (centralizer z).subtype:Set G))
    (D:Subgroup G) (hD:⁅CubicNormalizer.oddKernel ((P:Subgroup (centralizer z)).map (centralizer z).subtype),zpowers z⁆≤D) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V:=CubicNormalizer.oddKernel X
    ∃F:Subgroup G,F≤V⊓D ∧ Nat.card F=3 ∧ ⁅F,zpowers z⁆=F ∧
      normalizer (F:Set G)≤normalizer (V:Set G) ∧ V.relIndex (normalizer (F:Set G))=24 := by
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
  let B:=X⊓Subgroup.centralizer ({m.s}:Set G)
  let K:=normalizer (U:Set G)
  obtain ⟨hVK,hKV,hVi,_⟩:=R.reflected_line_normalizer_data h P m A hA htA ht hs hTN hlocal
  obtain ⟨hB,hVB,hBNV,hBi,_⟩:=R.opposite_line_normalizer_data h P m ht hs
  have hspan:U⊔B=X:=reflected_fixed_lines_span h P m hB
  have hNU:normalizer (X:Set G)≤K:=cubic_normalizer_preserves_reflected_line h P m.t
    ⟨R.T_le_centralizer ht.1,m.t_normalizes⟩
  have hNB:normalizer (X:Set G)≤normalizer (B:Set G):=cubic_normalizer_preserves_reflected_line h P m.s
    ⟨R.T_le_centralizer hs.1,m.s_normalizes⟩
  have hVN:V≤normalizer (X:Set G):=(map_subtype_le _:V≤Subgroup.centralizer (X:Set G)).trans (centralizer_le_normalizer _)
  have hi:(normalizer (X:Set G)).relIndex K=3:=by
    have hh:=relIndex_mul_relIndex V (normalizer (X:Set G)) K hVN hNU
    rw[R.cubic_normalizer_kernel_index h P m,hVi] at hh
    omega
  obtain ⟨g,hg,hF,hFc,hFn,hinv,hcomm⟩:=h.exists_inverted_cubic_line P m U B D hB hspan hKV
    (inf_le_right.trans hNB) hi hD
  let e:=MulAut.conj g
  let F:=B.map e.toMonoidHom
  have hVm:V.map e.toMonoidHom=V:=mem_normalizer_iff_map_conj_eq.mp (hKV hg)
  have hNF:normalizer (F:Set G)≤normalizer (V:Set G):=by
    have hh:=map_mono hBNV (f:=e.toMonoidHom)
    rw[map_normalizer_eq_of_bijective B e.bijective,map_normalizer_eq_of_bijective V e.bijective,hVm] at hh
    exact hh
  have hFi:V.relIndex (normalizer (F:Set G))=24:=by
    have hh:=relIndex_map_map_of_injective (f:=e.toMonoidHom) V (normalizer (B:Set G)) e.injective
    rw[hVm,map_normalizer_eq_of_bijective B e.bijective,hBi] at hh
    exact hh
  exact ⟨F,hF,hFc,hcomm,hNF,hFi⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem exists_reflected_moved_line_source (h:IsType z) (P:Sylow 3 (centralizer z)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V:=CubicNormalizer.oddKernel X
    ∃_m:CubicNormalizer.ReflectedMarking z X,∀D:Subgroup G,⁅V,zpowers z⁆≤D→
      ∃F:Subgroup G,F≤V⊓D ∧ Nat.card F=3 ∧ ⁅F,zpowers z⁆=F ∧
        normalizer (F:Set G)≤normalizer (V:Set G) ∧ V.relIndex (normalizer (F:Set G))=24 := by
  obtain ⟨R⟩:=h.exists_rootPair
  obtain ⟨m,A,hA,htA,ht,hs,hTN,_,_,hlocal,_,_,_⟩:=R.exists_reflected_line_source_geometry h P
  exact ⟨m,fun D hD=>R.reflected_moved_line h P m A hA htA ht hs hTN hlocal D hD⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
