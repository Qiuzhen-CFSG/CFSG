module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicNormalizer.LineNormalizer.Data
/-!
# The original S4 line-normalizer quotient

Starting only from IsType and the actual Sylow three in C(z), choose the
positioned reflected line. Its canonical odd kernel is normal in the full
line normalizer, and the literal quotient is isomorphic to S4.
Source: Aschbacher, Sporadic Groups (1994),45.7–45.8,pp.245–246.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G:Type*} [Group G] [Finite G] {z:G}
theorem exists_reflected_line_quotient_source (h:IsType z) (P:Sylow 3 (centralizer z)) :
    let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
    let V:=CubicNormalizer.oddKernel X
    ∃m:CubicNormalizer.ReflectedMarking z X,
      let U:=X⊓Subgroup.centralizer ({m.t}:Set G)
      let K:=normalizer (U:Set G)
      V≤K ∧ V.relIndex K=24 ∧ ∃hN:(V.subgroupOf K).Normal,
        letI := hN
        Nonempty ((K⧸V.subgroupOf K)≃*Equiv.Perm (Fin 4)) := by
  obtain ⟨R⟩:=h.exists_rootPair
  obtain ⟨m,A,hA,htA,ht,hs,hTN,_,_,hlocal,_,_,_⟩:=R.exists_reflected_line_source_geometry h P
  obtain ⟨hVK,hKV,hi,φ,hφ,hker⟩:=R.reflected_line_normalizer_data h P m A hA htA ht hs hTN hlocal
  let X:=(P:Subgroup (centralizer z)).map (centralizer z).subtype
  let V:=CubicNormalizer.oddKernel X
  let K:=normalizer ((X⊓Subgroup.centralizer ({m.t}:Set G):Subgroup G):Set G)
  let hN:(V.subgroupOf K).Normal:=normal_subgroupOf_of_le_normalizer hKV
  refine ⟨m,hVK,hi,hN,?_⟩
  let :=hN
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
