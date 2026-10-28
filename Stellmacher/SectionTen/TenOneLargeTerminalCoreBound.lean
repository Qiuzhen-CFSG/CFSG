module
public import Stellmacher.SectionTen.TenOneLargePredecessorIndex
public import Stellmacher.SectionTen.TenOneLargePredecessorSelection
public import Stellmacher.SectionTen.TenOneLargePredecessorCentralLayer
public import Stellmacher.SectionTen.TenOneLargeCentralLayerContainment
public import Stellmacher.SectionTen.TenOneLargeResidualCoreCentralizer

/-!
# The final terminal core index bound in the large case of (10.1)

The actual terminal two-core has index at most two over its residual
subgroup O₂(E). Only the original ambient context, path offset and absence
of quotient transvections are assumed.

The core-centralizer supplement identifies this index with the index of
V in C1=C_Q(V). Choose the actual preceding neighbor with both center-core
escapes. Its intersection C2 with C1 has central commutator with O₂(E).
The proved source-(20) centralizer equality and residual central-layer
containment give C2≤V. The native predecessor index calculation then bounds
C1/V by two, and the supplement transfers the bound back to Q/O₂(E).

Source: Stellmacher (10.1), printed p.65 after (20). The index calculation
uses the genuine Frobenius quotient bound and all original graph subgroups.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

private theorem core_index_reduction
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    let Q := QAt ctx.Γ ctx.criticalPath.a'
    let U := twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')
    let V := VAt ctx.Γ ctx.criticalPath.a'
    let C := Q⊓centralizer (V:Set G)
    U.relIndex Q=V.relIndex C := by
  let P := GAt ctx.Γ ctx.criticalPath.a'
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let E := EAt ctx.Γ ctx.criticalPath.a'
  let U := twoCoreIn E
  let V := VAt ctx.Γ ctx.criticalPath.a'
  let C := Q⊓centralizer (V:Set G)
  have hs := ten_one_large_core_centralizer_supplement ctx middle hpath hno
  change Q=C⊔U ∧ C⊓U=V at hs
  have hCQ : C≤Q := inf_le_left
  have hUQ : U≤Q := hs.1 ▸ le_sup_right
  have hQP : Q≤P := by
    change ctx.Γ.twoCoreAt ctx.criticalPath.a'≤ctx.Γ.stabilizer ctx.criticalPath.a'
    rw [ctx.Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hE : E=twoResidualIn P := ctx.Γ.twoResidualAt_def _
  have hEP : E≤P := hE ▸ twoResidualIn_le P
  have hUP : U≤P := (twoCoreIn_le E).trans hEP
  have hPU : P≤normalizer (U:Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  let _ : (U.subgroupOf Q).Normal :=
    (normal_subgroupOf_iff_le_normalizer hUQ).mpr (hQP.trans hPU)
  have hjoin : C.subgroupOf Q⊔U.subgroupOf Q=⊤ := by
    rw [←subgroupOf_sup hCQ hUQ,←hs.1,subgroupOf_self]
  have hh := relIndex_sup_right (C.subgroupOf Q) (U.subgroupOf Q)
  rw [hjoin,relIndex_top_right,relIndex_subgroupOf hCQ,←inf_relIndex_left C U,hs.2] at hh
  exact hh

public theorem ten_one_large_terminal_core_index_le_two
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hno : ∀ actor : G, actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep →
      actor ∉ QAt ctx.Γ ctx.criticalPath.a' → ¬ QuotientCardEq
        (⁅VAt ctx.Γ ctx.criticalPath.a', Subgroup.zpowers actor⁆ ⊔
          ZAt ctx.Γ ctx.criticalPath.a') (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    (twoCoreIn (EAt ctx.Γ ctx.criticalPath.a')).relIndex (QAt ctx.Γ ctx.criticalPath.a')≤2 := by
  obtain ⟨previous,hadj,hne,hforward,hreverse⟩ :=
    ten_one_large_predecessor_selection ctx middle hpath hno
  let C2 := (QAt ctx.Γ ctx.criticalPath.a' ⊓ centralizer
    (VAt ctx.Γ ctx.criticalPath.a' : Set G)) ⊓ QAt ctx.Γ previous
  have hcomm := ten_one_large_predecessor_central_layer ctx middle hpath hno
    previous hadj hne hforward hreverse
  have hfixed := ten_one_large_residual_core_centralizer ctx middle hpath hno
    (ten_one_large_first_residual_five ctx middle hpath hno)
  have hcontain : C2 ≤ VAt ctx.Γ ctx.criticalPath.a' :=
    ten_one_large_central_layer_containment ctx middle hpath hno C2 inf_le_left hcomm hfixed
  rw [core_index_reduction ctx middle hpath hno]
  exact ten_one_large_centralizer_index_of_predecessor ctx middle hpath hno previous hadj hne
    hforward hreverse hcontain

end Stellmacher.SectionTen
