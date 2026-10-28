module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.ReducedResidual
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Original

/-!
# Guarded component applications at the original point normalizer

The same original G,T supplies both structural input and 12.2.13 under
the multiple-overgroup guard. Escape places the full point normalizer in
H_z. The component input then gives uniqueness, normality and full movement
there, and constructs its reduced local C T with an identified whole
residual, trivial quotient centralizer and Fitting subgroup, and the two
surviving residual rows. Its quadratic actor acts on the literal section.

The re-exported source assembly proves component existence in every original
local, vanishing of the full local quotient centralizer, and equality with
its reduction. The remaining row exclusions then give 14.7.52 and the literal
Data and original Rudvalis applications. Earlier14747, RowExclusions, the G₂
exclusion and the earlier source inputs remain explicit; no whole-residual
conclusion or local-uniqueness record is supplied as an earlier input.
The previously checked universal exports are re-exported unchanged.
Source: Aschbacher–Smith 14.7.47–52, pp.1063–1065, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Apply common-point component uniqueness and full movement at the
original full point normalizer, discharging its H_z membership by 12.2.13. -/
theorem original_component_geometry_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (C : Subgroup F.H) (hC : C.IsCComponent) :
    (∀ D : Subgroup F.H, D.IsCComponent → D = C) ∧ C.Normal ∧
      F.U ≤ C.map F.H.subtype ∧ ⁅F.U,C.map F.H.subtype⁆ = F.U ∧
      Group.IsSolvable (centralizer
        (C.map (QuotientGroup.mk' (pCore 2 F.H)) : Set (HStar F.H))) ∧
      C.map F.H.subtype ⊔ (T : Subgroup G) ∈ F.Hz L (normalizer (L : Set G)) := by
  have hH := h.point_mem_Hz_at F (previous hmany)
  exact ⟨local_unique_component_at h (structural hmany) source47 F.H hH C hC,
    local_component_normal_at h (structural hmany) source47 F.H hH C hC,
    local_span_le_component_at h (structural hmany) source47 F.H hH C hC,
    local_component_full_movement_at h (structural hmany) source47 F.H hH C hC,
    local_component_star_centralizer_solvable_at h (structural hmany) source47 F.H hH C hC,
    local_component_sylow_join_mem_Hz_at h (structural hmany) source47 F.H hH C hC⟩

/-- The canonical reduction of the original component has the two literal
whole-residual alternatives, with its supplement and Fitting calculation proved. -/
theorem original_reduced_residual_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (C : Subgroup F.H) (hC : C.IsCComponent) :
    let A := C.map F.H.subtype
    let J := A ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 J)
    let R := (pResidual 2 J).map J.subtype
    J ≤ F.H ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
      (A.subgroupOf J).IsCComponent ∧ pResidual 2 J = A.subgroupOf J ∧
      R = A ∧ fittingSubgroup (HStar J) = ⊥ ∧
      centralizer ((A.subgroupOf J).map q : Set (HStar J)) = ⊥ ∧
      ResidualRows (R ⧸ pCore 2 R) ∧ ⁅F.UH J,A⁆ = F.UH J := by
  have hH := h.point_mem_Hz_at F (previous hmany)
  let A := C.map F.H.subtype
  let J := A ⊔ (T : Subgroup G)
  obtain ⟨hJ,hKJ,hres,hemb⟩ :=
    reduced_component_eq_residual_at h (structural hmany) source47 F.H hH C hC
  obtain ⟨hc,hf⟩ :=
    reduced_component_centralizer_and_fitting_at h (structural hmany) source47 F.H hH C hC
  refine ⟨sup_le (map_subtype_le _) (F.sylow_le_of_mem_Hz hH),hJ,hKJ,hres,hemb,hf,hc,
    reduced_whole_residual_rows_at h (structural hmany) source47 exclusions F.H hH C hC,?_⟩
  have hm := local_component_full_movement_at h (structural hmany) source47 J hJ
    (A.subgroupOf J) hKJ
  rwa [map_subgroupOf_eq_of_le (show A ≤ J from le_sup_left)] at hm

/-- The faithful quadratic action on that same original reduction is
constructed without a universal structural or module source record. -/
theorem original_reduced_quadratic_actor_of_many_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (C : Subgroup F.H) (hC : C.IsCComponent) :
    let J := C.map F.H.subtype ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 J)
    ∃ hU : IsElementaryAbelian 2 (F.UH J),
      let := hU
      ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
        quadraticRatio a.representation ≤ 2 ∧
        ∃ B : Subgroup J,
          B ≤ (F.Ri L 1).subgroupOf J ∧
          IsElementaryTwo (B.map q) ∧ IsQuadratic a.representation (B.map q) ∧
          fixedCodim a.representation (B.map q) ≤ 2 * rank (B.map q) ∧
          B.map q ⊓ centralizer
            (((C.map F.H.subtype).subgroupOf J).map q : Set (HStar J)) = ⊥ := by
  have hH := h.point_mem_Hz_at F (previous hmany)
  exact (local_component_quadratic_reduction_at h hab (structural hmany) source47
    F.H hH C hC).2.2.2.2.2.2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
