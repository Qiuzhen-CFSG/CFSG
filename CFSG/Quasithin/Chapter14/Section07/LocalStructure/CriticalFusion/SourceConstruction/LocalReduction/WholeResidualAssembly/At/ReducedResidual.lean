module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Components
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.NonEnlargement
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.SemisimpleCenter

/-!
# The whole residual of the constructed reduced local

Common L₁ containment and component escape construct J = C T inside the
original I. The intrinsic component in J is perfect and normal; its full
Sylow supplement therefore identifies it with O²(J). The literal image
in J/O₂(J) is simple and has two-group quotient. Its centralizer and the
Fitting subgroup are consequently trivial. The same subtype maps identify
the embedded residual with the original component in G.

The remaining row exclusions give the whole-residual alternatives for
this constructed J. This does not assert I = J or construct a component
in an arbitrary I; those remain duties of the original guarded assembly.
Source: Aschbacher–Smith 14.7.47–48 and 14.7.52, pp.1063–1065,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual reduced-local component is the whole intrinsic two-residual.
Its existence is the supplied original component, not a residual hypothesis. -/
theorem reduced_component_eq_residual_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    let A := C.map I.subtype
    let J := A ⊔ (T : Subgroup G)
    J ∈ F.Hz L (normalizer (L : Set G)) ∧
      (A.subgroupOf J).IsCComponent ∧
      pResidual 2 J = A.subgroupOf J ∧
      (pResidual 2 J).map J.subtype = A := by
  let A := C.map I.subtype
  let J := A ⊔ (T : Subgroup G)
  let KJ := A.subgroupOf J
  have hJ := local_component_sylow_join_mem_Hz_at h structural source47 I hI C hC
  have hJI : J ≤ I := sup_le (map_subtype_le _) (F.sylow_le_of_mem_Hz hI)
  have hCI : (A.subgroupOf I).IsCComponent := by
    simpa only [A,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  have hKJ : KJ.IsCComponent := hCI.subgroupOf_of_le le_sup_left hJI
  let := local_component_normal_at h structural source47 J hJ KJ hKJ
  let S := T.subtype (F.sylow_le_of_mem_Hz hJ)
  have hgen : KJ ⊔ (S : Subgroup J) = ⊤ := by
    rw [Sylow.coe_subtype,←subgroupOf_sup
      (show A ≤ J from le_sup_left) (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hp : IsPPerfect 2 KJ := by
    let := hKJ.perfect
    intro N hN hquot
    let := hN
    have hsub : Subsingleton (KJ ⧸ N) := by
      by_contra! hn
      exact Group.IsPerfect.not_isNilpotent (KJ ⧸ N) hquot.isNilpotent
    apply eq_top_iff.mpr
    intro c _
    exact (QuotientGroup.eq_one_iff c).mp (Subsingleton.elim _ _)
  have he := pResidual_eq_of_isPPerfect_sup KJ (S : Subgroup J) hp S.isPGroup' hgen
  refine ⟨hJ,hKJ,he,?_⟩
  rw [he,map_subgroupOf_eq_of_le (show A ≤ J from le_sup_left)]

/-- In the constructed reduced local, the component centralizer and Fitting
subgroup vanish. This uses its proved residual equality, not 14.7.28. -/
theorem reduced_component_centralizer_and_fitting_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    let J := C.map I.subtype ⊔ (T : Subgroup G)
    let q := QuotientGroup.mk' (pCore 2 J)
    let B := ((C.map I.subtype).subgroupOf J).map q
    centralizer (B : Set (HStar J)) = ⊥ ∧ fittingSubgroup (HStar J) = ⊥ := by
  let J := C.map I.subtype ⊔ (T : Subgroup G)
  let KJ := (C.map I.subtype).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := KJ.map q
  obtain ⟨hJ,hKJ,hres,_⟩ := reduced_component_eq_residual_at h structural source47 I hI C hC
  let hn : KJ.Normal := local_component_normal_at h structural source47 J hJ KJ hKJ
  let : B.Normal := hn.map q (QuotientGroup.mk'_surjective _)
  let : IsSimpleGroup B := ((source47 J hJ KJ hKJ).2.of_equiv
    (cComponentTwoCoreQuotientEquiv hKJ)).isSimpleGroup
  have hB := (local_component_star_of_earlier14747 source47 J hJ KJ hKJ).1
  let := hB.2
  change pResidual 2 J = KJ at hres
  have hBres : B = pResidual 2 (HStar J) := by
    rw [show B = KJ.map q from rfl,←hres]
    exact map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)
  have hquot : IsPGroup 2 ((HStar J) ⧸ B) := by
    exact (isPGroup_quotient_pResidual 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hBres.symm)
  have hc := centralizer_eq_bot_of_simple_two_quotient B
    (Group.IsPerfect.not_isMulCommutative _) hquot (pCore_quotient_pCore_eq_bot 2)
  refine ⟨hc,le_bot_iff.mp ?_⟩
  exact (le_centralizer_iff.mp
    (hB.le_centralizer_of_solvable_normal (fittingSubgroup (HStar J)))).trans hc.le

/-- The remaining row exclusions identify the whole residual of C T,
using the actual embedded residual and its intrinsic two-core quotient. -/
theorem reduced_whole_residual_rows_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (source47 : Earlier14747 F L) (exclusions : RowExclusions F L)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    let J := C.map I.subtype ⊔ (T : Subgroup G)
    let R := (pResidual 2 J).map J.subtype
    ResidualRows (R ⧸ pCore 2 R) := by
  obtain ⟨_,_,_,he⟩ := reduced_component_eq_residual_at h structural source47 I hI C hC
  dsimp only
  rw [he]
  let e : C ≃* C.map I.subtype := equivMapOfInjective C I.subtype I.subtype_injective
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  rcases local_component_residual_rows source47 exclusions I hI C hC with ha | ha
  all_goals obtain ⟨a⟩ := ha
  · exact Or.inl ⟨eq.symm.trans a⟩
  · exact Or.inr ⟨eq.symm.trans a⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly
