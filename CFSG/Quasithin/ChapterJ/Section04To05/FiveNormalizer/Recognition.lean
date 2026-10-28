module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Image
public import Theory.SpecificGroups.SymmetricFive.FiveNormalizerSuzuki
public import Theory.GroupTheory.PCoreSurjective

/-!
# The source first parabolic modulo its two-core

The original quotient map restricts to F₁ with image the actual Sylow-five
normalizer in S₅. Its concrete Suzuki equivalence gives a surjection onto
Sz(2) whose kernel is precisely F₁∩Q. This kernel is a two-group and the
Suzuki group has trivial two-core, so it is the entire two-core of F₁.

Source: Aschbacher–Smith, J.4.4(3), printed p.441. The only Sylow-five
input is inversion by the same source-selected v, already constructed in J.4.1.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} (p:Plane d)

theorem SourceChoice.F₁_projection (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    ∃ f:p.F₁ B5→*BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0,
      Function.Surjective f ∧ f.ker=d.toTypeRuSetup.Q.subgroupOf (p.F₁ B5) := by
  let P:=B5.mapSurjective d.ru2.quotient_surjective
  let q:p.F₁ B5→*S5:=d.ru2.quotientMap.comp (inclusion (p.F₁_le_H B5))
  have hr : q.range=normalizer (B5.map d.ru2.quotientMap:Set S5) := by
    rw [MonoidHom.range_comp,inclusion_range]
    exact s.F₁_image p B5 hi
  obtain ⟨e⟩:=Theory.SpecificGroups.SymmetricFive.FiveNormalizerOvergroups.normalizer_equiv_suzuki P
  let e' := (MulEquiv.subgroupCongr hr).trans e
  let f:=e'.toMonoidHom.comp q.rangeRestrict
  refine ⟨f,e'.surjective.comp q.rangeRestrict_surjective,?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e'.injective,MonoidHom.ker_rangeRestrict]
  ext x
  change inclusion (p.F₁_le_H B5) x∈d.ru2.quotientMap.ker ↔ _
  rw [d.ru2.quotient_kernel]
  rfl

theorem SourceChoice.F₁_twoCore (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (p.F₁ B5).pCoreIn 2=p.F₁ B5⊓d.toTypeRuSetup.Q := by
  obtain ⟨f,hf,hker⟩:=s.F₁_projection p B5 hi
  have hk : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 d.toTypeRuSetup.H).comap_subtype
  have hcore:=f.comap_pCore_of_ker_isPGroup hf hk
  rw [ReeF4.Parabolics.Binary.suzuki_twoCore_eq_bot] at hcore
  change f.ker=pCore 2 (p.F₁ B5) at hcore
  rw [hker] at hcore
  rw [pCoreIn,←hcore,subgroupOf_map_subtype,inf_comm]

theorem SourceChoice.F₁_twoCore_le_Q (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    (p.F₁ B5).pCoreIn 2≤d.toTypeRuSetup.Q := by
  rw [s.F₁_twoCore p B5 hi]
  exact inf_le_right

theorem SourceChoice.F₁_quotient (s:SourceChoice p) (B5:Sylow 5 d.toTypeRuSetup.H)
    (hi:∀a∈B5Image B5,s.v*a*s.v⁻¹=a⁻¹) :
    Nonempty (((p.F₁ B5)⧸pCore 2 (p.F₁ B5))≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  obtain ⟨f,hf,hker⟩:=s.F₁_projection p B5 hi
  have hk : IsPGroup 2 f.ker := by
    rw [hker]
    exact (isPGroup_pCoreIn 2 d.toTypeRuSetup.H).comap_subtype
  have hcore:=f.comap_pCore_of_ker_isPGroup hf hk
  rw [ReeF4.Parabolics.Binary.suzuki_twoCore_eq_bot] at hcore
  change f.ker=pCore 2 (p.F₁ B5) at hcore
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
