module
public import CFSG.Quasithin.ChapterC.Section01.LinearThreeMS.NonbinarySource.SylowInitial
public import Theory.Representation.NormalElementaryQuotient.FixedCore
public import Theory.GroupTheory.PCoreImage

/-!
# The radical comparison on the faithful initial module

The central omega of the actual Sylow is the fixed subgroup of the original
initial layer. Restricting both groups to KR and using literal conjugation
therefore identifies its centralizer image with the pointwise fixer of the
Sylow-fixed subspace in the faithful initial representation.

The quotient kernel is exactly O₂(KR), including at field four, and MS2
places it in R. Exact prime-core lifting consequently turns the original
C.1.34 radical inequality into its equivalent comparison in this known
natural/doubled initial-module action. No whole-core section or exceptional
covering-kernel hypothesis is required. The comparison itself still needs
to be evaluated in the relevant source rows.

NonblockMSClassification and PointApplication apply the equivalence to the
original Chapter4 and Chapter11 configurations.
Source: Aschbacher--Smith C.1.34, printed pp.136--137, and original
4.3.8--10 and11.1.5, pp.616--617,765--766.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SylowInitial
open Chapter1.RadicalExclusions.ModelReduction.FullSieve
open SourceInterface
variable {G : Type*} [Group G] [Finite G] {K R : Subgroup G}
variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
variable (h : LinearThreeMSPair KnownSimple.IsKnownSimple K R n F) (hn : 1 < n)
local notation "J" => (K ⊔ R : Subgroup G)
local notation "E" => centralOmegaLayer K R
local notation "q" => centralOmegaProjection K R
local notation "ρ" => centralOmegaRepresentation K R
local notation "T" => R.subgroupOf (K ⊔ R)

include h

omit [CharP F 2] in
private theorem sylowOmega_subgroupOf {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    (SourceInterface.omegaCenterIn S).subgroupOf J =
      E ⊓ centralizer (S.subgroupOf J : Set J) := by
  have hSJ : S ≤ J := (Chapter1.isSylowIn_iff.mp hS).2.1
  ext x
  change (x : G) ∈ SourceInterface.omegaCenterIn S ↔ _
  rw [sylowOmega_eq_initial_fixed h hS]
  have hE : (x : G) ∈ initialOmega K R ↔ x ∈ E := by
    change (x : G) ∈ (E).map (J).subtype ↔ x ∈ E
    exact mem_map_iff_mem (J).subtype_injective
  change ((x : G) ∈ initialOmega K R ∧ (x : G) ∈ centralizer (S : Set G)) ↔ _
  rw [hE]
  constructor
  · rintro ⟨hx,hc⟩
    exact ⟨hx,fun s hs => Subtype.ext (hc s hs)⟩
  · rintro ⟨hx,hc⟩
    exact ⟨hx,fun s hs => congrArg (J).subtype (hc ⟨s,hSJ hs⟩ hs)⟩

omit [CharP F 2] in
private theorem centralizer_subgroupOf {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    (J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).subgroupOf J =
      centralizer ((E ⊓ centralizer (S.subgroupOf J : Set J) : Subgroup J) : Set J) := by
  rw [←sylowOmega_subgroupOf h hS]
  have hZJ : SourceInterface.omegaCenterIn S ≤ J :=
    fun z hz => (Chapter1.isSylowIn_iff.mp hS).2.1
      ((mem_omegaCenterIn_iff S z).mp hz).1
  ext x
  constructor
  · rintro ⟨_,hc⟩ y hy
    exact Subtype.ext (hc y hy)
  · intro hc
    exact ⟨x.property,fun y hy => congrArg (J).subtype (hc ⟨y,hZJ hy⟩ hy)⟩

include hn

omit hn [CharP F 2] in
/-- The literal Sylow-omega centralizer, projected to the faithful initial
module, is precisely the pointwise fixer of its Sylow-fixed subspace. -/
theorem centralizer_image {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    ((J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).subgroupOf J).map q =
      NormalElementaryQuotient.fixedSpaceFixer ρ ((S.subgroupOf J).map q) := by
  rw [centralizer_subgroupOf h hS]
  exact NormalElementaryQuotient.centralizer_fixed_image E q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) (S.subgroupOf J)

/-- All radical/core comparisons pass to the faithful initial action with
no residual kernel premise, including at the original field-four marking. -/
theorem notCentralizerCore_iff_initial_action {S : Subgroup G}
    (hS : Chapter1.IsSylowIn 2 S J) :
    MSNotCentralizerCore K R S ↔
      (T).map q ≠ (NormalElementaryQuotient.fixedSpaceFixer ρ
        ((S.subgroupOf J).map q)).pCoreIn 2 := by
  have hk : IsPGroup 2 (q).ker := by
    change IsPGroup 2 (QuotientGroup.mk' (centralOmegaKernel K R)).ker
    rw [QuotientGroup.ker_mk',centralOmega_kernel_eq_core h hn]
    exact pCore_isPGroup
  have hRT : (q).ker ≤ T := by
    change (QuotientGroup.mk' (centralOmegaKernel K R)).ker ≤ T
    rw [QuotientGroup.ker_mk',centralOmega_kernel_eq_core h hn]
    exact (join_oddIndex h hn).twoCore_le
  have hc := NormalElementaryQuotient.radical_eq_fixed_core_iff E q
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hk (S.subgroupOf J) T hRT
  rw [←centralizer_subgroupOf h hS] at hc
  have htransport : R = (J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).pCoreIn 2 ↔
      T = ((J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).subgroupOf J).pCoreIn 2 := by
    have hm : (((J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).subgroupOf J).pCoreIn 2).map (J).subtype =
        (J ⊓ centralizer (SourceInterface.omegaCenterIn S : Set G)).pCoreIn 2 := by
      rw [map_pCoreIn_of_injective 2 _ _ (J).subtype_injective,
        map_subgroupOf_eq_of_le inf_le_left]
    constructor
    · intro he
      apply map_injective (J).subtype_injective
      rw [map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right),hm]
      exact he
    · intro he
      have hh := congrArg (fun A : Subgroup J => A.map (J).subtype) he
      rwa [map_subgroupOf_eq_of_le (show R ≤ J from le_sup_right),hm] at hh
  exact not_congr (htransport.trans hc)

end CFSG.Quasithin.ChapterC.LinearThreeMS.NonbinarySource.SylowInitial
