module

public import CFSG.Quasithin.Chapter13.Section08.SourceDefs
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Elementary
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# Quotients and overgroups for the components in §13.8

The quotient equivalence identifies the literal image K* in H/O₂(H) with
K/O₂(K), using only relative subnormality. A nontrivial normal two-subgroup
in L₁T certifies the two-core condition when passing to a generated overgroup
inside G₁. Solvable exclusion supplies an actual C-component of H.

These deductions support Aschbacher–Smith 13.8.15–17, printed pp.952–953
(combined manuscript of 1 March 2004). They do not prove the outstanding
Fitting-centralizer bound, component normality, Suzuki exclusion or model
classification. All normality hypotheses here are relative to H.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section08.Components
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic quotient is the actual image K*, including its precise kernel. -/
noncomputable def componentStarEquiv (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) :
    (K ⧸ pCore 2 K) ≃* Source.starImage H K := by
  let e : K ≃* K.subgroupOf H := (subgroupOfEquivOfLe hKH).symm
  exact (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (cComponentTwoCoreQuotientEquiv hK)

/-- A C-component remains a C-component in H/O₂(H). -/
theorem starImage_isCComponent (H K : Subgroup G)
    (hK : (K.subgroupOf H).IsCComponent) :
    (Source.starImage H K).IsCComponent := by
  let := pCore_isNilpotent (p := 2) (G := H)
  exact hK.map_quotient (pCore 2 H)

/-- Transport quasisimplicity between the intrinsic quotient and the literal image. -/
theorem quasisimple_star_iff (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) :
    IsQuasisimple (Source.starImage H K) ↔ IsQuasisimple (K ⧸ pCore 2 K) := by
  constructor
  · intro h
    let := h
    exact IsQuasisimple.of_mulEquiv (componentStarEquiv H K hKH hK).symm
  · intro h
    let := h
    exact IsQuasisimple.of_mulEquiv (componentStarEquiv H K hKH hK)

omit [Finite G] in
/-- Retain the nontrivial two-core clause when constructing a member of Hz. -/
theorem mem_Hz_of_normal_two_subgroup (L₁ T G₁ M P J : Subgroup G)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ T)
    (hn : G₁ ≤ normalizer (P : Set G))
    (hbase : L₁ ⊔ T ≤ J) (hJG : J ≤ G₁) (hout : ¬ J ≤ M) :
    J ∈ Source.Hz L₁ T G₁ M := by
  refine ⟨⟨?_, hbase⟩, hJG, hout⟩
  change J.pCoreIn 2 ≠ ⊥
  intro he
  exact hP (le_bot_iff.mp ((le_pCoreIn_of_normalizes hp (hPbase.trans hbase)
    (hJG.trans hn)).trans he.le))

omit [Finite G] in
/-- The universal solvable exclusion of 13.8.13 makes each member of Hz nonsolvable. -/
theorem not_solvable_of_mem_Hz (L₁ T G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) : ¬ Group.IsSolvable H := by
  intro hs
  exact hH.2.2 (hex H hH.1.2 hH.2.1 hs)

/-- Select a genuine C-component of H from solvable exclusion. -/
theorem exists_component_of_mem_Hz (L₁ T G₁ M H : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hex : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ →
      Group.IsSolvable J → J ≤ M) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent := by
  obtain ⟨K, hK⟩ := exists_isCComponent_of_not_isSolvable
    (not_solvable_of_mem_Hz L₁ T G₁ M H hH hex)
  refine ⟨K.map H.subtype, map_subtype_le K, ?_⟩
  have he : (K.map H.subtype).subgroupOf H = K := by
    change (K.map H.subtype).comap H.subtype = K
    exact comap_map_eq_self_of_injective H.subtype_injective K
  rwa [he]

omit [Finite G] in
/-- The T-conjugate span of an outside component generates a member of Hz with L₁T. -/
theorem generated_overgroup_mem_Hz (L₁ T G₁ M H K P : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hKH : K ≤ H) (hKM : ¬ K ≤ M)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ T)
    (hn : G₁ ≤ normalizer (P : Set G)) :
    conjugateSpanBy K T ⊔ (L₁ ⊔ T) ∈ Source.Hz L₁ T G₁ M := by
  apply mem_Hz_of_normal_two_subgroup L₁ T G₁ M P _ hP hp hPbase hn le_sup_right
  · refine (sup_le ?_ (show L₁ ⊔ T ≤ H from hH.1.2)).trans hH.2.1
    exact (conjugateSpanBy_mono le_rfl (le_sup_right.trans hH.1.2)).trans
      (conjugateSpanBy_le_self hKH)
  · intro he
    exact hKM ((le_conjugateSpanBy K T).trans (le_sup_left.trans he))

omit [Finite G] in
/-- Relative normality in H collapses the T-conjugate span. -/
theorem conjugateSpan_eq_of_normal (H K T : Subgroup G) (hKH : K ≤ H)
    (hTH : T ≤ H) (hn : (K.subgroupOf H).Normal) : conjugateSpanBy K T = K := by
  apply le_antisymm _ (le_conjugateSpanBy K T)
  exact conjugateSpanBy_le le_rfl (hTH.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn))

omit [Finite G] in
/-- After proving relative normality, the smaller product KL₁T still belongs to Hz. -/
theorem normal_overgroup_mem_Hz (L₁ T G₁ M H K P : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hKH : K ≤ H) (hKM : ¬ K ≤ M)
    (hP : P ≠ ⊥) (hp : IsPGroup 2 P) (hPbase : P ≤ L₁ ⊔ T)
    (hn : G₁ ≤ normalizer (P : Set G)) (hKn : (K.subgroupOf H).Normal) :
    K ⊔ (L₁ ⊔ T) ∈ Source.Hz L₁ T G₁ M := by
  have h := generated_overgroup_mem_Hz L₁ T G₁ M H K P hH hKH hKM hP hp hPbase hn
  rwa [conjugateSpan_eq_of_normal H K T hKH (le_sup_right.trans hH.1.2) hKn] at h

omit [Finite G] in
/-- The generated overgroup is the source's setwise product when L₁ normalizes
the component orbit and T normalizes L₁. -/
theorem generated_overgroup_product (K L₁ T : Subgroup G)
    (hL : L₁ ≤ normalizer (conjugateSpanBy K T : Set G))
    (hT : T ≤ normalizer (L₁ : Set G)) :
    ((conjugateSpanBy K T ⊔ (L₁ ⊔ T) : Subgroup G) : Set G) =
      (conjugateSpanBy K T : Set G) * (L₁ : Set G) * (T : Set G) := by
  rw [coe_mul_of_right_le_normalizer_left _ _
    (sup_le hL (le_normalizer_conjugateSpanBy K T)),
    coe_mul_of_right_le_normalizer_left L₁ T hT, mul_assoc]

omit [Finite G] in
/-- Relative normality certifies that the join denoting KL₁T is the actual
setwise product, rather than just a larger generated subgroup. -/
theorem normal_overgroup_product (H K L₁ T : Subgroup G)
    (hKH : K ≤ H) (hbase : L₁ ⊔ T ≤ H)
    (hKn : (K.subgroupOf H).Normal) (hT : T ≤ normalizer (L₁ : Set G)) :
    ((K ⊔ (L₁ ⊔ T) : Subgroup G) : Set G) =
      (K : Set G) * (L₁ : Set G) * (T : Set G) := by
  rw [coe_mul_of_right_le_normalizer_left K (L₁ ⊔ T)
    (hbase.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hKn)),
    coe_mul_of_right_le_normalizer_left L₁ T hT, mul_assoc]

/-- Quasisimplicity of the literal image K* from a Fitting-centralizer bound. -/
theorem star_quasisimple_of_fitting_centralizes (H K : Subgroup G)
    (hK : (K.subgroupOf H).IsCComponent)
    (hc : fittingSubgroup (Source.Hstar H) ≤
      centralizer (Source.starImage H K : Set (Source.Hstar H))) :
    IsQuasisimple (Source.starImage H K) :=
  (starImage_isCComponent H K hK).isQuasisimple_of_fitting_centralizes hc

/-- The quotient equivalence sends a representative to its image under H → H/O₂(H). -/
theorem componentStarEquiv_mk (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (k : K) :
    (componentStarEquiv H K hKH hK (QuotientGroup.mk' (pCore 2 K) k) : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩ := by
  rfl

end CFSG.Quasithin.Chapter13.Section08.Components

end
