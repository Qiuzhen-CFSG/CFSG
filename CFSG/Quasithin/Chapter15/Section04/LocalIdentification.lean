module

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.TwoCoreRecognition

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.ComponentRecognition

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceLocalInputs

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceAssembly

public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.AlternateObstruction
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.Centralizer
public import Theory.GroupTheory.OrderFourIntersectionObstruction
public import Theory.PGroup
public import Theory.PGroupCore
public import Theory.GroupTheory.Fitting.Core
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Local identification: legacy interfaces and source development

The original declarations in this file are retained for API compatibility.
They do **not** establish Aschbacher–Smith 15.4.21–23 (printed pp.1164–1165).
See `docs/quasithin-proof-basis.md`.

`LocalData` does not identify its actions with conjugation; `TwoCoreBranch`
is inconsistent; `local_generalized_fitting_dichotomy` uses ordinary Fitting;
and the exceptional and pairwise certificates assume the identifications.
Their valid conditional statements must not be used as source theorems.

The genuine setup and independent proof steps live in the `LocalIdentification`
descendants. Their remaining classification premises must still be discharged.
-/

namespace CFSG.Quasithin.Chapter15.Section04

set_option linter.unusedSectionVars false

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The ambient two-core of a subgroup, viewed in the ambient group. -/
public def twoCoreIn (L : Subgroup G) : Subgroup G :=
  (pCore 2 L).map L.subtype

/-- Legacy data with actions not identified with conjugation. These fields
have not been derived from the source configuration. -/
public structure LocalData where
  X : Subgroup G
  X₁ : Subgroup G
  X₂ : Subgroup G
  Y : Subgroup G
  Y₁ : Subgroup G
  Y₂ : Subgroup G
  T : Subgroup G
  T₀ : Subgroup G
  L₁ : Subgroup G
  L₂ : Subgroup G
  G₁ : Subgroup G
  G₂ : Subgroup G
  I : Subgroup G
  V₁ : Subgroup G
  V₂ : Subgroup G
  X_factors : X₁ ⊔ X₂ ≤ X
  Y_factors : Y₁ ⊔ Y₂ ≤ Y
  T₀_eq : T₀ = T ⊓ normalizer (X₁ : Set G) ⊓ normalizer (Y₁ : Set G)
  L₁_choice : L₁ = X₁ ∨ L₁ = X₂
  L₂_choice : L₂ = Y₁ ∨ L₂ = Y₂
  G₁_eq : G₁ = L₁ ⊔ T₀
  G₂_eq : G₂ = L₂ ⊔ T₀
  I_eq : I = G₁ ⊔ G₂
  L₁_le_I : L₁ ≤ I
  L₂_le_I : L₂ ≤ I
  T₀_le_I : T₀ ≤ I
  action₁ : G₁ →* MulAut ↥V₁
  action₂ : G₂ →* MulAut ↥V₂
  V₁_elementary : IsElementaryAbelian 2 ↥V₁
  V₂_elementary : IsElementaryAbelian 2 ↥V₂
  V₁_rank_two : Nat.card ↥V₁ = 4
  V₂_rank_two : Nat.card ↥V₂ = 4
  V₁_centralizer : centralizer (V₁ : Set G) ≤ G₁
  V₂_centralizer : centralizer (V₂ : Set G) ≤ G₂
  sylow_intersection : ∃ S : Sylow 2 I,
    G₁ ⊓ G₂ = (S : Subgroup I).map I.subtype

/-- Legacy inconsistent certificate. Its rank-three containment and exclusion
fields contradict each other. It does not describe a source branch. -/
public structure TwoCoreBranch (d : LocalData (G := G)) : Prop where
  fitting_eq : fittingSubgroup d.I = pCore 2 d.I
  cover : d.I ≤ d.L₁ ⊔ d.L₂ ⊔ d.T₀
  L₁_normalizer : d.I ≤ normalizer (d.L₁ : Set G)
  L₂_normalizer : d.I ≤ normalizer (d.L₂ : Set G)
  rank_three : ∃ V : Subgroup d.I,
    IsElementaryAbelian 3 V ∧ Nat.card V = 27
  rank_three_le_twoCore : ∀ V : Subgroup d.I,
    IsElementaryAbelian 3 V → Nat.card V = 27 →
      V.map d.I.subtype ≤ (pCore 2 d.I).map d.I.subtype
  rank_three_excluded : ∀ V : Subgroup d.I,
    IsElementaryAbelian 3 V → Nat.card V = 27 →
      ¬ V.map d.I.subtype ≤ (pCore 2 d.I).map d.I.subtype

/-- Legacy conditional factorization from an inconsistent certificate. -/
public theorem TwoCoreBranch.factorization
    {d : LocalData (G := G)} (h : TwoCoreBranch d) :
    d.I = d.L₁ ⊔ d.L₂ ⊔ d.T₀ ∧
      (d.L₁.subgroupOf d.I).Normal ∧
      (d.L₂.subgroupOf d.I).Normal := by
  have h₁ : (d.L₁.subgroupOf d.I).Normal :=
    (normal_subgroupOf_iff_le_normalizer d.L₁_le_I).mpr h.L₁_normalizer
  have h₂ : (d.L₂.subgroupOf d.I).Normal :=
    (normal_subgroupOf_iff_le_normalizer d.L₂_le_I).mpr h.L₂_normalizer
  refine ⟨le_antisymm h.cover ?_, h₁, h₂⟩
  exact sup_le (sup_le d.L₁_le_I d.L₂_le_I) d.T₀_le_I

/-- The legacy certificate is contradictory. This proves no case of 15.4.23. -/
public theorem TwoCoreBranch.eliminate
    {d : LocalData (G := G)} (h : TwoCoreBranch d) : False := by
  obtain ⟨V, hV, hcard⟩ := h.rank_three
  exact h.rank_three_excluded V hV hcard (h.rank_three_le_twoCore V hV hcard)

/-- Legacy exceptional certificate assuming both model identifications.
It uses `C_I(K)` without proving equality with the source centralizer `C_T(K)`. -/
public structure ExceptionalBranch (d : LocalData (G := G)) where
  K : Subgroup G
  K_le_I : K ≤ d.I
  K_normalizer : d.I ≤ normalizer (K : Set G)
  cover : d.I = K ⊔ d.T₀
  K_is_A6 : Nonempty (K ≃* alternatingGroup (Fin 6))
  centralizer_normal :
    ((d.I ⊓ centralizer (K : Set G)).subgroupOf d.I).Normal
  quotient_is_S6 :
    (let _ := centralizer_normal
    Nonempty (d.I ⧸ (d.I ⊓ centralizer (K : Set G)).subgroupOf d.I ≃*
      Equiv.Perm (Fin 6)))

/-- Legacy projection of the assumed exceptional identifications. -/
public theorem ExceptionalBranch.conclusions
    {d : LocalData (G := G)} (h : ExceptionalBranch d) :
    d.I = h.K ⊔ d.T₀ ∧ Nonempty (h.K ≃* alternatingGroup (Fin 6)) ∧
      ∃ hC : ((d.I ⊓ centralizer (h.K : Set G)).subgroupOf d.I).Normal,
        (let _ := hC
         Nonempty (d.I ⧸ (d.I ⊓ centralizer (h.K : Set G)).subgroupOf d.I ≃*
           Equiv.Perm (Fin 6))) := by
  refine ⟨h.cover, h.K_is_A6, h.centralizer_normal, ?_⟩
  simpa using h.quotient_is_S6

/-- Legacy conditional dichotomy for ordinary Fitting. Despite its public
name, this is not the generalized-Fitting dichotomy of 15.4.21–22. -/
public theorem local_generalized_fitting_dichotomy
    {d : LocalData (G := G)}
    (hF : fittingSubgroup d.I = pCore 2 d.I ∨
      fittingSubgroup d.I ≠ pCore 2 d.I)
    (h_two : fittingSubgroup d.I = pCore 2 d.I → TwoCoreBranch d)
    (h_exc : fittingSubgroup d.I ≠ pCore 2 d.I → ExceptionalBranch d) :
    (fittingSubgroup d.I = pCore 2 d.I ∧
      d.I = d.L₁ ⊔ d.L₂ ⊔ d.T₀ ∧
      (d.L₁.subgroupOf d.I).Normal ∧
      (d.L₂.subgroupOf d.I).Normal) ∨
      (fittingSubgroup d.I ≠ pCore 2 d.I ∧
        ∃ K : Subgroup G, K ≤ d.I ∧ d.I = K ⊔ d.T₀ ∧
          Nonempty (K ≃* alternatingGroup (Fin 6)) ∧
          ∃ hC : ((d.I ⊓ centralizer (K : Set G)).subgroupOf d.I).Normal,
            (let _ := hC
             Nonempty (d.I ⧸ (d.I ⊓ centralizer (K : Set G)).subgroupOf d.I ≃*
               Equiv.Perm (Fin 6)))) := by
  rcases hF with hF | hF
  · left
    exact ⟨hF, (h_two hF).factorization⟩
  · right
    have hc := (h_exc hF).conclusions
    rcases hc with ⟨hcover, hA6, hrest⟩
    rcases hrest with ⟨hC, hS6⟩
    exact ⟨hF, (h_exc hF).K, (h_exc hF).K_le_I, hcover, hA6, hC, hS6⟩

/-- Legacy certificate assuming every pairwise recognition conclusion.
No construction from the source local actions is provided by this record. -/
public structure PairwiseCertificate (d : LocalData (G := G)) : Prop where
  L₁_choice : d.L₁ = d.X₁ ∨ d.L₁ = d.X₂
  L₂_choice : d.L₂ = d.Y₁ ∨ d.L₂ = d.Y₂
  L₁_is_A4 : Nonempty (d.L₁ ≃* alternatingGroup (Fin 4))
  L₂_is_A4 : Nonempty (d.L₂ ≃* alternatingGroup (Fin 4))
  twoCore_join_is_D8 :
    Nonempty ((↥(twoCoreIn d.L₁ ⊔ twoCoreIn d.L₂)) ≃* DihedralGroup 4)
  twoCore_intersection :
    twoCoreIn d.L₁ ⊓ twoCoreIn d.L₂ ≠ ⊥

/-- Legacy projection of the pairwise certificate. -/
public theorem pairwise_structural_conclusions
    {d : LocalData (G := G)} (h : PairwiseCertificate d) :
    Nonempty (d.L₁ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty (d.L₂ ≃* alternatingGroup (Fin 4)) ∧
      Nonempty ((↥(twoCoreIn d.L₁ ⊔ twoCoreIn d.L₂)) ≃* DihedralGroup 4) ∧
      twoCoreIn d.L₁ ⊓ twoCoreIn d.L₂ ≠ ⊥ := by
  exact ⟨h.L₁_is_A4, h.L₂_is_A4, h.twoCore_join_is_D8,
    h.twoCore_intersection⟩

/-- Legacy projection of the assumed nontrivial intersection. -/
public theorem pairwise_nontrivial_intersection
    {d : LocalData (G := G)} (h : PairwiseCertificate d) :
    twoCoreIn d.L₁ ⊓ twoCoreIn d.L₂ ≠ ⊥ :=
  h.twoCore_intersection

end CFSG.Quasithin.Chapter15.Section04
