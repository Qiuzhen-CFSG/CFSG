module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover

/-!
# Legacy conditional interface for the critical-fusion calculation

This API does not specify the source hypotheses of 14.7.66–70. It assumes
parts of the desired normalizer, fusion, rank and intersection conclusions.
Its centralizer condition is not C-component membership; `H_le_M` is not
membership in the maximal-local family; and `IsSylowTwoIn` is stronger than
Sylow maximality. The map on all of G is not the source quotient of H.

The conditional declarations are retained for compatibility. New source
proofs use `CriticalFusion.SourceSetup`, with no dependency on this record.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
Lemmas 14.7.63--70, printed pp.1069--1074 (PDF pp.1086--1090).
-/

@[expose] public section
noncomputable section

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion

open Subgroup
open scoped commutatorElement

variable {G Gs : Type*} [Group G] [Finite G] [Group Gs] [Finite Gs]

/-- The literal conjugate used for the critical-pair notation. -/
def conjugateBy (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g).toMonoidHom

/-- The marked image in the quotient actor `G*`. -/
def starImage (q : G →* Gs) (A : Subgroup G) : Subgroup Gs := A.map q

/-- The inverse image of the `K`-fixed space in the literal quotient
`U/V₁`.  The commutator is written in ambient group coordinates, so this
definition does not identify `O₂(H)` and `O₂(K)`. -/
def quotientFixedPreimage (K U V₁ : Subgroup G) : Set G :=
  {u | u ∈ U ∧ ∀ k ∈ K, u * k * u⁻¹ * k⁻¹ ∈ V₁}

/-- A subgroup is a Sylow two subgroup of a marked ambient subgroup.

This formulation keeps the marked quotient carrier visible and avoids
silently changing the source subgroup by a chosen equivalence. -/
def IsSylowTwoIn (R K : Subgroup Gs) : Prop :=
  IsPGroup 2 R ∧ ∀ P : Subgroup Gs, IsPGroup 2 P → P ≤ K → P ≤ R

/-- The source family `L*(G,T)` is kept as a parameter: its construction is
owned by the earlier local-family modules. -/
def IsLStar (LStar : Set (Subgroup G)) (K : Subgroup G) : Prop := K ∈ LStar

/-- A marked critical conjugate with its actual center line. -/
structure PermittedConjugate (U V₂ L : Subgroup G) where
  conjugator : G
  conjugator_mem : conjugator ∈ L
  Uα : Subgroup G
  Zα : Subgroup G
  Uα_eq : Uα = conjugateBy U conjugator
  Zα_le_V₂ : Zα ≤ V₂

/-- Legacy assumptions for the conditional API, including target conclusions.
Do not use this record as the hypotheses of the source theorem. -/
structure Input where
  /- The actual marked local configuration. -/
  star : G →* Gs
  z : G
  H : Subgroup G
  K : Subgroup G
  U : Subgroup G
  V : Subgroup G
  V₁ : Subgroup G
  V₂ : Subgroup G
  L : Subgroup G
  T : Subgroup G
  M : Subgroup G
  G₂ : Subgroup G
  R₁ : Subgroup G
  Q : Subgroup G
  Uα : Subgroup G
  Zα : Subgroup G
  U₀ : Subgroup G
  criticalConjugator : G
  criticalConjugator_mem_L : criticalConjugator ∈ L
  b : ℕ
  LStar : Set (Subgroup G)
  /- Theorem 14.7.63. -/
  H_eq_centralizer_z : H = centralizer ({z} : Set G)
  H_eq_KT : H = K ⊔ T
  K_le_centralizer_H : K ≤ centralizer (H : Set G)
  HStar_is_S5 : Nonempty ((H ⧸ pCore 2 H) ≃* ChapterJ.S5)
  U_abelian : IsMulCommutative U
  U_eq_generated_VH : U = ChapterJ.conjugateSpan H V
  /- The actual quotient and fixed-space marking. -/
  U₀_is_fixed_preimage : (U₀ : Set G) = quotientFixedPreimage K U V₁
  Uα_eq_critical_conjugate : Uα = conjugateBy U criticalConjugator
  Zα_eq_center_conjugate : Zα = conjugateBy V₁ criticalConjugator
  /- 14.7.66: the critical image lies in the marked Sylow. -/
  Uα_le_R₁ : Uα ≤ R₁
  QStar_eq_R₁Star : starImage star Q = starImage star R₁
  R₁Star_is_sylow : IsSylowTwoIn (starImage star R₁) (starImage star K)
  QStar_elementary_four : IsElementaryAbelian 2 (starImage star Q)
  QStar_card : Nat.card (starImage star Q) = 4
  UαStar_nontrivial : starImage star Uα ≠ ⊥
  UαStar_ne_QStar : starImage star Uα ≠ starImage star Q
  /- 14.7.67(1),(2): the earlier L₂T action and hyperplane uniqueness. -/
  G₂_le_normalizer_V₂ : G₂ ≤ normalizer (V₂ : Set G)
  normalizer_V₂_le_M : normalizer (V₂ : Set G) ≤ M
  hyperplane_unique :
    ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 →
      ∀ g : G, F ≤ conjugateBy V g → conjugateBy V g = V
  /- 14.7.67(3): the source local-family exclusion. -/
  lstar_of_no_proper_overgroup :
    (∀ I : Subgroup G, K < I → I ≤ T ⊔ K → False) → IsLStar LStar K
  no_proper_K_overgroup : ∀ I : Subgroup G, K < I → I ≤ T ⊔ K → False
  /- 14.7.67(4),(5): normalizer control. -/
  H_le_normalizer_K : H ≤ normalizer (K : Set G)
  normalizer_K_le_H : normalizer (K : Set G) ≤ H
  H_le_M : H ≤ M
  LT_le_normalizer_V : L ⊔ T ≤ normalizer (V : Set G)
  normalizer_V_le_LT : normalizer (V : Set G) ≤ L ⊔ T
  /- 14.7.68: the source fusion consequences of the fixed-space preimage. -/
  z_mem_U₀ : z ∈ U₀
  z_conjugate_mem_implies_H :
    ∀ g : G, z ∈ conjugateBy U₀ g → g ∈ H
  fixed_mod_V₁ : G → Prop
  centralizer_fixed_le_H :
    ∀ u : G, u ∈ U₀ → u ≠ 1 → fixed_mod_V₁ u →
      centralizer ({u} : Set G) ≤ H
  unique_U₀_of_fixed :
    ∀ u : G, u ∈ U₀ → u ≠ 1 → fixed_mod_V₁ u →
      ∀ g : G, u ∈ conjugateBy U₀ g → g ∈ H
  H_normalizes_U₀ : H ≤ normalizer (U₀ : Set G)
  z_fixed_mod_V₁ : fixed_mod_V₁ z
  z_ne_one : z ≠ 1
  /- 14.7.70(1): the permitted rechoice of the critical conjugate. -/
  permitted : Nonempty (PermittedConjugate U V₂ L)
  /- 14.7.70(2): module rank and the Goldschmidt exclusion of rank three. -/
  twoRank : Subgroup G → ℕ
  U₀_rank_le_three : twoRank U₀ ≤ 3
  rank_three_obstruction : twoRank U₀ = 3 → False
  /- 14.7.70(3): the literal intersection and commutator containments. -/
  U₀_sup_V_le_inter : U₀ ⊔ V ≤ U ⊓ Uα
  inter_le_U₀_sup_V : U ⊓ Uα ≤ U₀ ⊔ V
  comm_le_inter : ⁅U, Uα⁆ ≤ U ⊓ Uα
  comm_sup_V_le_inter : ⁅U, Uα⁆ ⊔ V ≤ U ⊓ Uα
  inter_le_comm_sup_V : U ⊓ Uα ≤ ⁅U, Uα⁆ ⊔ V
  comm_sup_U₀_le_inter : ⁅U, Uα⁆ ⊔ U₀ ≤ U ⊓ Uα
  inter_le_comm_sup_U₀ : U ⊓ Uα ≤ ⁅U, Uα⁆ ⊔ U₀
  /- 14.7.70(4): the earlier distance bounds. -/
  b_ge_three : 3 ≤ b
  b_le_three_of_permitted :
    ∀ _p : PermittedConjugate U V₂ L, b ≤ 3

namespace Input

variable (i : Input (G := G) (Gs := Gs))

omit [Finite G] [Finite Gs] in
theorem qStar_eq (i : Input (G := G) (Gs := Gs)) :
    starImage i.star i.Q = starImage i.star i.R₁ := i.QStar_eq_R₁Star

omit [Finite G] [Finite Gs] in
theorem lt_star (i : Input (G := G) (Gs := Gs)) :
    IsLStar i.LStar i.K := i.lstar_of_no_proper_overgroup i.no_proper_K_overgroup

end Input

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion

end
