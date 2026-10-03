module

public import Stellmacher.SectionOne.RankOneThreeGroupAssembly.Basic

/-!
# Local recursion and genericity interfaces

The local hypothesis retains the source-derived quotient Sylow, odd-core
image, cardinal-preserving restriction, local SL2 product and m=1. Genericity
concerns only displayed local factors equipped with their lifted order-four
coordinates. Their coordinate commutator identity also proves normalization
by the whole elementary abelian Sylow subgroup, as used in the exceptional
finite-action calculation.

This module supports the rank-at-least-two case of Stellmacher (1.6).
The action is on an elementary abelian two-group; the local hypotheses and
minimal-offender conditions are explicit in the declarations that use them.
Source: `refs/latex/stellmacher-n-group.tex`, proof of (1.6), journal pp.18–19.
-/

open scoped Pointwise symmDiff commutatorElement

namespace Stellmacher.SectionOne.RankOneThreeGroupAssembly

universe u v

private noncomputable def sl2TwoEquivGL :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃*
      Matrix.GeneralLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective Matrix.SpecialLinearGroup.toGL ⟨
    Matrix.SpecialLinearGroup.toGL_injective,
    by
      intro A
      have hdet : Matrix.det (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by
        have hu : Matrix.GeneralLinearGroup.det A = 1 := Subsingleton.elim _ _
        exact congrArg Units.val hu
      refine ⟨⟨(A : Matrix (Fin 2) (Fin 2) (ZMod 2)), hdet⟩, ?_⟩
      exact Units.ext rfl⟩

public theorem isSL2Two_card
    {E : Type u} [Group E] [Finite E] (hE : IsSL2Two E) :
    Nat.card E = 6 := by
  rcases hE with ⟨e⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_congr sl2TwoEquivGL.toEquiv,
    Matrix.card_GL_field]
  decide

/-- The recursive quotient data, including the full-module equality `m(P)=1`. -/
@[expose] public def RankOneAssemblyLocalHypothesis
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) : Prop :=
  ∀ A : Subgroup G,
    oneAmax (G := G) (V := V) S A → Nat.card A = 2 →
    let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
    let H := W_A ⊔ S
    let A_H := A.subgroupOf H
    ∃ hA_H : A_H.Normal,
      let _ : A_H.Normal := hA_H
      let V_A := FixedPoints.subgroup A_H V
      ∃ P : Sylow 2 (H ⧸ A_H),
        (P : Subgroup (H ⧸ A_H)) =
            (S.subgroupOf H).map (QuotientGroup.mk' A_H) ∧
          oddCore (H ⧸ A_H) =
            (W_A.subgroupOf H).map (QuotientGroup.mk' A_H) ∧
          Nat.card ((W_A.subgroupOf H).map (QuotientGroup.mk' A_H)) =
            Nat.card W_A ∧
          Stellmacher.SectionOne.RankOneLocalSL2Data
            (G := H ⧸ A_H) (V := V_A)
            (P : Subgroup (H ⧸ A_H)) ∧
          m (G := H ⧸ A_H) (V := V_A)
            (P : Subgroup (H ⧸ A_H)) = 1

/-- The source-level coordinate data attached to one lifted derived factor.
This is deliberately an ambient formulation: it records exactly the
order-four subgroup `A_i` and the two conclusions about its points which are
transported out of the recursive quotient. -/
@[expose] public def RankOneLocalFactorCoordinate
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S A F : Subgroup G) : Prop :=
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  ∃ Aᵢ : Subgroup G,
    A ≤ Aᵢ ∧ Aᵢ ≤ S ∧ Nat.card Aᵢ = 4 ∧
    ⁅W_A, Aᵢ⁆ = F ∧
    ∀ x : G, x ∈ Aᵢ → x ∉ A →
      ⁅F, Subgroup.zpowers x⁆ = F ∧
      (Nat.card (FixedPoints.subgroup A V) : ℚ) /
        Nat.card (↥(FixedPoints.subgroup A V ⊓
          FixedPoints.subgroup (Subgroup.zpowers x) V)) = 2

/-- Genericity for the displayed local factors of one recursive quotient.
The coordinate premise restricts the quantifier to the factors denoted
`E_i'` in the source, avoiding an unjustified assertion about arbitrary
diagonal order-three subgroups of the local odd core. -/
@[expose] public def RankOneLocalGenericHypothesis
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S A : Subgroup G) : Prop :=
  let W_A := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  let H := W_A ⊔ S
  let A_H := A.subgroupOf H
  ∀ hA_H : A_H.Normal,
    let _ : A_H.Normal := hA_H
    let V_A := FixedPoints.subgroup A_H V
    ∀ F : Subgroup G, F ≤ W_A → Nat.card F = 3 →
      oneOmega (G := H ⧸ A_H) (V := V_A)
        ((F.subgroupOf H).map (QuotientGroup.mk' A_H)) →
      RankOneLocalFactorCoordinate (G := G) (V := V) S A F →
      commutatorAction F V ≤ V_A

/-- The exact genericity condition used by the rank-at-least-two assembly.
Its negation supplies one non-generic displayed local factor together with
the order-four coordinate used on journal page 18. -/
@[expose] public def RankOneAssemblyGenericHypothesis
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (S : Subgroup G) : Prop :=
  ∀ A : Subgroup G,
    oneAmax (G := G) (V := V) S A → Nat.card A = 2 →
      RankOneLocalGenericHypothesis (G := G) (V := V) S A

/-- The local commutator subgroup used by the recursive quotient lies in the
ambient odd core. -/
public theorem local_commutator_le_oddCore
    {G : Type u} [Group G] [Finite G]
    (S A : Subgroup G) :
    ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ ≤ oddCore G := by
  let _ : (oddCore G).Normal := pPrimeCore_normal
  exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
    (Subgroup.commutator_le_left (oddCore G) S)

/-- When `A ≤ S` and `S` is elementary abelian, the local commutator
`[C_W(A),S]` still centralizes `A`. -/
public theorem local_commutator_le_centralizer
    {G : Type u} [Group G] [Finite G]
    (S A : Subgroup G) (hS : IsElementaryAbelian 2 S) (hAS : A ≤ S) :
    ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆ ≤
      Subgroup.centralizer (A : Set G) := by
  let _ : IsMulCommutative S := hS.toIsMulCommutative
  let _ : (oddCore G).Normal := pPrimeCore_normal
  have hAnormalS : (A.subgroupOf S).Normal := by infer_instance
  have hSnormA : S ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAS).mp hAnormalS
  have hnormCent : Subgroup.normalizer (A : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (A : Set G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (A : Set G))).mp inferInstance
  have hSnormW : S ≤ Subgroup.normalizer (oddCore G) :=
    Subgroup.le_normalizer_of_normal
  have hSnormInf : S ≤ Subgroup.normalizer
      (oddCore G ⊓ Subgroup.centralizer (A : Set G)) :=
    (le_inf hSnormW (hSnormA.trans hnormCent)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  exact (Subgroup.le_normalizer_iff_commutator_le_left.mp hSnormInf).trans
    inf_le_right

/-- A lifted factor's coordinate identity makes it normalized by the full
elementary abelian Sylow subgroup. Both entries of `[W_A,A_i]` are invariant
under that subgroup, hence so is their commutator. -/
public theorem RankOneLocalFactorCoordinate.normalized
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V]
    (S A F : Subgroup G) (hS : IsElementaryAbelian 2 S)
    (hc : RankOneLocalFactorCoordinate (G := G) (V := V) S A F) :
    S ≤ Subgroup.normalizer (F : Set G) := by
  obtain ⟨B, _, hBS, _, hcomm, _⟩ := hc
  let W := ⁅oddCore G ⊓ Subgroup.centralizer (A : Set G), S⁆
  have hSnormW : S ≤ Subgroup.normalizer W :=
    Subgroup.normalizer_commutator_ge_right _ _
  let _ : IsMulCommutative S := hS.toIsMulCommutative
  have hSnormB : S ≤ Subgroup.normalizer B :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBS).mp inferInstance
  rw [← hcomm, Subgroup.commutator_def]
  apply Subgroup.le_normalizer_closure_iff.mpr
  rintro s hs _ ⟨w, hw, b, hb, rfl⟩
  have hw' : s * w * s⁻¹ ∈ W :=
    (Subgroup.mem_normalizer_iff.mp (hSnormW hs) w).mp hw
  have hb' : s * b * s⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.mp (hSnormB hs) b).mp hb
  have h := Subgroup.commutator_mem_commutator hw' hb'
  change s * ⁅w, b⁆ * s⁻¹ ∈ ⁅W, B⁆
  simpa only [← MulAut.conj_apply, ← map_commutatorElement] using h

end Stellmacher.SectionOne.RankOneThreeGroupAssembly
