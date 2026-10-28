module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.HexagonStructure.SuzukiCartanAction
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.HexagonStructure.SuzukiSections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.SuzukiLocal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocalIdentification

/-!
# Original and geometric mixed Suzuki centralizer exclusion

Use the original factor maps and proved local identifications to construct
the actual Suzuki R_j and root Sylow. The published regular (2B) producers
discharge both remainder-in-kernel inputs. The source three-core centralizes
this R_j and every conjugate of its root; the opposite linear marking gives
the exact two-root centralizer product in the same radical.

The final contradiction uses its actual induced action and Frattini quotient.
The square-profile applications retain exactly the earlier Fong--Seitz (1J)
assertion about the product of the two canonical root orders. Quotient
applications use the literal Q.q on the original S, and the general marked
applications also apply to the universal geometric numerator.

Original-factor perfectness is retained only where the existing identification
producers require it; it is not a hypothesis of the underlying Theory exclusion.
The marked variant can consume an independently transported linear marking
without original linear perfectness. No full-panel model, Cartan centralization,
or numerical representation bound is assumed. Equal Suzuki, unitary and
solvable/small cases still require their own source arguments.

Source: Fong--Seitz I (1J), (5C), (6C), printed pp.6,25--26,39--40;
DGS Theorem D, printed p.224.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h split

/-- The same original factor gives the actual Cartan centralization.
The published regular Suzuki (2B) theorem discharges the kernel input. -/
theorem original_suzuki_threeCartan_centralizes (j : Fin 2)
    (hp : Group.IsPerfect (L j))
    {m : ℕ} (μ : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m) :
    threeCartan Q ≤ centralizer (rankOne Q split j : Set (X ⧸ Q.D)) ∧
      ∀ w, rootAt Q split j w ≤ centralizer (threeCartan Q : Set (X ⧸ Q.D)) := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  have hm := MarkedLocal.suzuki_parameter_pos j hp μ
  have hK := MarkedLocal.suzuki_remainder_le_kernel Q e h split j T hT hm μ
  let a := MarkedLocal.suzukiRankOneEquiv Q e h split j hp T hT μ
  let ν := originalSuzukiRootEquiv Q e h split j hp T hT μ
  let s := UnitarySource.actorReflection Q split j
  exact ⟨threeCartan_centralizes_suzuki_rankOne Q split j hK hm a ν s,
    threeCartan_centralizes_suzuki_roots Q split j hK hm a ν s⟩

/-- Actual original/geometric root coordinates identify the centralizer
product. Both nonlinear and linear kernel inclusions are discharged. -/
theorem original_mixed_suzuki_centralizer_product
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hthree : 3 ∣ Nat.card F - 1) :
    (((MarkedLocal.sylowMap Q e h).range ⊓
      rightConjugate (MarkedLocal.sylowMap Q e h).range
        ((UnitarySource.actorReflection Q split j).val : X ⧸ Q.D)) ⊓
      centralizer (threeCartan Q : Set (X ⧸ Q.D)) : Set (X ⧸ Q.D)) =
        (rootAt Q split j (Q.simple i) : Set (X ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i*Q.simple j) : Set (X ⧸ Q.D)) := by
  let := h.finite_local i
  obtain ⟨Ti,hTi⟩ := h.sylow i
  let si := UnitarySource.actorReflection Q split i
  let sj := UnitarySource.actorReflection Q split j
  have hp := radical_centralizer_product Q split hhex i j hij (threeCartan Q) (threeCartan_le_cartan Q)
    (linear_threeCartan_nontrivial_fixedFree Q split i
      (MarkedLocal.linear_remainder_le_kernel Q e h split i Ti hTi μi)
      (MarkedLocal.linearLocalEquiv Q e h split i hpi Ti hTi μi) si hthree).2
    (original_suzuki_threeCartan_centralizes Q e h split j hpj μj).2
  rw [marked_radical_eq h Q e split j sj.val sj.class_eq] at hp
  exact hp

/-- The mixed (6C) contradiction from original quotient markings. These
perfect-factor hypotheses are exactly those of the existing model producers;
the underlying Theory theorem has no perfectness premise. -/
theorem original_mixed_suzuki_exclusion
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hthree : 3 ∣ Nat.card F - 1) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hm := MarkedLocal.suzuki_parameter_pos j hpj μj
  exact no_mixed_suzuki_of_linear_cubic Q split hhex i j hij
    (MarkedLocal.linear_remainder_le_kernel Q e h split i Ti hTi μi)
    (MarkedLocal.suzuki_remainder_le_kernel Q e h split j Tj hTj hm μj)
    (MarkedLocal.linearLocalEquiv Q e h split i hpi Ti hTi μi)
    (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
    hthree hm (MarkedLocal.suzukiRankOneEquiv Q e h split j hpj Tj hTj μj)
    (originalSuzukiRootEquiv Q e h split j hpj Tj hTj μj)

/-- A transported linear local marking can be consumed without requiring
the original linear factor to be perfect. Only the Suzuki model producer's
existing premise remains; both actual (2B) inclusions are proved. -/
theorem marked_mixed_suzuki_exclusion
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (μlocal : localGroup Q split i ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hthree : 3 ∣ Nat.card F - 1) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  have hm := MarkedLocal.suzuki_parameter_pos j hpj μj
  exact no_mixed_suzuki_of_linear_cubic Q split hhex i j hij
    (MarkedLocal.linear_remainder_le_kernel Q e h split i Ti hTi μi)
    (MarkedLocal.suzuki_remainder_le_kernel Q e h split j Tj hTj hm μj)
    μlocal (UnitarySource.actorReflection Q split i) (UnitarySource.actorReflection Q split j)
    hthree hm (MarkedLocal.suzukiRankOneEquiv Q e h split j hpj Tj hTj μj)
    (originalSuzukiRootEquiv Q e h split j hpj Tj hTj μj)

/-- Use the exact earlier (1J) square profile instead of an extra parity
or cubic-divisibility assumption. All local actions are on the same Q. -/
theorem original_mixed_suzuki_exclusion_of_square_profile
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j))) : False := by
  let := h.finite_local i
  let := h.finite_local j
  obtain ⟨Ti,hTi⟩ := h.sylow i
  obtain ⟨Tj,hTj⟩ := h.sylow j
  exact original_mixed_suzuki_exclusion Q e h split hhex i j hij hpi hpj μi μj
    (linear_cubic_of_suzuki_square_profile Q split i j
      (MarkedLocal.linear_remainder_le_kernel Q e h split i Ti hTi μi)
      (MarkedLocal.linearLocalEquiv Q e h split i hpi Ti hTi μi)
      (originalSuzukiRootEquiv Q e h split j hpj Tj hTj μj) hsquare)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure

namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- The source centralizer product under the literal quotient map Q.q. -/
theorem quotient_mixed_suzuki_centralizer_product
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hthree : 3 ∣ Nat.card F - 1) :
    ((((S.subgroupOf (generated L S)).map Q.q) ⊓
      rightConjugate ((S.subgroupOf (generated L S)).map Q.q)
        ((UnitarySource.actorReflection Q split j).val : (generated L S) ⧸ Q.D)) ⊓
      centralizer (threeCartan Q : Set ((generated L S) ⧸ Q.D)) : Set ((generated L S) ⧸ Q.D)) =
        (rootAt Q split j (Q.simple i) : Set ((generated L S) ⧸ Q.D)) *
        (rootAt Q split j (Q.simple i*Q.simple j) : Set ((generated L S) ⧸ Q.D)) := by
  rw [quotient_sourceS_image_eq_unipotent h Q split]
  have hh := original_mixed_suzuki_centralizer_product Q (originalMarkedIso Q) h split
    hhex i j hij hpi hpj μi μj hthree
  rwa [MarkedLocal.sylow_range Q (originalMarkedIso Q) h split] at hh

/-- Original-source exclusion with all actual quotient and factor maps. -/
theorem quotient_mixed_suzuki_exclusion
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hthree : 3 ∣ Nat.card F - 1) : False :=
  original_mixed_suzuki_exclusion Q (originalMarkedIso Q) h split
    hhex i j hij hpi hpj μi μj hthree

/-- The full literal source-map application with the earlier (1J) premise. -/
theorem quotient_mixed_suzuki_exclusion_of_square_profile
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (h : HypothesisF11 L S) (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (hhex : rotationOrder Q = 6) (i j : Fin 2) (hij : i ≠ j)
    (hpi : Group.IsPerfect (L i)) (hpj : Group.IsPerfect (L j))
    (μi : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    {m : ℕ} (μj : ((L j) ⧸ pCore 2 (L j)) ≃* SuzukiMatrixGroup m)
    (hsquare : IsSquare (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j))) : False :=
  original_mixed_suzuki_exclusion_of_square_profile Q (originalMarkedIso Q) h split
    hhex i j hij hpi hpj μi μj hsquare

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.HexagonStructure
