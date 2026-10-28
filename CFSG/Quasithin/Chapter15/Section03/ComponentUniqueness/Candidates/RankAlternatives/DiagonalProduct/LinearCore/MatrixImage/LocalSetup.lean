module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore.MatrixImage
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Definitions

/-!+# The source inputs for the linear image calculation

`SourceSetup` collects earlier local conclusions, with the actual Sylow
subgroup and the O_{2,Φ} quotient of 15.3.36. It contains no Borel placement,
matrix coverage or image-generation conclusion. `DiagonalCoordinates`
retains exactly the field, quotient equivalence, conjugation and matrix
chosen in `LinearDiagonalOnTwoQuotient`.

The conditional assembly below unpacks that witness once. It uses the
Borel reduction to return image generation in those same coordinates.
Both the even-exponent PSL₃ case and the field of order four are included.
Borel placement, inner-diagonal coverage and cubic Borel generation remain
three independent obligations. This is not a proof of 15.3.37 without them.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.7, 15.3.11--12, 15.3.33 and 15.3.36--37, printed pp.1122--1135.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage

variable {G : Type*} [Group G]

/-- Earlier source conclusions for the rank-two, single-component branch.
Normality is relative to I; the Sylow assertion is an explicit source input,
not an assertion supplied by the choices in `LocalData`. -/
structure SourceSetup (d : CharacteristicTwo.LocalData G) (I L : Subgroup G) : Prop where
  outside : I ∈ d.Hplus
  sylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = d.S
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  odd_core : pPrimeCore 2 I = ⊥
  component_outside : ¬ L ≤ d.M
  orbit_eq : L = localSpan L d.S
  rank_component : primeRank 3 L = 2
  rank_yplus : primeRank 3 d.Yplus = 2
  rank_overgroup : primeRank 3 I ≤ 2
  theta_eq : theta (d.M ⊓ I) = d.Yplus
  normalizer_eq : I ⊓ normalizer (d.Yplus : Set G) = d.M ⊓ I
  quotient_three : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y)
  yplus_quotient_three : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus)
  intersection_characteristic_two :
    generalizedFitting (d.M ⊓ I : Subgroup G) = pCore 2 (d.M ⊓ I : Subgroup G)
  residual_ne : componentPart d.Yplus L ≠ ⊥
  core_normalizes : d.R ≤ normalizer (L : Set G)
  component_cores_le :
    L.pCoreIn 2 ⊔ (componentPart d.Yplus L).pCoreIn 2 ≤ d.R
  shadow : RankTwo.RankTwoShadow d.Yplus d.S
  characteristic_two_containment : ∀ D : Subgroup G, D ≤ L →
    d.Yplus ⊔ d.S ≤ normalizer (D : Set G) →
    generalizedFitting D = pCore 2 D → D ≤ d.M ⊓ I

/-- The exact two linear model alternatives; the second permits a central two-cover. -/
def LinearCase (L : Subgroup G) (q : ℕ) : Prop :=
  (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧ q = 2 ^ n) ∨
    q = 4

/-- Both source branches give an even exponent for the supplied matrix field. -/
theorem LinearCase.even_card {L : Subgroup G} {q : ℕ} (h : LinearCase L q) :
    ∃ n : ℕ, 0 < n ∧ Even n ∧ q = 2 ^ n := by
  rcases h with ⟨n, hn, heven, _, hq⟩ | hq
  · exact ⟨n, hn, heven, hq⟩
  · exact ⟨2, by decide, by decide, hq⟩

/-- The data already supplied by the diagonal witness, in its original field. -/
structure DiagonalCoordinates (L : Subgroup G) (y : G) (F : Type*) [Field F] where
  e : (L ⧸ pCore 2 L) ≃* PSL(3,F)
  conjugation : MulAut L
  matrix : Matrix.GeneralLinearGroup (Fin 3) F
  conjugation_eq : ConjugationOn L y conjugation
  outer : Matrix.PSL3.OuterSolvable.linearConj F matrix ∉ MulAut.innerSubgroup PSL(3,F)
  compatible : ∀ x : L, e (QuotientGroup.mk' (pCore 2 L) (conjugation x)) =
    Matrix.PSL3.OuterSolvable.linearConj F matrix (e (QuotientGroup.mk' (pCore 2 L) x))

/-- A representation of precisely the existing witness, without rechoosing its actor. -/
theorem diagonalCoordinates_iff {L : Subgroup G} {y : G} {q : ℕ} :
    LinearDiagonalOnTwoQuotient L y q ↔
      ∃ (F : Type) (_ : Field F) (_ : Finite F),
        Nat.card F = q ∧ Nonempty (DiagonalCoordinates L y F) := by
  constructor
  · rintro ⟨F, hF, hfin, hcard, e, α, d₀, hc, ho, he⟩
    exact ⟨F, hF, hfin, hcard, ⟨⟨e, α, d₀, hc, ho, he⟩⟩⟩
  · rintro ⟨F, hF, hfin, hcard, ⟨w⟩⟩
    exact ⟨F, hF, hfin, hcard, w.e, w.conjugation, w.matrix,
      w.conjugation_eq, w.outer, w.compatible⟩

variable [Finite G]

/-- Simplicity and perfectness required by model automorphism results are
inherited from the actual component. No independent model certification is needed. -/
theorem SourceSetup.model_properties {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    {H : Type*} [Group H] (e : (L ⧸ pCore 2 L) ≃* H) :
    IsSimpleGroup H ∧ Group.IsPerfect H ∧ ¬ Group.IsSolvable H := by
  let eL := subgroupOfEquivOfLe h.component_le
  let := h.component.2
  let : IsSimpleGroup ((L.subgroupOf I) ⧸ center (L.subgroupOf I)) :=
    IsQuasisimple.simple
  let eZ := QuotientGroup.quotientMulEquivOfEq
    (component_center_eq_twoCore h.component h.odd_core)
  let : IsSimpleGroup ((L.subgroupOf I) ⧸ pCore 2 (L.subgroupOf I)) :=
    eZ.symm.isSimpleGroup
  let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf I)) (pCore 2 L)
    eL (pCore_map_iso 2 eL)
  let : IsSimpleGroup H := (eQ.trans e).symm.isSimpleGroup
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := eL.toMonoidHom) eL.surjective
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective
    (f := quotientMap e) (quotientMap_surjective e)
  exact ⟨inferInstance, inferInstance, Group.IsPerfect.not_isSolvable H⟩

/-- The supplied local Sylow gives a Sylow in the supplied quotient coordinates. -/
theorem SourceSetup.quotient_sylow {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    {F : Type*} [Field F] (e : (L ⧸ pCore 2 L) ≃* PSL(3,F)) :
    ∃ T : Sylow 2 PSL(3,F),
      (T : Subgroup PSL(3,F)) = (d.S.subgroupOf L).map (quotientMap e) := by
  obtain ⟨P, hP⟩ := h.sylow
  exact MatrixImage.quotient_sylow h.component_le h.component.1 P hP e

/-- Conditional assembly in fixed coordinates. All three additional inputs still
have to be proved from the source setup and the concrete model. -/
theorem image_le_of_source_borel {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (y : d.Yplus) (hy : orderOf y = 3)
    {F : Type*} [Field F] (w : DiagonalCoordinates L (y : G) F)
    (b : BorelPlacement d.Yplus d.S d.M L hn w.e)
    (hlinear : ∀ x : d.Yplus, orderOf x = 3 →
      quotientAction hn w.e x ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F)
    (hmodel : CubicBorelGeneration F) :
    (quotientAction hn w.e).range ≤
      ((componentPart d.Yplus L).subgroupOf d.Yplus).map (quotientAction hn w.e) ⊔
        zpowers (quotientAction hn w.e y) :=
  image_le_of_borel h.theta_eq h.component_le hn w.e y hy
    w.conjugation w.matrix w.conjugation_eq w.outer w.compatible b hlinear hmodel

/-- Unpack the supplied linear witness once and attach the image conclusion to
exactly that field, quotient equivalence and matrix. The Borel, coverage and
cubic-model premises are deliberately still explicit. -/
theorem image_witness_of_local_inputs {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (h : SourceSetup d I L)
    (hn : d.Yplus ≤ normalizer (L : Set G))
    (y : d.Yplus) (hy : orderOf y = 3) {q : ℕ}
    (hcase : LinearCase L q) (hdiag : LinearDiagonalOnTwoQuotient L y q)
    (hplacement : ∀ (F : Type) [Field F] [Finite F], LinearCase L (Nat.card F) →
      ∀ w : DiagonalCoordinates L (y : G) F,
        Nonempty (BorelPlacement d.Yplus d.S d.M L hn w.e))
    (hlinear : ∀ (F : Type) [Field F] [Finite F], LinearCase L (Nat.card F) →
      ∀ (w : DiagonalCoordinates L (y : G) F) (x : d.Yplus), orderOf x = 3 →
        quotientAction hn w.e x ∈ Matrix.PSL3.OuterSolvable.innerDiagonal F)
    (hmodel : ∀ (F : Type) [Field F] [Finite F],
      (∃ n : ℕ, 0 < n ∧ Even n ∧ Nat.card F = 2 ^ n) → CubicBorelGeneration F) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = q ∧
      ∃ w : DiagonalCoordinates L (y : G) F,
        (quotientAction hn w.e).range ≤
          ((componentPart d.Yplus L).subgroupOf d.Yplus).map (quotientAction hn w.e) ⊔
            zpowers (quotientAction hn w.e y) := by
  obtain ⟨F, hF, hfin, hcard, ⟨w⟩⟩ := diagonalCoordinates_iff.mp hdiag
  have hfield : LinearCase L (Nat.card F) := hcard.symm ▸ hcase
  obtain ⟨b⟩ := hplacement F hfield w
  exact ⟨F, hF, hfin, hcard, w,
    image_le_of_source_borel h hn y hy w b (hlinear F hfield w)
      (hmodel F hfield.even_card)⟩

end CFSG.Quasithin.Chapter15.Section03.Candidates.LinearCore.MatrixImage
