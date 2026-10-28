module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UniformRoots
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.LocalStructure
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

/-!
# Additive field coordinates on a source linear simple root

The original local quotient isomorphism to PSL₂(F) carries its quotient
Sylow to a concrete Sylow. The literal endpoint panel identifies with the
local Borel cosets and then with the natural projective line. Its size is
|F|+1, so the canonical simple root has order |F|. The previously proved
injective root projection is therefore onto that Sylow.

Compose with the concrete additive-field Sylow isomorphism. The resulting
root parametrization is injective, has exactly the canonical root as its
range, and retains the equation through the original local quotient and
specified model isomorphism. This supplies individual linear root fields;
it does not identify the fields on different roots, Weyl scalings or any
mixed positive/negative commutator identity.

Source: Aschbacher–Smith F.1.1–3, pp.259–260; DGS, Groups and Graphs,
Part II, pp.80–81 and Theorem D, p.224. The root count uses the proved
finite split panel coordinates, without restricting the dihedral parameter.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}

private theorem linear_normalizer_cosets_card (T : Sylow 2 PSL(2,F)) :
    Nat.card (PSL(2,F) ⧸ sylowNormalizer T) = Nat.card F + 1 := by
  obtain ⟨x, hx⟩ := Linear.normalizer_eq_point_stabilizer F T
  change Nat.card (PSL(2,F) ⧸ normalizer (T : Set PSL(2,F))) = _
  rw [hx]
  have hb : Function.Bijective (MulAction.ofQuotientStabilizer PSL(2,F) x) := by
    refine ⟨MulAction.injective_ofQuotientStabilizer _ _, ?_⟩
    intro y
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2,F) x y
    exact ⟨QuotientGroup.mk g, hg⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hb)]
  exact Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp)

variable (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (i : Fin 2) [Finite (L i)] (hp : Group.IsPerfect (L i))
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))

/-- The concrete model Sylow is the image of the original quotient Sylow. -/
def linearModelSylow : Sylow 2 PSL(2,F) :=
  (quotientSylow T).mapSurjective (f := μ.toMonoidHom) μ.surjective

/-- The model map restricted to that same Sylow. -/
def linearSylowEquiv : quotientSylow T ≃* linearModelSylow i T μ :=
  (quotientSylow T : Subgroup ((L i) ⧸ pCore 2 (L i))).equivMapOfInjective
    μ.toMonoidHom μ.injective

include e h hT μ in
/-- The actual canonical simple root has the order of the supplied local field. -/
theorem simpleRoot_card_linear : Nat.card (simpleRoot Q split i) = Nat.card F := by
  have he := Nat.card_congr ((localBorelPanel Q e h i).symm.trans
    (localBorelModelCosetEquiv (L i) S T hT μ))
  have hindex := singleton_parabolic_root_index Q split i
  change Nat.card (Panel Q i) = 1 + Nat.card (simpleRoot Q split i) at hindex
  rw [linear_normalizer_cosets_card, hindex] at he
  omega

/-- The root-to-field homomorphism uses the original lift, local quotient,
model isomorphism and Sylow additive coordinates in that order. -/
def simpleRootLinearMap : simpleRoot Q split i →* Multiplicative F :=
  (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearModelSylow i T μ)).symm.toMonoidHom.comp
    ((linearSylowEquiv i T μ).toMonoidHom.comp
      (simpleRootSylowProjection Q e h split i hp T hT))

theorem simpleRootLinearMap_bijective :
    Function.Bijective (simpleRootLinearMap Q e h split i hp T hT μ) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  constructor
  · exact (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive _).symm.injective.comp
      ((linearSylowEquiv i T μ).injective.comp
        (simpleRootSylowProjection_injective Q e h split i hp T hT))
  · exact (simpleRoot_card_linear Q e h split i T hT μ).trans
      (Nat.card_congr Multiplicative.ofAdd)

/-- Additive field coordinates on the literal simple root, not only an order formula. -/
def simpleRootLinearEquiv : simpleRoot Q split i ≃* Multiplicative F :=
  MulEquiv.ofBijective (simpleRootLinearMap Q e h split i hp T hT μ)
    (simpleRootLinearMap_bijective Q e h split i hp T hT μ)

@[simp] theorem simpleRootLinearEquiv_model (r : simpleRoot Q split i) :
    ((BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearModelSylow i T μ))
      (simpleRootLinearEquiv Q e h split i hp T hT μ r) : PSL(2,F)) =
      μ (simpleRootProjection Q e h split i hp r) := by
  change ((BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearModelSylow i T μ))
      ((BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive (linearModelSylow i T μ)).symm
        (linearSylowEquiv i T μ (simpleRootSylowProjection Q e h split i hp T hT r))) : PSL(2,F)) = _
  rw [MulEquiv.apply_symm_apply]
  change μ (simpleRootSylowProjection Q e h split i hp T hT r : (L i) ⧸ pCore 2 (L i)) = _
  rw [simpleRootSylowProjection_coe]


/-- Embed field addition into the actual source quotient along the canonical root. -/
def linearRootParameter : Multiplicative F →* X ⧸ Q.D :=
  (simpleRoot Q split i).subtype.comp
    (simpleRootLinearEquiv Q e h split i hp T hT μ).symm.toMonoidHom

@[simp] theorem linearRootParameter_range :
    (linearRootParameter Q e h split i hp T hT μ).range = simpleRoot Q split i := by
  rw [linearRootParameter, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (simpleRootLinearEquiv Q e h split i hp T hT μ).symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem linearRootParameter_injective :
    Function.Injective (linearRootParameter Q e h split i hp T hT μ) :=
  (simpleRoot Q split i).subtype_injective.comp
    (simpleRootLinearEquiv Q e h split i hp T hT μ).symm.injective

/-- Field addition has exactly the multiplication law of this source root. -/
theorem linearRootParameter_add (a b : F) :
    linearRootParameter Q e h split i hp T hT μ (Multiplicative.ofAdd (a+b)) =
      linearRootParameter Q e h split i hp T hT μ (Multiplicative.ofAdd a) *
        linearRootParameter Q e h split i hp T hT μ (Multiplicative.ofAdd b) :=
  map_mul _ _ _

omit [Finite (L i)] in
include e h hp in
/-- Extract a field of the original parameter and an actual additive root
isomorphism from the supplied PSL₂ quotient witness. -/
theorem exists_linear_root_coordinates {n : ℕ}
    (hmodel : ClassicalGroup.IsPSL ((L i) ⧸ pCore 2 (L i)) 2 (2^n)) :
    Nat.card (simpleRoot Q split i) = 2^n ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2),
        Nat.card K = 2^n ∧ Nonempty (simpleRoot Q split i ≃* Multiplicative K) := by
  let := h.finite_local i
  obtain ⟨K, hK, hf, hcard, ⟨μ⟩⟩ := hmodel
  let : Fintype K := Fintype.ofFinite K
  let : CharP K 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  obtain ⟨T, hT⟩ := h.sylow i
  exact ⟨(simpleRoot_card_linear Q e h split i T hT μ).trans hcard,
    K, hK, hf, inferInstance, hcard, ⟨simpleRootLinearEquiv Q e h split i hp T hT μ⟩⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
