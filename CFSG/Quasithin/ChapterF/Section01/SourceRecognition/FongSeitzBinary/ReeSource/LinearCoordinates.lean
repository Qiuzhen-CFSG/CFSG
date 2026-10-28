module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.RankOneCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearRootCoordinates

/-!
# Binary-inclusive linear root coordinates on the source quotient

A natural PSL₂ marking of the faithful parabolic quotient identifies its
full Borel with a Sylow normalizer. The projective line has |F| + 1 points,
so the general panel-kernel argument identifies the actual simple root
with that entire model Sylow. Its additive field coordinates then give
an injective parameter homomorphism into the same source quotient, with
exact root range and the original model-projection formula.

This applies in characteristic two including F₂ and does not assume a
perfect rank-one factor. The natural rank-one marking is an earlier input,
not a conclusion of this module; it must be supplied by the rank-one
catalogue/row-selection owner. In particular this constructs one root field,
not the common Ree field or its mixed commutators. Source: Fong–Seitz I (2A),
pp.7–8, and II §10, pp.221–222; the natural projective action is reused
from the project's existing rank-one proofs.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X F : Type*} [Group X] [Field F] [Finite F] [CharP F 2]
  {P : Fin 2 → Subgroup X}

/-- The full natural PSL₂ panel has one more point than a Sylow root, including F₂. -/
theorem linear_normalizer_index (T : Sylow 2 PSL(2,F)) :
    (normalizer (T : Set PSL(2,F))).index = 1 + Nat.card T := by
  obtain ⟨x, hx⟩ := Linear.normalizer_eq_point_stabilizer F T
  rw [hx]
  change Nat.card (PSL(2,F) ⧸ MulAction.stabilizer PSL(2,F) x) = _
  have hb : Function.Bijective (MulAction.ofQuotientStabilizer PSL(2,F) x) := by
    refine ⟨MulAction.injective_ofQuotientStabilizer _ _, ?_⟩
    intro y
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq PSL(2,F) x y
    exact ⟨QuotientGroup.mk g,hg⟩
  rw [Nat.card_congr (Equiv.ofBijective _ hb),
    Projectivization.card_of_finrank_two F (Fin 2 → F) (by simp),
    ← Nat.card_congr (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T).toEquiv]
  rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.add_comm]

variable (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* PSL(2,F)) (T : Sylow 2 PSL(2,F))
  (hB : (quotientBorel Q i).map μ.toMonoidHom = normalizer (T : Set PSL(2,F)))

/-- A natural PSL₂ marking gives additive coordinates on the actual source root. -/
def linearRootEquiv : simpleRoot Q split i ≃* Multiplicative F :=
  (modelRootEquiv Q split i μ T hB (linear_normalizer_index T)).trans
    (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T).symm

@[simp] theorem linearRootEquiv_model (r : simpleRoot Q split i) :
    ((BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T) (linearRootEquiv Q split i μ T hB r) : PSL(2,F)) =
      μ (rootProjection Q split i r) := by
  change ((BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T)
    ((BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T).symm
      (modelRootEquiv Q split i μ T hB (linear_normalizer_index T) r)) : PSL(2,F)) = _
  rw [MulEquiv.apply_symm_apply]
  exact modelRootEquiv_apply _ _ _ _ _ _ _ _

/-- The field maps into the same source quotient with its simple root as range. -/
def linearParameter : Multiplicative F →* X ⧸ Q.D :=
  (simpleRoot Q split i).subtype.comp (linearRootEquiv Q split i μ T hB).symm.toMonoidHom

theorem linearParameter_range : (linearParameter Q split i μ T hB).range = simpleRoot Q split i := by
  rw [linearParameter, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (linearRootEquiv Q split i μ T hB).symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem linearParameter_injective : Function.Injective (linearParameter Q split i μ T hB) :=
  (simpleRoot Q split i).subtype_injective.comp (linearRootEquiv Q split i μ T hB).symm.injective

theorem linearParameter_add (a b : F) :
    linearParameter Q split i μ T hB (Multiplicative.ofAdd (a+b)) =
      linearParameter Q split i μ T hB (Multiplicative.ofAdd a) *
        linearParameter Q split i μ T hB (Multiplicative.ofAdd b) := map_mul _ _ _

/-- The chosen parameter in the faithful quotient is the literal model root parameter. -/
theorem linearParameter_projection (a : Multiplicative F) :
    μ (rootProjection Q split i ((linearRootEquiv Q split i μ T hB).symm a)) =
      (BenderSuzuki.ZD.Linear.psl2SylowEquivAdditive T a : PSL(2,F)) := by
  rw [← linearRootEquiv_model Q split i μ T hB, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
