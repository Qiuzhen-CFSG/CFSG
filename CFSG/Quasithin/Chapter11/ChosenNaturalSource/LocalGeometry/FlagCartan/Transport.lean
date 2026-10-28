module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
public import Mathlib.Algebra.Module.ZMod
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# Transporting natural flag geometry through the chosen quotient

The coordinate projection is the binary intertwiner composed with the original
map V → V/C_V(L). Its kernel is exactly C_V(L). Conjugation by a subgroup
normalizing both L and V descends through this projection, producing the actual
binary action on the marked field space. Invariance under this action is
equivalent to normalization of the ambient preimage; in particular this applies
to the original Sylow subgroup T, without a field-linearity assumption on T.

For elements of L the descended action is precisely the supplied SL₃, Sp₄ or
G₂ marking. Thus the original N_L(U) maps onto the marked subspace stabilizer.
The induced map on solvable residuals has two-group kernel and gives an
isomorphism of their literal two-core quotients. Finally, field dimension
proves V₃ = V in the SL₃ branch. These are transport and local applications;
model flag existence, uniqueness and the model residual calculations remain
separate obligations.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.0.2 and the opening of §11.1, printed pp.759--761.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative MatrixGroups
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
namespace Coordinates
variable (c : Coordinates D F)

/-- The original quotient followed by this marking's binary intertwiner. -/
@[expose] def projection : V →* Multiplicative c.Space :=
  c.linearEquiv.toAddEquiv.toMultiplicative.toMonoidHom.comp D.toCentralQuotient

/-- Every coordinate vector has an original representative in V. -/
theorem projection_surjective : Function.Surjective c.projection :=
  c.linearEquiv.toAddEquiv.toMultiplicative.surjective.comp D.toCentralQuotient_surjective

/-- The coordinate kernel is precisely the original relative centralizer. -/
theorem projection_eq_one_iff (v : V) :
    c.projection v = 1 ↔ (v : G) ∈ centralizer (L : Set G) := by
  change c.linearEquiv.toAddEquiv.toMultiplicative (D.toCentralQuotient v) = 1 ↔ _
  rw [map_eq_one_iff _ c.linearEquiv.toAddEquiv.toMultiplicative.injective]
  exact quotient_eq_one_iff D v

variable {A : Subgroup G} (hL : A ≤ normalizer (L : Set G))
    (hV : A ≤ normalizer (V : Set G))

private def conjugationEnd (a : A) : Multiplicative c.Space →* Multiplicative c.Space :=
  c.projection.liftOfSurjective c.projection_surjective
    ⟨c.projection.comp (V.normalizerMonoidHom (inclusion hV a)).toMonoidHom, by
      intro v hv
      apply (c.projection_eq_one_iff _).mpr
      have hvC := (c.projection_eq_one_iff v).mp hv
      exact ((normalizer_le_normalizer_centralizer L (hL a.property)) v.val).mp hvC⟩

private theorem conjugationEnd_projection (a : A) (v : V) :
    c.conjugationEnd hL hV a (c.projection v) =
      c.projection (V.normalizerMonoidHom (inclusion hV a) v) := by
  unfold conjugationEnd
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- Conjugation on the marked quotient, retaining the actual ambient actor. -/
def conjugationAction : Representation (ZMod 2) A c.Space where
  toFun a := (AddMonoidHom.toMultiplicative.symm (c.conjugationEnd hL hV a)).toZModLinearMap 2
  map_one' := by
    ext x
    obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    change (c.conjugationEnd hL hV 1 (Multiplicative.ofAdd x)).toAdd = x
    rw [← hv, c.conjugationEnd_projection]
    simpa using congrArg Multiplicative.toAdd hv
  map_mul' a b := by
    ext x
    obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    change (c.conjugationEnd hL hV (a * b) (Multiplicative.ofAdd x)).toAdd =
      (c.conjugationEnd hL hV a (c.conjugationEnd hL hV b (Multiplicative.ofAdd x))).toAdd
    rw [← hv, c.conjugationEnd_projection, c.conjugationEnd_projection,
      c.conjugationEnd_projection]
    rw [map_mul, map_mul, MulAut.mul_apply]

/-- The descended action agrees with the original conjugation map. -/
theorem conjugationAction_projection (a : A) (v : V) :
    c.conjugationAction hL hV a (c.projection v).toAdd =
      (c.projection (V.normalizerMonoidHom (inclusion hV a) v)).toAdd :=
  congrArg Multiplicative.toAdd (c.conjugationEnd_projection hL hV a v)

/-- Actual ambient normalization is equivalent to coordinate invariance. -/
theorem normalizes_preimage_iff (U : Submodule F.Carrier c.Space) :
    A ≤ normalizer (c.preimage U : Set G) ↔
      ∀ a : A, ∀ x ∈ U, c.conjugationAction hL hV a x ∈ U := by
  constructor
  · intro h a x hx
    obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    have hvU : (v : G) ∈ c.preimage U := (c.mem_preimage U v).mpr (by
      change (c.projection v).toAdd ∈ U
      rw [hv]
      exact hx)
    have hw := (h a.property v.val).mp hvU
    have hw' := (c.mem_preimage U (V.normalizerMonoidHom (inclusion hV a) v)).mp hw
    change (c.projection (V.normalizerMonoidHom (inclusion hV a) v)).toAdd ∈ U at hw'
    rw [← c.conjugationAction_projection hL hV, hv] at hw'
    exact hw'
  · intro h
    apply le_normalizer_iff.mpr
    intro a ha v hv
    have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
    let v' : V := ⟨v, hvV⟩
    let a' : A := ⟨a, ha⟩
    apply (c.mem_preimage U (V.normalizerMonoidHom (inclusion hV a') v')).mpr
    change (c.projection (V.normalizerMonoidHom (inclusion hV a') v')).toAdd ∈ U
    rw [← c.conjugationAction_projection hL hV]
    exact h a' _ ((c.mem_preimage U v').mp hv)

end Coordinates

namespace Coordinates
variable (c : Coordinates D F)

/-- The full group belonging to this same natural-action marking. -/
@[expose] def ModelGroup : Type := match c with
  | .sl3 _ => Matrix.SpecialLinearGroup (Fin 3) F.Carrier
  | .sp4 _ => Matrix.symplecticGroup (Fin 2) F.Carrier
  | .g2 _ => Atlas.G2.Model F.Carrier

instance : Group c.ModelGroup := match c with
  | .sl3 _ => inferInstanceAs (Group (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
  | .sp4 _ => inferInstanceAs (Group (Matrix.symplecticGroup (Fin 2) F.Carrier))
  | .g2 _ => inferInstanceAs (Group (Atlas.G2.Model F.Carrier))

/-- The actual field-linear natural action of the marked model group. -/
@[expose] def modelAction : Representation F.Carrier c.ModelGroup c.Space := by
  cases c with
  | sl3 m => exact specialLinearNatural 3
  | sp4 m => exact symplecticNatural 2
  | g2 m => exact g2Natural F.Carrier

/-- The original isomorphism from L/O₂(L), including its full center. -/
@[expose] def groupEquiv : (L ⧸ pCore 2 L) ≃* c.ModelGroup := by
  cases c with
  | sl3 m => exact m.groupEquiv
  | sp4 m => exact m.groupEquiv
  | g2 m => exact m.groupEquiv

/-- The supplied binary intertwiner implements the marked field action. -/
theorem intertwines (g : L ⧸ pCore 2 L) (v : D.chosenCentralQuotient) :
    c.linearEquiv (D.centralQuotientAction g v) =
      c.modelAction (c.groupEquiv g) (c.linearEquiv v) := by
  cases c with
  | sl3 m => exact m.intertwines g v
  | sp4 m => exact m.intertwines g v
  | g2 m => exact m.intertwines g v

/-- The original projection from L followed by the supplied group marking. -/
@[expose] def quotientMap : L →* c.ModelGroup :=
  c.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- The original component maps onto its marked model group. -/
theorem quotientMap_surjective : Function.Surjective c.quotientMap :=
  c.groupEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

instance : Finite c.ModelGroup :=
  Finite.of_surjective c.quotientMap c.quotientMap_surjective

/-- For L-elements the model action equals original conjugation on the quotient. -/
theorem projection_component_conjugation (l : L) (v : V) :
    (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
      c.modelAction (c.quotientMap l) (c.projection v).toAdd := by
  let w : D.space := (D.spaceEquiv.symm v).toAdd
  have hw : (w.val.toMul.val : G) = (v : G) :=
    (D.spaceEquiv_apply w).symm.trans
      (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
  have he : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
      V.normalizerMonoidHom (inclusion D.normalizes l) v := by
    apply Subtype.ext
    rw [D.spaceEquiv_apply]
    change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
    rw [hw]
    rfl
  change c.linearEquiv (Submodule.Quotient.mk
    (D.spaceEquiv.symm (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd) = _
  rw [← he, D.spaceEquiv.symm_apply_apply]
  exact c.intertwines (QuotientGroup.mk' (pCore 2 L) l) (Submodule.Quotient.mk w)

/-- The ambient L-invariance test in the marked natural representation. -/
theorem component_normalizes_preimage_iff (U : Submodule F.Carrier c.Space) :
    L ≤ normalizer (c.preimage U : Set G) ↔
      ∀ g : c.ModelGroup, ∀ x ∈ U, c.modelAction g x ∈ U := by
  have he (l : L) (x : c.Space) :
      c.conjugationAction L.le_normalizer D.normalizes l x =
        c.modelAction (c.quotientMap l) x := by
    obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    rw [← show (c.projection v).toAdd = x from congrArg Multiplicative.toAdd hv,
      c.conjugationAction_projection, c.projection_component_conjugation]
  rw [c.normalizes_preimage_iff L.le_normalizer D.normalizes]
  constructor
  · intro h g x hx
    obtain ⟨l, rfl⟩ := c.quotientMap_surjective g
    rw [← he]
    exact h l x hx
  · intro h l x hx
    rw [he]
    exact h _ x hx

/-- Individual normalizer membership uses the same model action and original lift. -/
theorem mem_normalizer_preimage_iff (U : Submodule F.Carrier c.Space) (l : L) :
    (l : G) ∈ normalizer (c.preimage U : Set G) ↔
      ∀ x, c.modelAction (c.quotientMap l) x ∈ U ↔ x ∈ U := by
  constructor
  · intro h x
    obtain ⟨v, hv⟩ := c.projection_surjective (Multiplicative.ofAdd x)
    have he : (c.projection v).toAdd = x := congrArg Multiplicative.toAdd hv
    rw [← he, ← c.projection_component_conjugation]
    exact (c.mem_preimage U (V.normalizerMonoidHom (inclusion D.normalizes l) v)).symm.trans
      ((h v.val).symm.trans (c.mem_preimage U v))
  · intro h v
    constructor
    · intro hv
      have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
      let v' : V := ⟨v, hvV⟩
      apply (c.mem_preimage U (V.normalizerMonoidHom (inclusion D.normalizes l) v')).mpr
      change (c.projection (V.normalizerMonoidHom (inclusion D.normalizes l) v')).toAdd ∈ U
      rw [c.projection_component_conjugation]
      exact (h _).mpr ((c.mem_preimage U v').mp hv)
    · intro hv
      have hvV : v ∈ V := (D.normalizes l.property v).mpr
        (D.centralQuotientPreimage_le _ hv)
      let v' : V := ⟨v, hvV⟩
      apply (c.mem_preimage U v').mpr
      apply (h _).mp
      change c.modelAction (c.quotientMap l) (c.projection v').toAdd ∈ U
      rw [← c.projection_component_conjugation]
      exact (c.mem_preimage U (V.normalizerMonoidHom (inclusion D.normalizes l) v')).mp hv

/-- The setwise stabilizer of a field subspace under the marked natural action. -/
@[expose] def modelStabilizer (U : Submodule F.Carrier c.Space) : Subgroup c.ModelGroup :=
  BinaryOffender.subspaceStabilizer (restrictScalars (k := ZMod 2) c.modelAction)
    (U.restrictScalars (ZMod 2))

/-- The actual local normalizer is the full preimage of the marked stabilizer. -/
theorem normalizer_preimage (U : Submodule F.Carrier c.Space) :
    ((c.modelStabilizer U).comap c.quotientMap).map L.subtype =
      L ⊓ normalizer (c.preimage U : Set G) := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ⟨l.property, (c.mem_normalizer_preimage_iff U l).mpr hl⟩
  · rintro ⟨hl, hx⟩
    exact ⟨⟨x, hl⟩, (c.mem_normalizer_preimage_iff U ⟨x, hl⟩).mp hx, rfl⟩

/-- The literal projection from the original local normalizer to its model stabilizer. -/
@[expose] def normalizerProjection (U : Submodule F.Carrier c.Space) :
    (L ⊓ normalizer (c.preimage U : Set G) : Subgroup G) →* c.modelStabilizer U :=
  (c.quotientMap.comp (inclusion inf_le_left)).codRestrict _ (by
    intro l
    exact (c.mem_normalizer_preimage_iff U ⟨l, l.property.1⟩).mp l.property.2)

/-- Every marked stabilizer element lifts to the original local normalizer. -/
theorem normalizerProjection_surjective (U : Submodule F.Carrier c.Space) :
    Function.Surjective (c.normalizerProjection U) := by
  intro g
  obtain ⟨l, hl⟩ := c.quotientMap_surjective g.val
  have hn : (l : G) ∈ normalizer (c.preimage U : Set G) :=
    (c.mem_normalizer_preimage_iff U l).mpr (hl ▸ g.property)
  exact ⟨⟨l, l.property, hn⟩, Subtype.ext hl⟩

/-- The projection on the actual embedded normalizer residual. -/
@[expose] def residualProjection (U : Submodule F.Carrier c.Space) :
    localResidual L (c.preimage U) →* solvableResidual (c.modelStabilizer U) :=
  (c.normalizerProjection U).solvableResidualMap.comp
    ((solvableResidual (L ⊓ normalizer (c.preimage U : Set G) : Subgroup G)).equivMapOfInjective
      (L ⊓ normalizer (c.preimage U : Set G)).subtype
      (L ⊓ normalizer (c.preimage U : Set G)).subtype_injective).symm.toMonoidHom

/-- The actual local residual maps onto the marked stabilizer residual. -/
theorem residualProjection_surjective (U : Submodule F.Carrier c.Space) :
    Function.Surjective (c.residualProjection U) :=
  ((c.normalizerProjection U).solvableResidualMap_surjective
    (c.normalizerProjection_surjective U)).comp
    ((solvableResidual (L ⊓ normalizer (c.preimage U : Set G) : Subgroup G)).equivMapOfInjective
      (L ⊓ normalizer (c.preimage U : Set G)).subtype
      (L ⊓ normalizer (c.preimage U : Set G)).subtype_injective).symm.surjective

/-- The residual projection is still the original component quotient on ambient elements. -/
theorem residualProjection_coe (U : Submodule F.Carrier c.Space)
    (x : localResidual L (c.preimage U)) :
    ((c.residualProjection U x).val : c.ModelGroup) =
      c.quotientMap ⟨x, (localResidual_le _ x.property).1⟩ := by
  let e := (solvableResidual (L ⊓ normalizer (c.preimage U : Set G) : Subgroup G)).equivMapOfInjective
    (L ⊓ normalizer (c.preimage U : Set G)).subtype
    (L ⊓ normalizer (c.preimage U : Set G)).subtype_injective
  have he : ((e.symm x).val : G) = (x : G) :=
    congrArg (fun z : localResidual L (c.preimage U) => (z : G)) (e.apply_symm_apply x)
  change c.quotientMap ⟨(e.symm x).val, (e.symm x).val.property.1⟩ = _
  exact congrArg c.quotientMap (Subtype.ext he)

/-- The normalizer projection kernel embeds in the original O₂(L). -/
theorem normalizerProjection_ker_isTwoGroup (U : Submodule F.Carrier c.Space) :
    IsPGroup 2 (c.normalizerProjection U).ker := by
  let f : (c.normalizerProjection U).ker →* pCore 2 L :=
    ((inclusion (show L ⊓ normalizer (c.preimage U : Set G) ≤ L from inf_le_left)).comp
      (c.normalizerProjection U).ker.subtype).codRestrict _ (by
        intro x
        apply (QuotientGroup.eq_one_iff _).mp
        apply c.groupEquiv.injective
        rw [map_one]
        exact congrArg Subtype.val x.property)
  exact (pCore_isPGroup (p := 2) (G := L)).of_injective f (by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 L => (z.val : G)) h)))

/-- The same two-group kernel control holds on the actual local residual. -/
theorem residualProjection_ker_isTwoGroup (U : Submodule F.Carrier c.Space) :
    IsPGroup 2 (c.residualProjection U).ker :=
  ((c.normalizerProjection U).solvableResidualMap_ker_isPGroup
    (c.normalizerProjection_ker_isTwoGroup U)).comap_of_injective
    ((solvableResidual (L ⊓ normalizer (c.preimage U : Set G) : Subgroup G)).equivMapOfInjective
      (L ⊓ normalizer (c.preimage U : Set G)).subtype
      (L ⊓ normalizer (c.preimage U : Set G)).subtype_injective).symm.toMonoidHom
    ((solvableResidual (L ⊓ normalizer (c.preimage U : Set G) : Subgroup G)).equivMapOfInjective
      (L ⊓ normalizer (c.preimage U : Set G)).subtype
      (L ⊓ normalizer (c.preimage U : Set G)).subtype_injective).symm.injective

/-- The original local residual and marked residual have isomorphic two-core quotients. -/
@[expose] def residualCoreQuotientEquiv (U : Submodule F.Carrier c.Space) :
    (localResidual L (c.preimage U) ⧸ pCore 2 (localResidual L (c.preimage U))) ≃*
      (solvableResidual (c.modelStabilizer U) ⧸
        pCore 2 (solvableResidual (c.modelStabilizer U))) :=
  (c.residualProjection U).pCoreQuotientEquiv
    (c.residualProjection_surjective U) (c.residualProjection_ker_isTwoGroup U)

/-- The residual quotient isomorphism retains the literal projection on representatives. -/
theorem residualCoreQuotientEquiv_mk (U : Submodule F.Carrier c.Space)
    (x : localResidual L (c.preimage U)) :
    c.residualCoreQuotientEquiv U (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (c.residualProjection U x) := rfl

/-- The original Sylow action in the supplied coordinates, including outer actions. -/
@[expose] def sylowAction (S : D.NonbinaryNaturalInput) : Representation (ZMod 2) T c.Space :=
  c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes

/-- The literal T-invariance condition is exactly invariance under its descended action. -/
theorem sylow_normalizes_preimage_iff (S : D.NonbinaryNaturalInput)
    (U : Submodule F.Carrier c.Space) :
    (T : Subgroup G) ≤ normalizer (c.preimage U : Set G) ↔
      ∀ t : T, ∀ x ∈ U, c.sylowAction S t x ∈ U :=
  c.normalizes_preimage_iff D.sylow_normalizes_component S.sylow_normalizes U

end Coordinates

namespace InvariantFlag
variable {c : Coordinates D F} (f : InvariantFlag c)

/-- A model residual calculation supplies the literal source Lᵢ/O₂(Lᵢ).
The model calculation is an explicit premise, not an asserted source theorem. -/
theorem Li_isPSL2 (i : Fin 2)
    (hmodel : Nonempty ((solvableResidual (c.modelStabilizer (f.space i.castSucc)) ⧸
      pCore 2 (solvableResidual (c.modelStabilizer (f.space i.castSucc)))) ≃*
        PSL(2, F.Carrier))) :
    Nonempty ((f.Li i ⧸ pCore 2 (f.Li i)) ≃* PSL(2, F.Carrier)) :=
  ⟨(c.residualCoreQuotientEquiv (f.space i.castSucc)).trans hmodel.some⟩

/-- A three-dimensional model makes the third flag preimage the original whole seed. -/
theorem top_of_finrank_eq_three [FiniteDimensional F.Carrier c.Space]
    (h : Module.finrank F.Carrier c.Space = 3) : f.Vi 2 = V := by
  have hs : f.space 2 = ⊤ := Submodule.eq_top_of_finrank_eq (by
    rw [f.dimension, h]
    rfl)
  change c.preimage (f.space 2) = V
  rw [hs, c.preimage_top]

theorem sl3_top
    (m : ActionEquiv D.centralQuotientAction (linearNatural F 3))
    (f : InvariantFlag (.sl3 m)) : f.Vi 2 = V := by
  let : FiniteDimensional F.Carrier (Coordinates.sl3 m).Space :=
    inferInstanceAs (FiniteDimensional F.Carrier (Fin 3 → F.Carrier))
  apply f.top_of_finrank_eq_three
  change Module.finrank F.Carrier (Fin 3 → F.Carrier) = 3
  simp

end InvariantFlag
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
