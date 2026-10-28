module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Marked

/-!
# Original vector and actor projections on the marked G₂ plane

The actor map is the literal residual projection followed by the short-local
SL₂ map; its kernel is exactly O₂(L₂). The vector map is the original central
quotient projection restricted to the entire plane preimage, and its kernel
is exactly the relative C_V(L). Ambient conjugation intertwines this same
vector map with the field-linear quotient-plane action.

The final coordinate identification of this action with the natural SL₂
two-space is separate. In particular the full plane preimage is not asserted
to be Irr⁺, and its possible central part is preserved.

Source: Aschbacher--Smith 11.0.2 and opening §11.1, printed pp.759--761.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
open Atlas.G2.LieParabolicSetup
open scoped MatrixGroups
/-- Restrict a multiplicative vector projection to a submodule containing its image. -/
def restrictVectorProjection {A W k : Type*} [Group A] [AddCommGroup W]
    [Semiring k] [Module k W] (p : A →* Multiplicative W) (U : Submodule k W)
    (h : ∀ a, (p a).toAdd ∈ U) : A →* Multiplicative U where
  toFun a := Multiplicative.ofAdd ⟨(p a).toAdd,h a⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd p.map_one
  map_mul' a b := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (p.map_mul a b)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- The aligned residual projection preserves the original two-group kernel. -/
theorem localProjection_ker_isTwoGroup (i : Fin 2) :
    IsPGroup 2 (localProjection S m i).ker := by
  have he : (localProjection S m i).ker =
      ((coordinates S m).residualProjection ((flag S m).space i.castSucc)).ker := by
    ext x
    change modelResidualEquiv S m i (((coordinates S m).residualProjection ((flag S m).space i.castSucc)) x) = 1 ↔ _
    rw [map_eq_one_iff _ (modelResidualEquiv S m i).injective]
    rfl
  rw [he]
  exact (coordinates S m).residualProjection_ker_isTwoGroup _

/-- The actual rank-one plane map, read from the marked octonion coordinates. -/
def planeProjection : (flag S m).Li 1 →* SL(2,S.field.Carrier) :=
  (shortSLHom (F := S.field.Carrier)).comp (localProjection S m 1)

theorem planeProjection_surjective : Function.Surjective (planeProjection S m) :=
  shortSLHom_surjective.comp (localProjection_surjective S m 1)

/-- Its kernel is the intrinsic two-core of the original plane residual. -/
theorem planeProjection_ker : (planeProjection S m).ker = pCore 2 ((flag S m).Li 1) := by
  change ((shortSLHom (F := S.field.Carrier)).comp (localProjection S m 1)).ker = _
  rw [← MonoidHom.comap_ker, shortSLHom_ker, ← local₁_intrinsic_pCore]
  exact (localProjection S m 1).comap_pCore_of_ker_isPGroup
    (localProjection_surjective S m 1) (localProjection_ker_isTwoGroup S m 1)


/-- The original coordinate projection restricted to the full plane preimage.
Its central kernel is retained, so this is not an isomorphism of the full plane. -/
def planeVectorProjection : (flag S m).Vi 1 →*
    Multiplicative ((flag S m).space 1) :=
  restrictVectorProjection ((coordinates S m).projection.comp
    (inclusion (D.centralQuotientPreimage_le _))) ((flag S m).space 1)
      (fun v => ((coordinates S m).mem_preimage _ _).mp v.property)

theorem planeVectorProjection_surjective : Function.Surjective (planeVectorProjection S m) := by
  intro x
  obtain ⟨v,hv⟩ := (coordinates S m).projection_surjective (Multiplicative.ofAdd x.toAdd.val)
  have hvp : v.val ∈ (flag S m).Vi 1 :=
    ((coordinates S m).mem_preimage _ _).mpr (by
      change ((coordinates S m).projection v).toAdd ∈ (flag S m).space 1
      rw [hv]
      exact x.toAdd.property)
  refine ⟨⟨v.val,hvp⟩, ?_⟩
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  exact congrArg Multiplicative.toAdd hv

/-- Exactly C_V(L) restricted to the original plane, including a nontrivial center. -/
theorem planeVectorProjection_ker : (planeVectorProjection S m).ker =
    (centralizer (L : Set G)).subgroupOf ((flag S m).Vi 1) := by
  ext v
  change planeVectorProjection S m v = 1 ↔ v.val ∈ centralizer (L : Set G)
  rw [← (coordinates S m).projection_eq_one_iff
    ⟨v.val,D.centralQuotientPreimage_le _ v.property⟩]
  change Multiplicative.ofAdd _ = Multiplicative.ofAdd _ ↔ _ = _
  constructor
  · intro h
    exact congrArg (fun z => Multiplicative.ofAdd z.toAdd.val) h
  · intro h
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd h

/-- The plane quotient by that exact central kernel is the marked field plane. -/
def planeCentralQuotientEquiv :
    (((flag S m).Vi 1) ⧸ (planeVectorProjection S m).ker) ≃*
      Multiplicative ((flag S m).space 1) :=
  QuotientGroup.quotientKerEquivOfSurjective _ (planeVectorProjection_surjective S m)


/-- Actual ambient conjugation on the full plane preimage. -/
def planeConjugation : (flag S m).Li 1 →* MulAut ((flag S m).Vi 1) :=
  ((flag S m).Vi 1).normalizerMonoidHom.comp
    (inclusion ((localResidual_le _).trans inf_le_right))

/-- The field-linear action on the marked quotient plane, using the unchanged
component marking. The SL₂ coordinate identification is a separate calculation. -/
def planeAction : Representation S.field.Carrier ((flag S m).Li 1) ((flag S m).space 1) :=
  Subrepresentation.toRepresentation (ρ := (coordinates S m).modelAction.comp
    ((coordinates S m).quotientMap.comp (inclusion ((localResidual_le _).trans inf_le_left))))
      { toSubmodule := (flag S m).space 1
        apply_mem_toSubmodule := by
          intro l x hx
          exact (((coordinates S m).mem_normalizer_preimage_iff ((flag S m).space 1)
            ⟨l.val,(localResidual_le _ l.property).1⟩).mp
              (localResidual_le _ l.property).2 x).mpr hx }

/-- The same original vector projection intertwines ambient conjugation and
its field-linear quotient action; no abstract replacement projection is used. -/
theorem planeVectorProjection_intertwines (l : (flag S m).Li 1) (v : (flag S m).Vi 1) :
    planeVectorProjection S m (planeConjugation S m l v) =
      Multiplicative.ofAdd (planeAction S m l (planeVectorProjection S m v).toAdd) := by
  apply congrArg Multiplicative.ofAdd
  apply Subtype.ext
  exact (coordinates S m).projection_component_conjugation
    ⟨l.val,(localResidual_le _ l.property).1⟩
    ⟨v.val,D.centralQuotientPreimage_le _ v.property⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2.ResidualIncidence
