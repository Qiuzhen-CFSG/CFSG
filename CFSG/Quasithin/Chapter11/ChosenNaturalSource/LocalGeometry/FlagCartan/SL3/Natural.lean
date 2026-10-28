module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Central

/-!
# Natural coordinates after vanishing of the original central kernel

The proved dual-cohomology calculation makes C_V(L) trivial in the nonbinary
SL₃ branch. The original coordinate projection is therefore an equivalence
on V itself and on each field-subspace preimage. Its conjugation formula is
still the supplied marking, with the original quotient and ambient lifts.
These equivalences supply coordinates for the local action calculations;
no splitting or replacement of V is assumed.

Source: Aschbacher--Smith, 11.0.3(3) and its use in 11.2.4,
printed pp.760,769--770.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The central kernel is killed by the proved SL₃ cohomology calculation. -/
theorem projection_injective : Function.Injective (Coordinates.sl3 m).projection := by
  apply (Coordinates.sl3 m).projection.ker_eq_bot_iff.mp
  apply bot_unique
  intro v hv
  apply Subtype.ext
  exact mem_bot.mp ((Preliminary.sl3_centralizer_eq_bot D S m) ▸
    (show (v : G) ∈ V ⊓ centralizer (L : Set G) from
      ⟨v.property, ((Coordinates.sl3 m).projection_eq_one_iff v).mp hv⟩))

/-- The original V itself is the natural three-space, via its original quotient map.
This equivalence is only formed after proving C_V(L)=1. -/
def naturalEquiv : V ≃* Multiplicative (Fin 3 → S.field.Carrier) :=
  MulEquiv.ofBijective (Coordinates.sl3 m).projection
    ⟨projection_injective D S m, (Coordinates.sl3 m).projection_surjective⟩

/-- The equivalence retains the exact quotient projection on every vector. -/
theorem naturalEquiv_apply (v : V) :
    naturalEquiv D S m v = (Coordinates.sl3 m).projection v := rfl

/-- The original conjugation by L is the marked natural SL₃ action on V. -/
theorem naturalEquiv_conjugation (l : L) (v : V) :
    (naturalEquiv D S m (V.normalizerMonoidHom (inclusion D.normalizes l) v)).toAdd =
      specialLinearNatural 3 ((Coordinates.sl3 m).quotientMap l)
        (naturalEquiv D S m v).toAdd :=
  (Coordinates.sl3 m).projection_component_conjugation l v

/-- Restrict the same coordinates to any actual field-subspace preimage. -/
def subspaceEquiv (U : Submodule S.field.Carrier (Fin 3 → S.field.Carrier)) :
    (Coordinates.sl3 m).preimage U ≃* Multiplicative U := by
  let f : (Coordinates.sl3 m).preimage U →* Multiplicative U :=
    { toFun := fun v => Multiplicative.ofAdd
        ⟨((Coordinates.sl3 m).projection ⟨v,D.centralQuotientPreimage_le _ v.property⟩).toAdd,
          ((Coordinates.sl3 m).mem_preimage U _).mp v.property⟩
      map_one' := by apply Subtype.ext; exact congrArg Multiplicative.toAdd (map_one _)
      map_mul' := by
        intro v w
        apply Subtype.ext
        exact congrArg Multiplicative.toAdd (map_mul (Coordinates.sl3 m).projection
          (⟨v,D.centralQuotientPreimage_le _ v.property⟩ : V)
          (⟨w,D.centralQuotientPreimage_le _ w.property⟩ : V)) }
  apply MulEquiv.ofBijective f
  constructor
  · intro v w he
    apply Subtype.ext
    have hp := congrArg (fun x : Multiplicative U => x.toAdd.val) he
    have hh := projection_injective D S m (congrArg Multiplicative.ofAdd hp)
    exact congrArg (fun z : V => (z : G)) hh
  · intro u
    obtain ⟨v,hv⟩ := (Coordinates.sl3 m).projection_surjective (Multiplicative.ofAdd u.toAdd.val)
    have hvU : (v : G) ∈ (Coordinates.sl3 m).preimage U := by
      apply ((Coordinates.sl3 m).mem_preimage U v).mpr
      change ((Coordinates.sl3 m).projection v).toAdd ∈ U
      rw [hv]
      exact u.toAdd.property
    refine ⟨⟨v,hvU⟩,?_⟩
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd hv

/-- The restricted natural coordinates still use the literal projection. -/
theorem subspaceEquiv_apply (U : Submodule S.field.Carrier (Fin 3 → S.field.Carrier))
    (v : (Coordinates.sl3 m).preimage U) :
    (subspaceEquiv D S m U v).toAdd.val =
      ((Coordinates.sl3 m).projection ⟨v,D.centralQuotientPreimage_le _ v.property⟩).toAdd := rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
