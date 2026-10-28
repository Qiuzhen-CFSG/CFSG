module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Coefficients
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.FieldDetection.OddLinear.Models

/-!
# Odd-subfield tori in the original two-core quotient

A faithful coefficient torus in J/O₂(J) restricts to the constructed
odd-degree field. The original odd field actor remains nonidentity there,
so it suffices to lift only these subfield parameters into N_G(T).
Schur--Zassenhaus and the common lifting theorem then give BorelMovement.

Both PSL₂ and PSL₃ consumers use actual markings of I/O₂(I), the original
Cartan actor and literal quotient maps. In PSL₃ the chosen torus is
diag(a,1,a⁻¹), fixed by the opposition graph; thus it is the torus needed
when the Sylow action also contains that graph automorphism. The invariant
subfield subgroup and simultaneous normalizer lifts remain to be
constructed by the source geometry producer. These conditional consumers
do not assert those lift hypotheses or the A.3.15 sieve.
Source: Aschbacher--Smith 11.5.6(3), printed p.781.
-/

@[expose] public noncomputable section
open Subgroup
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Restrict the coefficient torus before applying the literal normalizer lift. -/
def oddFieldSection (J : Subgroup G) (hJ : J ≤ E.Y) (F : BinaryField)
    (t : F.Carrierˣ →* (J ⧸ pCore 2 J)) (ht : Function.Injective t)
    (a : normalizer (J : Set G)) (ha : (a : G) ∈ E.X)
    (σ : F.Carrier ≃+* F.Carrier) (ho : Odd (orderOf σ)) (hσ : σ ≠ 1)
    (hact : ∀ u, coreQuotientAction J a (t u) = t (Units.map σ.toMonoidHom u))
    (hlift : ∀ u : (oddField F).Carrierˣ, ∃ j : J,
      (j : G) ∈ normalizer (T : Set G) ∧
      QuotientGroup.mk' (pCore 2 J) j = t (Units.map (oddInclusion F).toMonoidHom u)) :
    FieldTorusSection E where
  J := J
  le_Y := hJ
  field := oddField F
  torus := t.comp (Units.map (oddInclusion F).toMonoidHom)
  injective := ht.comp (by
    intro u v huv
    apply Units.ext
    exact (oddInclusion F).injective (congrArg Units.val huv))
  actor := a
  actor_mem := ha
  coefficient := oddRestriction F σ
  nontrivial := oddRestriction_ne_one F σ ho hσ
  action u := by
    rw [MonoidHom.comp_apply, hact, MonoidHom.comp_apply]
    apply congrArg t
    apply Units.ext
    exact (oddRestriction_apply F σ u.val).symm
  lifts := hlift

/-- The original-geometry consumer needs lifts only for the odd subfield. -/
theorem borel_movement_of_odd_field_torus (J : Subgroup G) (hJ : J ≤ E.Y) (F : BinaryField)
    (t : F.Carrierˣ →* (J ⧸ pCore 2 J)) (ht : Function.Injective t)
    (a : normalizer (J : Set G)) (ha : (a : G) ∈ E.X)
    (σ : F.Carrier ≃+* F.Carrier) (ho : Odd (orderOf σ)) (hσ : σ ≠ 1)
    (hact : ∀ u, coreQuotientAction J a (t u) = t (Units.map σ.toMonoidHom u))
    (hlift : ∀ u : (oddField F).Carrierˣ, ∃ j : J,
      (j : G) ∈ normalizer (T : Set G) ∧
      QuotientGroup.mk' (pCore 2 J) j = t (Units.map (oddInclusion F).toMonoidHom u)) :
    E.BorelMovement :=
  (oddFieldSection E J hJ F t ht a ha σ ho hσ hact hlift).borel_movement

open Matrix.ProjectiveSpecialLinearGroup.OddBorel
open BenderSuzuki.Converse

/-- The actual projective diagonal torus, transported to I/O₂(I). -/
def LinearFieldMarking.twoTorus {I : Subgroup G} (w : LinearFieldMarking E I 2) :
    w.field.Carrierˣ →* (I ⧸ pCore 2 I) :=
  w.model.symm.toMonoidHom.comp (torusHom w.field.Carrier)

/-- Characteristic two removes the projective scalar kernel in this torus. -/
theorem LinearFieldMarking.twoTorus_injective {I : Subgroup G}
    (w : LinearFieldMarking E I 2) : Function.Injective (w.twoTorus E) :=
  w.model.symm.injective.comp
    ((pi_injective (F := w.field.Carrier)).comp (torHom_injective (F := w.field.Carrier)))

/-- The original quotient actor has exactly the recorded coefficient action. -/
theorem LinearFieldMarking.twoTorus_action {I : Subgroup G}
    (w : LinearFieldMarking E I 2) (u : w.field.Carrierˣ) :
    coreQuotientAction I w.actor (w.twoTorus E u) =
      w.twoTorus E (Units.map w.coefficient.toMonoidHom u) := by
  apply w.model.injective
  rw [w.action]
  simpa only [twoTorus, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.apply_symm_apply] using
    Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.FieldInvolution.field_torusHom
      w.field.Carrier w.coefficient u

/-- The PSL₂ consumer; only the simultaneous normalizer lifts remain explicit. -/
theorem LinearFieldMarking.two_borel_movement {I : Subgroup G}
    (w : LinearFieldMarking E I 2) (hI : I ≤ E.Y)
    (hlift : ∀ u : (oddField w.field).Carrierˣ, ∃ i : I,
      (i : G) ∈ normalizer (T : Set G) ∧
      QuotientGroup.mk' (pCore 2 I) i =
        w.twoTorus E (Units.map (oddInclusion w.field).toMonoidHom u)) :
    E.BorelMovement :=
  borel_movement_of_odd_field_torus E I hI w.field (w.twoTorus E)
    (w.twoTorus_injective E) w.actor w.actor_mem w.coefficient w.odd_order w.nontrivial
    (w.twoTorus_action E) hlift

open Matrix.PSL3.CartanActions.RootTorusControl

/-- The graph-fixed root torus transported through the literal PSL₃ marking. -/
def LinearFieldMarking.threeTorus {I : Subgroup G} (w : LinearFieldMarking E I 3) :
    w.field.Carrierˣ →* (I ⧸ pCore 2 I) :=
  w.model.symm.toMonoidHom.comp (rootTorus w.field.Carrier)

/-- The one-parameter root torus is faithful in the projective quotient. -/
theorem LinearFieldMarking.threeTorus_injective {I : Subgroup G}
    (w : LinearFieldMarking E I 3) : Function.Injective (w.threeTorus E) :=
  w.model.symm.injective.comp (rootTorus_injective w.field.Carrier)

/-- The actual quotient action preserves the root-torus coefficient formula. -/
theorem LinearFieldMarking.threeTorus_action {I : Subgroup G}
    (w : LinearFieldMarking E I 3) (u : w.field.Carrierˣ) :
    coreQuotientAction I w.actor (w.threeTorus E u) =
      w.threeTorus E (Units.map w.coefficient.toMonoidHom u) := by
  apply w.model.injective
  rw [w.action]
  simp only [threeTorus, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, MulEquiv.apply_symm_apply]
  have hf : Atlas.fieldEquivPSL 3 w.coefficient =
      Matrix.PSL3.OuterSolvable.fieldAction w.field.Carrier w.coefficient := by
    ext z
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      (center SL(3, w.field.Carrier)) z
    rw [Atlas.fieldEquivPSL_mk]
    simp only [QuotientGroup.mk'_apply]
    rw [Matrix.PSL3.OuterSolvable.fieldAction_mk]
    rfl
  rw [hf]
  exact field_rootTorus w.field.Carrier w.coefficient u

/-- The PSL₃ consumer uses the torus fixed by the opposition graph. -/
theorem LinearFieldMarking.three_borel_movement {I : Subgroup G}
    (w : LinearFieldMarking E I 3) (hI : I ≤ E.Y)
    (hlift : ∀ u : (oddField w.field).Carrierˣ, ∃ i : I,
      (i : G) ∈ normalizer (T : Set G) ∧
      QuotientGroup.mk' (pCore 2 I) i =
        w.threeTorus E (Units.map (oddInclusion w.field).toMonoidHom u)) :
    E.BorelMovement :=
  borel_movement_of_odd_field_torus E I hI w.field (w.threeTorus E)
    (w.threeTorus_injective E) w.actor w.actor_mem w.coefficient w.odd_order w.nontrivial
    (w.threeTorus_action E) hlift

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions.FieldDetection.OddLinear
