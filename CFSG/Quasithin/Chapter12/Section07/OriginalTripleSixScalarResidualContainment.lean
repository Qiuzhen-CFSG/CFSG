module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarCommutator

/-!
# Normalization and the moved subgroup of the literal scalar residual

The residual is O² of the inverse image of the cubic center. O² means
the two-residual, not the odd core. Both characteristic transports are
retained, so every normalizer of K normalizes the literal residual.
The previously proved whole-core commutator identity then puts the
unchanged chosen module U in X and proves U=[U,X] by idempotence.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

omit [Finite G] in
/-- The normalizer transport follows both actual characteristic inclusions. -/
theorem tripleSixScalarResidual_normalizer_at (K : Subgroup G) :
    normalizer (K : Set G) ≤ normalizer (tripleSixScalarResidual K : Set G) := by
  let Z := centralPreimage (pCore 2 K)
  exact (normalizer_le_normalizer_characteristic_image K Z).trans
    (normalizer_le_normalizer_characteristic_map K.subtype K.subtype_injective
      Z (pResidual 2 Z))

/-- In the original outer branch U is contained in, and fully moved by,
the actual two-residual X. No odd-order hypothesis on X is asserted. -/
theorem original_tripleSix_scalar_residual_contains_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    U ≤ tripleSixScalarResidual K ∧ U = ⁅U,tripleSixScalarResidual K⁆ := by
  let X := tripleSixScalarResidual K
  let M := K ⊔ (T : Subgroup G)
  let Q := M.pCoreIn 2
  have hMK : M ≤ normalizer (K : Set G) :=
    sup_le K.le_normalizer D.sylow_normalizes_component
  have hMX : M ≤ normalizer (X : Set G) := hMK.trans
    (tripleSixScalarResidual_normalizer_at K)
  have hQM : Q ≤ M := pCoreIn_le 2 M
  have he : ⁅Q,X⁆ = U := original_tripleSix_central_closure_scalar_commutator_eq
    h structural D a z hz hzT hnot houter
  have hXp : IsPPerfect 2 X := by
    let Z := centralPreimage (pCore 2 K)
    let R := (pResidual 2 Z).map Z.subtype
    exact (isPPerfect_embedded_pResidual_of_finite 2 Z).of_surjective
      (R.equivMapOfInjective K.subtype K.subtype_injective).toMonoidHom
      (R.equivMapOfInjective K.subtype K.subtype_injective).surjective
  have hXM : X ≤ M := (map_subtype_le _).trans le_sup_left
  have hXQ : X ≤ normalizer (Q : Set G) := hXM.trans (M.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  refine ⟨he.symm.le.trans (le_normalizer_iff_commutator_le_right.mp (hQM.trans hMX)),?_⟩
  have hi := commutator_isPPerfect_idempotent X Q hXp (isPGroup_pCoreIn 2 M) hXQ
  rw [he] at hi
  exact hi.symm

end CFSG.Quasithin.Chapter12.Section07
