module

public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.CoveringKernelBound
public import Theory.GroupTheory.CoveringKernelEquiv
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic

/-!
# The constructed universal cover of PSL₃(4)

We use the derived subgroup of the free central extension of the actual
matrix group PSL₃(4). The general free-group construction proves finiteness,
quasisimplicity and universality; none of these depends on a multiplier table.
Field isomorphisms transport its projection to any field of order four,
without changing the covering group or its kernel.

The exceptional kernel calculation required by Aschbacher–Smith I.1.3(6),
printed p.407 (PDF p.418), is a separate obligation. In particular this
module does not identify the kernel with C₄ × C₄ × C₃. The projective
simplicity and field transport results come from the attributed ATLAS port
in `Theory.AtlasPort.ExceptionalIsomorphisms`.
-/

@[expose] public section

open Theory.GroupTheory
open scoped MatrixGroups

namespace Matrix.PSL3.ExceptionalFourCover

universe u w
noncomputable section

/-- The actual projective matrix group in degree three is quasisimple. -/
instance base_isQuasisimple (K : Type u) [Field K] :
    IsQuasisimple (ProjectiveSpecialLinearGroup (Fin 3) K) := by
  let : Group.IsPerfect PSL(3, K) := Atlas.psl_perfect (F := K) 3 (by decide)
  let : IsSimpleGroup PSL(3, K) := Atlas.psl_simple_high_rank (F := K) 3 (by decide)
  have hc : Subgroup.center PSL(3, K) = ⊥ := by
    change Subgroup.center (SL(3, K) ⧸ Subgroup.center SL(3, K)) = ⊥
    let : Group.IsPerfect SL(3, K) := Atlas.sl_perfect (F := K) 3 (by decide)
    exact Group.IsPerfect.center_quotient_center_eq_bot _
  refine { toIsPerfect := inferInstance, simple := ?_ }
  exact ((QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientBot :
      PSL(3, K) ⧸ (⊥ : Subgroup PSL(3, K)) ≃* PSL(3, K))).isSimpleGroup

/-- The concrete finite covering group, built from the free central extension. -/
abbrev CoverGroup := PerfectCentralCovering.UniversalGroup PSL3Four.PSL

/-- The projection to the actual matrix group over `GaloisField 2 2`. -/
def cover : Covering CoverGroup PSL3Four.PSL :=
  PerfectCentralCovering.universalQuasisimpleCover PSL3Four.PSL

theorem cover_toMonoidHom :
    cover.toMonoidHom = PerfectCentralCovering.universalProjection PSL3Four.PSL := rfl

theorem cover_surjective : Function.Surjective cover := cover.surjective

/-- Universality holds for covering groups in every target universe. -/
theorem cover_isUniversal : Covering.IsUniversal.{0, 0, w} cover :=
  PerfectCentralCovering.universalQuasisimpleCover_isUniversal PSL3Four.PSL

theorem cover_ker_eq_center : cover.toMonoidHom.ker = Subgroup.center CoverGroup := by
  let : IsSimpleGroup PSL3Four.PSL :=
    Atlas.psl_simple_high_rank (F := PSL3Four.F) 3 (by decide)
  exact cover.ker_eq_center_of_isSimple

/-- Coordinates for the intended exceptional multiplier, not yet a kernel identification. -/
abbrev Multiplier :=
  (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) × Multiplicative (ZMod 3)

theorem card_multiplier : Nat.card Multiplier = 48 := by
  change Nat.card ((ZMod 4 × ZMod 4) × ZMod 3) = 48
  norm_num [Nat.card_prod, Nat.card_zmod]

variable (K : Type u) [Field K] [Finite K]

/-- A proved field identification with the fixed four-element field. -/
noncomputable def fieldEquiv (hK : Nat.card K = 4) : PSL3Four.F ≃+* K := by
  let := Fintype.ofFinite PSL3Four.F
  let := Fintype.ofFinite K
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, PSL3Four.card_F, hK])

/-- Entrywise field transport, descended through the actual scalar center. -/
noncomputable def baseEquiv (hK : Nat.card K = 4) :
    PSL3Four.PSL ≃* ProjectiveSpecialLinearGroup (Fin 3) K :=
  Atlas.fieldEquivPSL 3 (fieldEquiv K hK)

/-- The same finite quasisimple group covering PSL₃ over an arbitrary field of order four. -/
noncomputable def coverOver (hK : Nat.card K = 4) :
    Covering CoverGroup (ProjectiveSpecialLinearGroup (Fin 3) K) :=
  (Covering.ofMulEquiv (baseEquiv K hK)).comp cover

theorem coverOver_surjective (hK : Nat.card K = 4) :
    Function.Surjective (coverOver K hK) := (coverOver K hK).surjective

theorem coverOver_isUniversal (hK : Nat.card K = 4) :
    Covering.IsUniversal.{u, 0, w} (coverOver K hK) :=
  Covering.IsUniversal.comp_ofMulEquiv cover_isUniversal (baseEquiv K hK)

/-- Changing the coefficient field leaves the literal kernel subgroup unchanged. -/
theorem coverOver_ker (hK : Nat.card K = 4) :
    (coverOver K hK).toMonoidHom.ker = cover.toMonoidHom.ker :=
  MonoidHom.ker_comp_of_injective cover.toMonoidHom
    (baseEquiv K hK).toMonoidHom (baseEquiv K hK).injective

end
end Matrix.PSL3.ExceptionalFourCover
