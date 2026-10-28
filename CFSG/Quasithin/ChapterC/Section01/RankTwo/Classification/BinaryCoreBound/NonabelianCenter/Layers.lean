module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Head
public import Stellmacher.OmegaOneCenterMap

/-!
# The intrinsic omega-center of a binary MS commutator core

Here the group is D = [O₂(J), L], and the omega subgroup is taken inside
Z(D). Its comparison with a subgroup of J is the composition of the actual
subtype maps through Z(D) and D. This gives an elementary normal subgroup
of J contained in R; no containment in Z(O₂(J)) is asserted.

These are the shared layer definitions for the nonabelian cases of
Aschbacher–Smith C.1.34, combined manuscript (1 March 2004), pp.136–137.
The MS rigidity controlling the size of this layer and the exponent of the
whole center is not proved here.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS
open Subgroup Stellmacher
open scoped IsMulCommutative
universe u
variable {J : Type u} [Group J]

/-- The omega subgroup of the intrinsic center of the actual commutator core. -/
abbrev coreCenterOmega (L : Subgroup J) : Subgroup (center (commutatorCore L)) :=
  omega₁ (center (commutatorCore L)) (p := 2)

theorem coreCenterOmega_elementary (L : Subgroup J) :
    IsElementaryAbelian 2 (coreCenterOmega L) :=
  IsElementaryAbelian.omega₁_of_isMulCommutative _

/-- Comparison with the ambient omega-center by the two subtype inclusions. -/
noncomputable def coreCenterOmegaEquivAmbient (L : Subgroup J) :
    coreCenterOmega L ≃* omegaOneCenterAmbient (commutatorCore L) :=
  ((coreCenterOmega L).equivMapOfInjective (center (commutatorCore L)).subtype
    (center (commutatorCore L)).subtype_injective).trans
    (((coreCenterOmega L).map (center (commutatorCore L)).subtype).equivMapOfInjective
      (commutatorCore L).subtype (commutatorCore L).subtype_injective)

theorem coreCenterOmegaEquivAmbient_apply (L : Subgroup J) (z : coreCenterOmega L) :
    (coreCenterOmegaEquivAmbient L z : J) = (((z : center (commutatorCore L)) :
      commutatorCore L) : J) := by rfl

/-- Exponent control of the whole center, if supplied, identifies it with its omega. -/
theorem coreCenterOmega_eq_top_of_squares (L : Subgroup J)
    (hsquare : ∀ z : center (commutatorCore L), z ^ 2 = 1) :
    coreCenterOmega L = ⊤ := by
  apply eq_top_iff.mpr
  intro z _
  apply Subgroup.subset_closure
  simpa using hsquare z

variable [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J} (h : Input κ L R)
include h

theorem Input.commutatorCore_normal : (commutatorCore L).Normal := by
  let := h.component_normal
  exact Subgroup.commutator_normal _ _

theorem Input.commutatorCore_twoGroup : IsPGroup 2 (commutatorCore L) := by
  let := h.component_normal
  have hDN : commutatorCore L ≤ pCore 2 J := commutator_le_left _ _
  exact pCore_isPGroup.of_injective (Subgroup.inclusion hDN)
    (Subgroup.inclusion_injective hDN)

theorem Input.coreCenterOmega_ambient_normal :
    (omegaOneCenterAmbient (commutatorCore L)).Normal := by
  let := h.commutatorCore_normal
  let : (coreCenterOmega L).Characteristic := omega₁_characteristic _
  change (((coreCenterOmega L).map (center (commutatorCore L)).subtype).map
    (commutatorCore L).subtype).Normal
  infer_instance

theorem Input.coreCenterOmega_ambient_le_radical :
    omegaOneCenterAmbient (commutatorCore L) ≤ R := by
  intro z hz
  have hzD := ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  exact h.radical.twoCore_le
    ((h.componentCore_eq_inf.le (h.commutatorCore_le hzD)).1)

end CFSG.Quasithin.ChapterC.BinaryMS
