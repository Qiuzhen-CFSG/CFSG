module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Cases
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ProductCentralizer
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.MovingSection

/-!
# Exceptional-core exhaustion and its faithful initial action

Write M = LR, K = L inside M, Q = O₂(M), and X = Ω₁Z(Q).
The source exhaustion equality [Q,K] = [X,K] places the entire intrinsic
core in the central elementary layer. The two-layer centralizer theorem
then proves C_M(X) = Q; the odd covering center is not discarded by
mistaking C_R(X) for C_M(X). All quotient actions use the original map.

Exhaustion is the outstanding MS93 critical-distance argument, not a
consequence of the initial FF action. The later recognition module consumes
this exact equality. Source: Aschbacher--Smith C.1.31--32, pp.135--136;
Meierfrankenfeld--Stellmacher (1993), (3.6), (3.8), and Section 7, pp.932--933.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC ChapterB.QuasisimpleSource
namespace AlternatingSixReconstruction.Exceptional
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

abbrev centralOmega (L R : Subgroup G) : Subgroup (L ⊔ R : Subgroup G) :=
  omegaCenterIn (pCore 2 (L ⊔ R : Subgroup G))

instance centralOmega_normal (L R : Subgroup G) : (centralOmega L R).Normal := by
  let : (omega₁ (center (pCore 2 (L ⊔ R : Subgroup G))) (p := 2)).Characteristic :=
    omega₁_characteristic _
  infer_instance

abbrev CentralMarking (L : Subgroup G) :=
  (L ⧸ centralPreimage (pCore 2 L)) ≃*
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))

/-- The precise whole-core equality required from the source graph argument. -/
def CoreExhaustion (L R : Subgroup G) : Prop :=
  ⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆ =
    ⁅centralOmega L R, L.subgroupOf (L ⊔ R)⁆

/-- The sole remaining source obligation in the exceptional branch. It retains
MS2(a), relative normality, and the original triple-cover marking. -/
def CoreExhaustionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G), SmallMSPair κ L R →
    CentralMarking L → Nat.card (center (L ⧸ pCore 2 L)) = 3 → CoreExhaustion L R

variable (h : SmallMSPair κ L R)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "Q" => pCore 2 M
local notation "X" => centralOmega L R

include h

/-- The two-constrained condition holds on the actual relative carrier. -/
theorem relative_fitting : generalizedFitting K = pCore 2 K := by
  apply le_antisymm _ ((pCore_le_fitting K 2).trans (fitting_le_generalizedFitting K))
  rw [pCore_subnormal_eq_comap 2 h.component.subnormal]
  apply map_le_iff_le_comap.mp
  rw [← h.fitting]
  exact generalizedFitting_map_subtype_le_of_isSubnormal K h.component.subnormal

/-- No shortness or elementary-core premise is needed for the upper bound. -/
theorem core_centralizer_le : centralizer (blockU L : Set L) ≤ pCore 2 L :=
  centralizer_blockU_le_of_fitting h.component_fitting

/-- The embedded relative core is the initial moved subgroup after exhaustion. -/
theorem relative_core_eq (hx : CoreExhaustion L R) :
    (blockU K).map (K).subtype = ⁅X, K⁆ :=
  h.ambient_commutator_eq_relative_core.symm.trans hx

/-- Exhaustion puts the whole relative core in the central elementary layer. -/
theorem relative_core_le_centralOmega (hx : CoreExhaustion L R) :
    blockU K ≤ omegaCenterIn (pCore 2 K) := by
  intro x hxU
  have hxX : (x : M) ∈ X := (commutator_le_left X K)
    (relative_core_eq h hx ▸ mem_map_of_mem (K).subtype hxU)
  obtain ⟨_, hc, hs⟩ := (mem_omegaCenterIn_iff Q (x : M)).mp hxX
  apply (mem_omegaCenterIn_iff _ _).mpr
  refine ⟨blockU_le_core hxU, ?_, Subtype.ext hs⟩
  intro y hy
  apply Subtype.ext
  exact hc y (pCoreIn_le_of_subnormal 2 h.component.subnormal
    (mem_map_of_mem (K).subtype hy))

/-- The full kernel equality follows from exhaustion and the two-layer
centralizer bound, rather than from the intersection with the radical. -/
theorem centralOmega_centralizer (hx : CoreExhaustion L R) :
    centralizer (X : Set M) = Q := by
  let := h.relative_normal
  have hquot : IsPGroup 2 (M ⧸ K) :=
    (isPGroup_quotient_pResidual (G := M) 2).of_equiv
      (QuotientGroup.quotientMulEquivOfEq h.relative_residual)
  apply le_antisymm
  · apply le_trans (centralizer_le (commutator_le_left X K))
    rw [← relative_core_eq h hx]
    exact centralizer_blockU_le_core_of_normal K (relative_fitting h) hquot
  · intro q hq x hxX
    exact (((mem_omegaCenterIn_iff Q x).mp hxX).2.1 q hq).symm

/-- The initial action is through the literal two-core quotient. -/
def initialAction (hx : CoreExhaustion L R) :
    Representation (ZMod 2) (M ⧸ Q) (Additive X) :=
  NormalElementaryQuotient.representation X (QuotientGroup.mk' Q)
    (QuotientGroup.mk'_surjective Q)
    ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h hx).symm)

theorem initialAction_faithful (hx : CoreExhaustion L R) :
    Function.Injective (initialAction h hx) :=
  NormalElementaryQuotient.representation_injective _ _ _ _

/-- MS3 supplies FF on this faithful action without requiring R to be Sylow. -/
theorem initialAction_isFFModule (hx : CoreExhaustion L R) :
    IsFFModule (initialAction h hx) := by
  unfold initialAction
  apply NormalElementaryQuotient.isFFModule_of_thompson_not_le
    X (QuotientGroup.mk' Q) (QuotientGroup.mk'_surjective Q)
    ((QuotientGroup.ker_mk' Q).trans (centralOmega_centralizer h hx).symm)
    (R.subgroupOf (L ⊔ R))
  · intro x hxX
    exact h.relative_radical.twoCore_le ((mem_omegaCenterIn_iff Q x).mp hxX).1
  · simpa only [QuotientGroup.ker_mk'] using
      h.relative_characteristic.thompson_not_le_core h.relative_radical.isPGroup
        h.relative_radical_ne_bot h.relative_radical.twoCore_le

omit h in
abbrev componentImage (L R : Subgroup G) : Subgroup
    ((L ⊔ R : Subgroup G) ⧸ pCore 2 (L ⊔ R : Subgroup G)) :=
  (L.subgroupOf (L ⊔ R)).map (QuotientGroup.mk' (pCore 2 (L ⊔ R : Subgroup G)))

end AlternatingSixReconstruction.Exceptional
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
