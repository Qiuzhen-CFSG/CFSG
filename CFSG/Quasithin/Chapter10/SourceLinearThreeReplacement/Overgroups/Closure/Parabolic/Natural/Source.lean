module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.Inputs
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction.Realization
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.OriginalAction.Kernel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural.PointModel.Geometry
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Source
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.SymmetricFourWreath.ResidualQuotient

/-!
# Recognition through the original paired natural action

Equivariance and injectivity of the canonical module coordinates identify
C_{L₀T}(z) with the full preimage of the literal model point stabilizer.
Maximality pulls back through the surjective action map. Restricting this
map to the stabilizer retains a two-group kernel, so the intrinsic two-core
quotients agree. The S₄-wreath quotient then gives the required S₃ wreath.

The original matrix realization supplies the full action with its two-group
kernel, and the paired point-model calculation supplies maximality and the
whole S₄-wreath stabilizer. The final `diagonalRecognition` discharges both
inputs under the original source hypotheses. Its seed application retains
only the separate intrinsic wreath-residual calculation.
Source: Aschbacher--Smith 10.2.4,10.2.11 and §10.3, pp.747,753--754,756--757.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}
  {hz : D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥}

/-- The marked homomorphism has exactly the original conjugation kernel. -/
theorem ActionData.ker_eq (a : ActionData s hz) :
    a.hom.ker = (centralizer (D.fullModule : Set G)).subgroupOf (localJoin T L) := by
  rw [← joinAction_ker D]
  ext g
  change a.hom g = 1 ↔ joinAction D g = 1
  constructor
  · intro hg
    apply MulEquiv.ext
    intro v
    apply (fullCoordinates s hz).injective
    rw [a.equivariant, hg, map_one]
    rfl
  · intro hg
    apply action_injective
    apply MulEquiv.ext
    intro w
    obtain ⟨v,rfl⟩ := (fullCoordinates s hz).surjective w
    rw [map_one, ← a.equivariant, hg]
    rfl

/-- Equivariance identifies the actual ambient centralizer, including its kernel. -/
theorem ActionData.stabilizer_preimage (a : ActionData s hz) (z : D.fullModule) :
    (diagonalParabolic T L (z : G)).subgroupOf (localJoin T L) =
      (pointStabilizer (fullCoordinates s hz z)).comap a.hom := by
  ext g
  change ((g : G) ∈ localJoin T L ∧ (g : G) ∈ centralizer ({(z : G)} : Set G)) ↔
    action (a.hom g) (fullCoordinates s hz z) = fullCoordinates s hz z
  constructor
  · intro hg
    rw [← a.equivariant]
    apply congrArg (fullCoordinates s hz)
    apply Subtype.ext
    rw [joinAction_apply, mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]
  · intro hg
    refine ⟨g.property, mem_centralizer_singleton_iff.mpr ?_⟩
    have he : joinAction D g z = z :=
      (fullCoordinates s hz).injective ((a.equivariant g z).trans hg)
    have hv := congrArg Subtype.val he
    rw [joinAction_apply] at hv
    exact mul_inv_eq_iff_eq_mul.mp hv

/-- The intrinsic quotient of an S₄-wreath stabilizer is the required S₃ wreath. -/
def pointQuotientEquiv (v : Space)
    (e : pointStabilizer v ≃* RegularWreathProduct (Equiv.Perm (Fin 4)) Bit) :
    (pointStabilizer v ⧸ pCore 2 (pointStabilizer v)) ≃* ParabolicWreath :=
  (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (SymmetricFourWreath.quotientEquivActor.trans
      (RegularWreathProduct.congr (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three)
        (MulEquiv.refl Bit)))

/-- Restriction and both subgroup identifications preserve the actual two-core quotient. -/
def ActionData.parabolicQuotientEquiv (a : ActionData s hz) (z : D.fullModule)
    (e : pointStabilizer (fullCoordinates s hz z) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 4)) Bit) :
    (diagonalParabolic T L (z : G) ⧸ pCore 2 (diagonalParabolic T L (z : G))) ≃*
      ParabolicWreath := by
  let S := pointStabilizer (fullCoordinates s hz z)
  let r := a.hom.subgroupComap S
  have hr : Function.Surjective r :=
    a.hom.subgroupComap_surjective_of_surjective S a.onto
  have hk : r.ker = a.hom.ker.subgroupOf (S.comap a.hom) := by
    ext x
    change (r x : S) = 1 ↔ a.hom x = 1
    exact Subtype.ext_iff
  have hp : IsPGroup 2 r.ker := by
    rw [hk]
    exact a.kernel_two.comap_subtype
  let c : diagonalParabolic T L (z : G) ≃* S.comap a.hom :=
    (subgroupOfEquivOfLe (diagonalParabolic_le_join (T := T) (L := L) (z : G))).symm.trans
      (MulEquiv.subgroupCongr (a.stabilizer_preimage z))
  exact (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans
    ((r.pCoreQuotientEquiv hr hp).trans (pointQuotientEquiv _ e))

/-- The model maximality is relative to the original L₀T, as in10.2.4. -/
theorem ActionData.parabolic_isCoatom (a : ActionData s hz) (z : D.fullModule)
    (hmax : IsCoatom (pointStabilizer (fullCoordinates s hz z))) :
    IsCoatom ((diagonalParabolic T L (z : G)).subgroupOf (localJoin T L)) := by
  rw [a.stabilizer_preimage z]
  exact isCoatom_comap_of_surjective a.onto hmax

/-- Combine the independent action and model calculations on the original diagonal.
Both outstanding premises must be proved before this supplies the source theorem. -/
theorem diagonalRecognition_of_action
    (hsource : NaturalActionAt T) (hmodel : ModelGeometry) : DiagonalRecognitionAt T := by
  intro hmany L D s d
  obtain ⟨a⟩ := hsource hmany L D s d
  let z : D.fullModule := ⟨d.first*d.second,
    D.fullModule.mul_mem (survivor_moved_le s d.first_mem)
      (survivor_partner_le s d.second_mem)⟩
  have hn : ∀ i, fullCoordinates s d.fixed_part z i ≠ 1 :=
    diagonal_coordinates_ne_one s d.fixed_part d.first_mem d.second_mem d.first_ne d.second_ne
  obtain ⟨hmax,⟨e⟩⟩ := hmodel _ hn
  exact ⟨a.parabolic_isCoatom z hmax, ⟨a.parabolicQuotientEquiv z e⟩⟩

/-- The existing seed consumer receives the exact stabilizer and its quotient.
Its separate intrinsic wreath-residual calculation is retained explicitly. -/
theorem parabolicSeed_of_action
    (hsource : NaturalActionAt T) (hmodel : ModelGeometry) (hwreath : WreathResidualAt T) :
    ParabolicSeedAt T :=
  parabolicSeed_of_recognition (diagonalRecognition_of_action hsource hmodel) hwreath

/-- The literal diagonal centralizer is a maximal subgroup of L₀T, and its
intrinsic two-core quotient is S₃ wr C₂. Both action and model calculations
are proved from the original hypotheses; no recognition premise remains. -/
theorem diagonalRecognition (T : Sylow 2 G) : DiagonalRecognitionAt T := by
  apply diagonalRecognition_of_action
  · intro _ L D s d
    exact ⟨(OriginalAction.originalLift s d.fixed_part).actionData⟩
  · intro v hv
    exact ⟨PointModel.pointStabilizer_isCoatom v hv,
      ⟨PointModel.pointStabilizerEquivSymmetricWreath v hv⟩⟩

/-- Discharge natural recognition in the original centralizer-seed consumer.
The independent intrinsic wreath-residual calculation remains with its owner. -/
theorem parabolicSeed (hwreath : WreathResidualAt T) : ParabolicSeedAt T :=
  parabolicSeed_of_recognition (diagonalRecognition T) hwreath

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
