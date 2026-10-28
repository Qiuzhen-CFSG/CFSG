module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeLocalCores
public import Mathlib.Algebra.CharP.CharAndCard

/-!
# The natural action of the linear-three local groups

An actual isomorphism to the special affine plane identifies the intrinsic
two-core with translations. Its quotient isomorphism reads the literal linear
part, and the affine conjugation formula proves the natural-action identity
for every group element. Applying this to the existing point and line local
coordinates proves the action assertion in both SL₃(4) and PSL₃(4).

Recognition of arbitrary maximal parabolics as these concrete local groups
is a separate geometric obligation. No such recognition is assumed here.

Source: Aschbacher–Smith, F.1.12(I)(1), printed pp.262–264; the application
is A.3.14(1), pp.49–50, in the proof of Lemma 14.4.9, p.1010.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
open Chapter1.Section02.LocalModels

/-- Affine coordinates prove the natural action on the intrinsic two-core,
including the identification of the literal core quotient map. -/
theorem naturalSL2Action_of_affineEquiv {X : Type*} [Group X]
    (F : Type) [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : X ≃* Matrix.SL2.Affine F) :
    NaturalSL2Action X (pCore 2 X) 4 := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by
    simpa [Nat.card_eq_fintype_card] using hF)
  let c : pCore 2 X ≃* Matrix.SL2.translations F :=
    (e.subgroupMap (pCore 2 X)).trans
      (MulEquiv.subgroupCongr ((pCore_map_iso 2 e).trans
        (Matrix.SL2.affine_twoCore_eq F)))
  let v := c.trans (Matrix.SL2.translationsEquiv F).symm
  let ρ := (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    (Matrix.SL2.affineCoreQuotientEquiv F)
  have hv (x : pCore 2 X) : e x = SemidirectProduct.inl (v x) := by
    exact (congrArg Subtype.val
      ((Matrix.SL2.translationsEquiv F).apply_symm_apply (c x))).symm
  refine ⟨F, inferInstance, inferInstance, hF, v, ρ, ?_⟩
  intro g x
  change v _ = Matrix.SL2.naturalAction F (e g).right (v x)
  apply SemidirectProduct.inl_injective (φ := Matrix.SL2.naturalAction F)
  rw [← hv]
  change e (g * x * g⁻¹) = _
  rw [map_mul, map_mul, map_inv, hv, Matrix.SL2.conjugate_inl]

variable (F : Type) [Field F] [Finite F] (hF : Nat.card F = 4)
include hF
open Matrix.PSL3.LinearThree

/-- The concrete vector-stabilizer local in SL₃(4). -/
theorem pointLocalSL_natural :
    NaturalSL2Action (pointLocalSL F) (pCore 2 (pointLocalSL F)) 4 :=
  naturalSL2Action_of_affineEquiv F hF (pointLocalAffineEquiv F)

/-- The concrete covector-stabilizer local in SL₃(4). -/
theorem lineLocalSL_natural :
    NaturalSL2Action (lineLocalSL F) (pCore 2 (lineLocalSL F)) 4 :=
  naturalSL2Action_of_affineEquiv F hF (lineLocalAffineEquiv F)

/-- The actual projective point-local image in PSL₃(4). -/
theorem pointLocal_natural :
    NaturalSL2Action (pointLocal F) (pCore 2 (pointLocal F)) 4 :=
  naturalSL2Action_of_affineEquiv F hF (pointLocalEquivAffine F)

/-- The actual projective line-local image in PSL₃(4). -/
theorem lineLocal_natural :
    NaturalSL2Action (lineLocal F) (pCore 2 (lineLocal F)) 4 :=
  naturalSL2Action_of_affineEquiv F hF (lineLocalEquivAffine F)

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
