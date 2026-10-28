module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.SignalizerReduction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.PrimeSignalizers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Triangle.Radical.ModelQuotients

/-!
# Radical containment for the actual prime-field radical quotient

Inside J = KT the normal component is B = K.subgroupOf J. The isomorphism
B ≃ K identifies their radical quotients. The image of the nontrivial
perfect first residual under the literal action on B/O∞(B) is nontrivial,
since the action kernel is solvable. The proved prime-field signalizer
theorem therefore kills the image of O₂(L₁T).
Source: Aschbacher--Smith 11.4.1(3), printed p.776.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
variable {G : Type*} [Group G] [Finite G]

/-- The radical containment has no remaining signalizer premise. -/
theorem local_core_le_radical_of_prime_model (T : Sylow 2 G) (A K : Subgroup G)
    [Group.IsPerfect A] (hA : A ≠ ⊥) (hAK : A ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ solvableRadical K) 2 p) :
    (A ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype := by
  let J := K ⊔ (T : Subgroup G)
  let B := K.subgroupOf J
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le K.le_normalizer hTK)
  have hq : IsPGroup 2 (J ⧸ B) := isPGroup_quotient_of_sup_eq_top B
    ((T : Subgroup G).subgroupOf J) T.isPGroup'.comap_subtype (by
      rw [← subgroupOf_sup (show K ≤ J from le_sup_left)
        (show (T : Subgroup G) ≤ J from le_sup_right), subgroupOf_self])
  let : Group.IsNilpotent (J ⧸ B) := hq.isNilpotent
  let C := A.subgroupOf J
  have hAJ : A ≤ J := hAK.trans le_sup_left
  let : Group.IsPerfect C := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hAJ).symm.toMonoidHom)
    (subgroupOfEquivOfLe hAJ).symm.surjective
  have hC : C ≠ ⊥ := by
    intro he
    apply hA
    simpa only [C, map_subgroupOf_eq_of_le hAJ, Subgroup.map_bot] using congrArg (map J.subtype) he
  let α := normalQuotientAction B (solvableRadical B)
  let : Group.IsPerfect (C.map α) := Group.IsPerfect.map _
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let eB : B ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eQ := (QuotientGroup.congr _ _ eB (map_solvableRadical_equiv eB)).trans e
  apply local_core_le_radical_of_signalizers T A K hAK hTK
    (radical_quotient_center_eq_bot B)
  intro U hU hn
  exact prime_model_two_signalizer_eq_bot hp F hF eQ (C.map α) U
    (radical_action_image_ne_bot B C hC) hU hn

variable {T : Sylow 2 G} {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- Application to the original flag and residual, with its actual radical model. -/
theorem ofFlag_radical_containment_of_prime_model (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H K : Subgroup G)
    (hA : f.Li 0 ≠ ⊥) (hAK : f.Li 0 ≤ K)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ solvableRadical K) 2 p) :
    (ofFlag S f X z H).R₁ ≤
      (solvableRadical (K ⊔ (T : Subgroup G) : Subgroup G)).map
        (K ⊔ (T : Subgroup G)).subtype := by
  let : Group.IsPerfect (f.Li 0) := LocalGeometry.localResidual_perfect _
  exact local_core_le_radical_of_prime_model T (f.Li 0) K hA hAK hTK hp hm

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Radical
