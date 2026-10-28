module

public import Theory.GroupTheory.NormalizerAction
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupAction.PerfectCentralQuotient
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.FieldAction

/-!
# The literal component action on a Suzuki model

The normalizer conjugation action passes through the center quotient and
then the actual equivalence K/Z(K) ≃ K* ≃ Sz. Faithfulness of automorphisms
on a perfect central quotient identifies its kernel with C_D(K), including
central covers. The cubic-field record specifies the remaining output: an
actual order-three element of D acting as an order-three entrywise field
automorphism. No existence of this record is asserted here.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, 13.6.6, p.927.
SuzukiMatrixGroup n has defining-field degree 2*n+1; source m=3 is n=1.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
variable {H S : Type*} [Group H] [Group S]

noncomputable def modelAction (K D : Subgroup H)
    (hn : D ≤ normalizer (K : Set H))
    (eK : NormalizerAction.componentImage K ≃* S) : D →* MulAut S :=
  (MulAut.centralQuotientAction ((NormalizerAction.componentCentralQuotientEquiv K).trans eK)).comp
    (K.normalizerMonoidHom.comp (inclusion hn))

theorem modelAction_apply (K D : Subgroup H)
    (hn : D ≤ normalizer (K : Set H))
    (eK : NormalizerAction.componentImage K ≃* S) (d : D) (k : K) :
    modelAction K D hn eK d
      (eK (NormalizerAction.componentCentralQuotientEquiv K (QuotientGroup.mk' (center K) k))) =
    eK (NormalizerAction.componentCentralQuotientEquiv K
      (QuotientGroup.mk' (center K) (K.normalizerMonoidHom (inclusion hn d) k))) :=
  MulAut.centralQuotientAction_apply _ _ _

theorem modelAction_eq_one_iff (K D : Subgroup H) (hK : IsComponent H K)
    (hn : D ≤ normalizer (K : Set H))
    (eK : NormalizerAction.componentImage K ≃* S) (d : D) :
    modelAction K D hn eK d = 1 ↔ (d : H) ∈ centralizer (K : Set H) := by
  let := hK.2
  have he : modelAction K D hn eK d = 1 ↔ K.normalizerMonoidHom (inclusion hn d) = 1 := by
    constructor
    · intro hd
      exact MulAut.centralQuotientAction_injective
        ((NormalizerAction.componentCentralQuotientEquiv K).trans eK)
        (hd.trans (map_one _).symm)
    · intro hd
      change MulAut.centralQuotientAction _ (K.normalizerMonoidHom (inclusion hn d)) = 1
      rw [hd, map_one]
  rw [he]
  change inclusion hn d ∈ K.normalizerMonoidHom.ker ↔ _
  rw [normalizerMonoidHom_ker]
  rfl

theorem modelAction_ker (K D : Subgroup H) (hK : IsComponent H K)
    (hn : D ≤ normalizer (K : Set H))
    (eK : NormalizerAction.componentImage K ≃* S) :
    (modelAction K D hn eK).ker = (centralizer (K : Set H)).subgroupOf D := by
  ext d
  exact modelAction_eq_one_iff K D hK hn eK d

open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII

/-- The actual cubic actor, with a literal field automorphism on the identified
central quotient. The matrix parameter n means field degree 2*n+1. -/
structure CubicFieldAction (K D : Subgroup H)
    (hn : D ≤ normalizer (K : Set H)) (n : ℕ)
    (eK : NormalizerAction.componentImage K ≃* SuzukiMatrixGroup n) where
  cubic : D
  cubic_order : orderOf cubic = 3
  field : BinaryGaloisField (2 * n + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * n + 1)
  field_order : orderOf field = 3
  action_eq : modelAction K D hn eK cubic = suzukiFieldAut n field

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent
