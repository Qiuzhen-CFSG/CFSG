module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.GraphLayers
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.ElementaryAbelianAction

/-!
# The actual action on the geometric center quotient

The center span is proved elementary by `GraphLayers`. Conjugation by any
subgroup of the vertex stabilizer therefore acts linearly on the literal
V_delta/Z_delta quotient. The source Chapter 8 identity
[V_delta,Q_delta] = Z_delta kills the actual two-core, so the action
descends to the actor's intrinsic core quotient. Every representative
retains its original conjugation formula; no representation witness or
conjugation-compatibility premise is required.

This constructs the action used on V_beta/Z_beta in DGS85 (12.6) and
(12.9)(c2), printed pp.183 and 186. The later Suzuki identification,
faithfulness, and q^4 upper bound are separate Chapter 12 obligations.
-/

@[expose] public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G) [∀ i, Finite (F i)]

/-- Construct the quotient representation from the source commutator bound. -/
theorem exists_center_layer_action
    (hgen : F false ⊔ F true = ⊤)
    (hZ : ∀ v, Z F v ≤ omegaCenterIn (Q F v))
    (hSyl : ∀ v, ∃ T : Sylow 2 (U F v),
      (T : Subgroup (U F v)).map (U F v).subtype = Q F v)
    (hb : 2 < b F) (v : Vertex F)
    (A : Subgroup G) (hA : A ≤ stabilizer F v)
    (hcore : A.pCoreIn 2 ≤ Q F v)
    (hcomm : ⁅V F v 1, Q F v⁆ ≤ Z F v) :
    let := V_elementary F hgen hZ hSyl hb v
    let : ((Z F v).subgroupOf (V F v 1)).Normal := normal_of_isMulCommutative _
    ∃ ρ : Representation (ZMod 2) (A ⧸ pCore 2 A)
      (Additive (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1))),
      ∀ a : A, ∀ x : V F v 1,
        (ρ (QuotientGroup.mk a) (Additive.ofMul (QuotientGroup.mk x))).toMul =
          QuotientGroup.mk ⟨(a : G) * (x : G) * (a : G)⁻¹,
            (mem_normalizer_iff.mp (stabilizer_normalizes_V F v 1 (hA a.property))
              x).mp x.property⟩ := by
  let := V_elementary F hgen hZ hSyl hb v
  let : ((Z F v).subgroupOf (V F v 1)).Normal := normal_of_isMulCommutative _
  have hAV := hA.trans (stabilizer_normalizes_V F v 1)
  have hAZ : A ≤ normalizer (Z F v : Set G) := hA.trans
    ((normal_subgroupOf_iff_le_normalizer (Z_le_stabilizer F v)).mp (Z_normal F v))
  obtain ⟨α, hα⟩ := exists_quotient_conjugation_action A (V F v 1) (Z F v)
    hAV hAZ inferInstance
  have hkill := quotient_conjugation_action_kills_commutator_layer A
    (V F v 1) (Z F v) (Q F v) inferInstance hAV hcomm α hα
  have hker : pCore 2 A ≤ α.ker := by
    intro a ha
    exact hkill (hcore (mem_map_of_mem A.subtype ha))
  let β := QuotientGroup.lift (pCore 2 A) α hker
  let : MulDistribMulAction (A ⧸ pCore 2 A)
      (V F v 1 ⧸ (Z F v).subgroupOf (V F v 1)) := MulDistribMulAction.compHom _ β
  refine ⟨Representation.ofElementaryAbelianAction, ?_⟩
  intro a x
  exact hα a x

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingThreeProfile
