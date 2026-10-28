module

public import CFSG.Quasithin.MainConverse.Transport
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CenterOrder
public import Theory.GroupTheory.CenterTwoCoreSylowPromotion
public import Theory.GroupTheory.SylowLocalCentralizerCriterion

/-!
# Even characteristic of the J₄ carrier

The inclusion of the literal matrix centralizer has image exactly C_Model(a).
Its induced equivalence transports the self-centralizing two-core and the
order-two center of that core to the full centralizer in the model. The
generic centralizer Sylow-promotion theorem then gives an ambient Sylow
two-subgroup whose center has image precisely the powers of a.

Every central involution of this Sylow subgroup is therefore a. The local
centralizer criterion proves characteristic two for every two-local
containing this Sylow subgroup, and Sylow conjugacy supplies condition E.
The concrete local inputs are unconditional, so the result holds directly
on the carrier and transports across any actual model equivalence.

Source: Aschbacher–Smith, Theorem 0.1.2(5), printed p.4, repeated as
Theorem 0.1.1(5), printed p.482; condition E on pp.3–4 and pp.481–482.
GLS3, Table 5.3i, printed p.270 motivates the local structure; the imported
matrix certificates prove the needed facts without a table premise.
-/

namespace CFSG.Quasithin.MainConverse.SporadicLocal.J4SylowCenterEven

open Subgroup Janko4
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- This equivalence is the actual inclusion, restricted to its proved range. -/
private noncomputable def centralizerEquiv :
    involutionCentralizer ≃* centralizer ({a} : Set Model) :=
  (MonoidHom.ofInjective centralizerToModel_injective).trans
    (MulEquiv.subgroupCongr centralizerToModel_range)

-- Explicit subgroup group structures avoid unfolding the concrete matrix carrier
-- while inferring the instances in these two transport steps.
private theorem centralizer_characteristicTwo :
    HasCharacteristicTwo (centralizer ({a} : Set Model)) :=
  (@Theory.Quasithin.centralizer_pCore_le_iff
    involutionCentralizer (centralizer ({a} : Set Model))
    involutionCentralizer.toGroup (centralizer ({a} : Set Model)).toGroup
    2 centralizerEquiv).mp localTwoCoreCentralizerControl.1

private theorem centralizer_twoCore_center_card :
    Nat.card (center (pCore 2 (centralizer ({a} : Set Model)))) = 2 := by
  let eQ : involutionTwoCore ≃* pCore 2 (centralizer ({a} : Set Model)) :=
    (@MulEquiv.subgroupMap involutionCentralizer (centralizer ({a} : Set Model))
      involutionCentralizer.toGroup (centralizer ({a} : Set Model)).toGroup
      centralizerEquiv involutionTwoCore).trans
      (MulEquiv.subgroupCongr
        (@pCore_map_iso involutionCentralizer (centralizer ({a} : Set Model))
          involutionCentralizer.toGroup (centralizer ({a} : Set Model)).toGroup
          2 centralizerEquiv))
  exact (Nat.card_congr (@centerCongr involutionTwoCore involutionTwoCore.toGroup
    (pCore 2 (centralizer ({a} : Set Model)))
    (pCore 2 (centralizer ({a} : Set Model))).toGroup eQ).toEquiv).symm.trans
      TwoCoreComparison.center_card_two

private theorem exists_sylow_center :
    ∃ T : Sylow 2 Model,
      (center (T : Subgroup Model)).map (T : Subgroup Model).subtype = zpowers a := by
  let P : Sylow 2 (centralizer ({a} : Set Model)) := default
  obtain ⟨T, hT⟩ := (centralizer_structure_of_center_two_core a orderOf_a
    centralizer_twoCore_center_card centralizer_characteristicTwo).2.2 P
  refine ⟨T, ?_⟩
  rw [hT]
  exact mapped_sylow_center_of_center_two_core a orderOf_a
    centralizer_twoCore_center_card centralizer_characteristicTwo P

private theorem sylow_central_involution_eq (T : Sylow 2 Model)
    (hcenter : (center (T : Subgroup Model)).map (T : Subgroup Model).subtype = zpowers a)
    (z : T) (hz : z ∈ center T) (ho : orderOf z = 2) : (z : Model) = a := by
  classical
  have hm : (z : Model) ∈ zpowers a := by
    rw [← hcenter]
    exact mem_map_of_mem (T : Subgroup Model).subtype hz
  rw [mem_zpowers_iff_mem_range_orderOf, orderOf_a] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hlt : n < 2 := Finset.mem_range.mp hn
  have hn : n = 0 ∨ n = 1 := by omega
  rcases hn with rfl | rfl
  · have hz1 : z = 1 := Subtype.ext (by simpa using he.symm)
    simp [hz1] at ho
  · simpa using he.symm

/-- The actual binary-matrix J₄ carrier has even characteristic. -/
public theorem evenCharacteristic : IsEvenCharacteristic Model := by
  obtain ⟨T, hT⟩ := exists_sylow_center
  apply IsEvenCharacteristicAt.all (T := T)
  intro M hM hTM
  obtain ⟨Q, hQ, hp, rfl⟩ := hM.1
  apply normalizer_core_selfCentralizing_of_sylow_centralizers T Q hp hQ hTM
  intro z hz ho
  rw [sylow_central_involution_eq T hT z hz ho]
  exact centralizer_characteristicTwo

/-- Condition E transports through the actual J₄ model equivalence.
The carrier proof makes simplicity and nonabelianness unnecessary here. -/
public theorem evenCharacteristic_of_equiv {G : Type*} [Group G] [Finite G]
    (e : G ≃* Model) : IsEvenCharacteristic G :=
  evenCharacteristic_of_model_equiv e evenCharacteristic

end CFSG.Quasithin.MainConverse.SporadicLocal.J4SylowCenterEven
