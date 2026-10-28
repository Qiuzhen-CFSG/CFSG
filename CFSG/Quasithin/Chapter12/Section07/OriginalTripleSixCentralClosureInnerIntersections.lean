module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureDegreeFiveExclusion
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureElementary
import Theory.Representation.HexacodeAction.WeightFourEvenNormalTwo
import Theory.Representation.HexacodeAction.WeightFourVectorCore
import Theory.GroupTheory.SylowNormalizedResidual
import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Maximal

/-!
# The literal intersections in the inner central-closure branch

The marked weight-four Klein four has fixed space exactly the original
scalar point. Transporting that equality identifies C_U(W), and elementary
abelianity of the whole closure identifies U intersect W. The full actor
and degree-five exclusion bound the same literal W by orders 16 and 32.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original point is exactly both the fixed subgroup and the intersection
of the unchanged U with its smaller closure, whose order is 16 or 32. -/
theorem original_tripleSix_central_closure_inner_intersections
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K) :
    let V1 := tripleSixPoint D a z
    let W := conjugateSpanBy V1 (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))
    U ⊓ centralizer (W : Set G) = V1 ∧ U ⊓ W = V1 ∧
      Nat.card (inducedAutomizer U W) = 4 ∧ (Nat.card W=16 ∨ Nat.card W=32) := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let V1 := tripleSixPoint D a z
  let W := conjugateSpanBy V1 R
  let c := tripleSixPointCoordinates D a
  let v := (c z).toAdd
  obtain ⟨hWT,f,hf,hfk,hK,hchart,hN,hp,hne,_⟩ :=
    original_tripleSix_central_closure_automizer h structural D a z hz hzT hnot
  let N := (inducedAutomizer U W).map f
  have hTN : (T : Subgroup G) ≤ normalizer (U : Set G) := ((structural K h).2.2 U D).1
  have hWN : W ≤ normalizer (U : Set G) := hWT.trans hTN
  have hc := original_tripleSix_central_closure_configuration h structural D a z hz hzT hnot
  have hWH : W = conjugateSpanBy V1 H := hc.2.1
  have hHW : H ≤ normalizer (W : Set G) := by
    rw [hWH]
    exact le_normalizer_conjugateSpanBy V1 H
  have hCK : K ⊓ C ≤ H :=
    (le_embedded_pResidual_sup_sylow_of_normalizes T (K ⊓ C)
      ((le_inf D.sylow_normalizes_component (hzT.trans C.le_normalizer)).trans
        inf_normalizer_le_normalizer_inf)).trans
      (sup_le (le_sup_right.trans le_sup_left) le_sup_right)
  have hCKimage : (inducedAutomizer U (K ⊓ C)).map f =
      (Hexacode.fullWeightVectorStabilizer v).map hexSign.ker.subtype := by
    apply le_antisymm
    · rintro _ ⟨_,⟨k,hk,rfl⟩,rfl⟩
      rw [hfk ⟨k,hk.1⟩]
      exact ⟨(tripleSixPointCentralizerProjection D a z ⟨k,hk⟩).val,
        (tripleSixPointCentralizerProjection D a z ⟨k,hk⟩).property,rfl⟩
    · rintro _ ⟨g,hg,rfl⟩
      obtain ⟨k,hk⟩ := tripleSixPointCentralizerProjection_surjective D a z ⟨g,hg⟩
      refine ⟨U.normalizerMonoidHom.rangeRestrict ⟨k,D.normalizes k.property.1⟩,
        ⟨⟨k,D.normalizes k.property.1⟩,k.property,rfl⟩,?_⟩
      rw [hfk ⟨k,k.property.1⟩]
      exact congrArg (fun q => q.val.val) hk
  have hn : (Hexacode.fullWeightVectorStabilizer v).map hexSign.ker.subtype ≤
      normalizer (N : Set HexAutomorphisms) := by
    rw [←hCKimage]
    exact (map_mono (ChapterE.Section06.inducedAutomizer_normalized hWN
      (hCK.trans hHW))).trans (le_normalizer_map f)
  have heven : N ≤ hexSign.ker := by
    rw [←hK]
    exact map_mono hinner
  have hv := tripleSix_sylow_fixed_weightFour D a z hz hzT
  have hcore := Hexacode.weightFour_even_normal_two_eq_core v hv N hN hp hne hn heven
  have hp := tripleSixPoint_properties D a z hz
  have hVW : V1≤W := le_conjugateSpanBy V1 R
  let : IsElementaryAbelian 2 W :=
    (original_tripleSix_central_closure_elementary h structural D a z hz hzT hnot hinner).1
  have hfix : U ⊓ centralizer (W : Set G)=V1 := by
    apply le_antisymm
    · intro u hu
      refine ⟨⟨u,hu.1⟩,?_,rfl⟩
      change (c ⟨u,hu.1⟩).toAdd∈Submodule.span Hexacode.F {v}
      have hf : (c ⟨u,hu.1⟩).toAdd∈fixedSpace Hexacode.evenAction
          ((Hexacode.fullWeightVectorStabilizer v).pCoreIn 2) := by
        intro g
        have hg : g.val.val∈N := hcore.symm ▸ mem_map_of_mem hexSign.ker.subtype g.property
        obtain ⟨b,⟨w,hw,hwmark⟩,hbg⟩ := hg
        have hucomm : (U.normalizerMonoidHom.rangeRestrict w).val ⟨u,hu.1⟩ = ⟨u,hu.1⟩ := by
          apply Subtype.ext
          exact mul_inv_eq_of_eq_mul (mem_centralizer_iff.mp hu.2 w hw)
        have hc := hchart (U.normalizerMonoidHom.rangeRestrict w) ⟨u,hu.1⟩
        rw [hucomm,hwmark,hbg] at hc
        exact hc.symm
      rw [Hexacode.weightFourVectorCore_fixed v hv] at hf
      exact hf
    · exact le_inf hp.2.1 ((le_centralizer_iff_isMulCommutative.mpr
        (inferInstance : IsMulCommutative W)).trans' hVW)
  have hmeet : U ⊓ W=V1 := by
    apply le_antisymm
    · exact (le_inf inf_le_left (inf_le_right.trans
        (le_centralizer_iff_isMulCommutative.mpr (inferInstance : IsMulCommutative W)))).trans_eq hfix
    · exact le_inf hp.2.1 hVW
  have hfour : Nat.card (inducedAutomizer U W)=4 := by
    rw [←card_map_of_injective hf]
    change Nat.card N=4
    rw [hcore,card_map_of_injective hexSign.ker.subtype_injective]
    let e := Hexacode.weightFourVectorStabilizerEquiv v hv
    rw [pCoreIn,card_map_of_injective (Hexacode.fullWeightVectorStabilizer v).subtype_injective,
      ←card_map_of_injective (f:=e.toMonoidHom) e.injective,pCore_map_iso 2 e,
      ←Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_eq,
      Theory.SpecificGroups.SymmetricSix.DuadCalculation.core_card]
  refine ⟨hfix,hmeet,hfour,?_⟩
  change Nat.card W=16 ∨ Nat.card W=32
  let Z := zpowers (z:G)
  obtain ⟨_,hZN,hr⟩ := original_tripleSix_central_closure_full_actor
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,_,_,_,_,x,_,_,_,_,_,_,_,_,_,_,_,_,_,hdim⟩ := hr
  let := he
  let : IsElementaryAbelian 2 U := D.elementary
  have hzorder : orderOf (z:G)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property)
    (fun hh => hz (Subtype.ext hh))
  have hZcard : Nat.card Z=2 := by rw [Nat.card_zpowers,hzorder]
  have hZW : Z≤W := (zpowers_le.mpr hp.1).trans hVW
  have hc := (Z.subgroupOf W).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv,hZcard] at hc
  change Nat.card (W ⧸ Z.subgroupOf W)*2=Nat.card W at hc
  have hvcard := Module.natCard_eq_pow_finrank (K:=ZMod 2)
    (V:=Additive (W ⧸ Z.subgroupOf W))
  rw [Nat.card_zmod] at hvcard
  change Nat.card (W ⧸ Z.subgroupOf W)=_ at hvcard
  have hne := original_tripleSix_central_closure_not_card_sixtyFour
    h structural D a z hz hzT hnot hinner
  change Nat.card W≠64 at hne
  rcases hdim with hd | hd | hd <;> rw [hd] at hvcard <;> norm_num at hvcard <;> omega

end CFSG.Quasithin.Chapter12.Section07
