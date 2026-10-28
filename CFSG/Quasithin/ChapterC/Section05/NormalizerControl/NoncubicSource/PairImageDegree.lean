module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.FittingPairSource
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.BinaryDegree
public import Theory.GroupTheory.CharacteristicTwoSmallModuleKernel
/-!
# The faithful degree bound for the literal two-conjugate pair

The original reduced source gives [O2(G),K]=U(K) and makes the pair
span W=U(K)+U(K)^g elementary and invariant. If the pair image in
G/O2(G) has trivial two-core, its centralizer kernel on W is exactly
its quotient kernel. The resulting faithful binary action has degree
at most twelve when |U(K)| is at most 64. The genuine noncentral-Fitting
source theorem therefore makes every C-component of this actual pair
image have central Fitting subgroup. No action of a two-core quotient
is assumed to descend without a kernel calculation.
Source: Aschbacher--Smith C.5.12, printed p.163.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
theorem six_pair_span_rank (U : Subgroup G) (hU : Nat.card U ≤ 64) (g : G)
    (X : Subgroup G) (hVX : U ⊔ U.conjBy g ≤ X)
    [IsElementaryAbelian 2 (U ⊔ U.conjBy g : Subgroup G)] :
    let : IsElementaryAbelian 2 ((U ⊔ U.conjBy g).subgroupOf X) := IsElementaryAbelian.subgroupOf hVX
    Module.finrank (ZMod 2) (Additive ((U ⊔ U.conjBy g).subgroupOf X)) ≤ 12 := by
  let V := U ⊔ U.conjBy g
  let : IsElementaryAbelian 2 (V.subgroupOf X) := IsElementaryAbelian.subgroupOf hVX
  have hUc : U.conjBy g ≤ centralizer (U : Set G) := by
    intro w hw u hu
    exact congrArg V.subtype (mul_comm (⟨u,mem_sup_left hu⟩ : V) ⟨w,mem_sup_right hw⟩)
  have hW : Nat.card (U.conjBy g) ≤ 64 :=
    (Nat.card_congr (U.equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).toEquiv).symm.le.trans hU
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes U (U.conjBy g)
    (hUc.trans (Subgroup.centralizer_le_normalizer _))
  have hpos : 0 < Nat.card (U ⊓ U.conjBy g : Subgroup G) := Nat.card_pos
  have hcV : Nat.card V ≤ 4096 := by
    change Nat.card (U ⊔ U.conjBy g : Subgroup G) ≤ 4096
    nlinarith
  have he : Nat.card (Additive (V.subgroupOf X)) = Nat.card V :=
    (Nat.card_congr Additive.toMul).trans (Nat.card_congr (subgroupOfEquivOfLe hVX).toEquiv)
  have hn : Nat.card (Additive (V.subgroupOf X)) =
      2 ^ Module.finrank (ZMod 2) (Additive (V.subgroupOf X)) := by
    simpa only [Nat.card_eq_fintype_card,ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (V.subgroupOf X)))
  have hp : 2 ^ Module.finrank (ZMod 2) (Additive (V.subgroupOf X)) ≤ 2 ^ 12 := by
    rw [← hn,he]
    exact hcV
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2:ℕ))).mp hp

theorem reduced_pair_image_fitting_central
    {κ : GroupClass} (K V : Subgroup G) (hK : IsShort K)
    (S : Sylow 2 G) (hSK : (S : Subgroup G) ≤ normalizer (K : Set G))
    (hV : IsPReduced 2 V) (hUV : U K ≤ V)
    (hchar : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hU : Nat.card (U K) ≤ 64) (g : G)
    (hSQTK : IsSQTK κ ((K ⊔ K.conjBy g).map (QuotientGroup.mk' (pCore 2 G))))
    (hO : pCore 2 ((K ⊔ K.conjBy g).map (QuotientGroup.mk' (pCore 2 G))) = ⊥)
    (L : Subgroup ((K ⊔ K.conjBy g).map (QuotientGroup.mk' (pCore 2 G))))
    (hL : L.IsCComponent) : fittingSubgroup L ≤ center L := by
  let D := K ⊔ K.conjBy g
  let W := U K ⊔ (U K).conjBy g
  let Q := pCore 2 G
  let q := QuotientGroup.mk' Q
  have hWD : W ≤ D := sup_le_sup (map_subtype_le _) (map_mono (map_subtype_le _))
  have hcomm := source_core_commutator_of_reduced K V hK S hSK hV hUV
  have hpair := conjugate_pair_span_kernel K (U K) g hchar hcomm
  let : V.Normal := hV.normal
  let : IsElementaryAbelian 2 V := hV.elementary
  have hUgV : (U K).conjBy g ≤ V := by
    have hm : V.map (MulAut.conj g).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_of_normal (mem_top g))
    exact (map_mono hUV).trans_eq hm
  have hWV : W ≤ V := sup_le hUV hUgV
  let : IsElementaryAbelian 2 W := {
    toIsMulCommutative := IsMulCommutative.of_comm (fun a b =>
      Subtype.ext (congrArg V.subtype (mul_comm (⟨a,hWV a.property⟩ : V) ⟨b,hWV b.property⟩)))
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun w =>
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : G) (hWV w.property))) }
  let : IsElementaryAbelian 2 (W.subgroupOf D) := IsElementaryAbelian.subgroupOf hWD
  let : (W.subgroupOf D).Normal := (normal_subgroupOf_iff_le_normalizer hWD).mpr hpair.1
  have hQW : Q ≤ centralizer (W : Set G) := by
    have hc : Q ≤ centralizer (V : Set G) := le_centralizer_iff.mp hV.le_centralizer_pCore
    exact hc.trans (centralizer_le hWV)
  have hk := centralizer_small_module_eq_quotient_kernel Q D W hchar
    (IsElementaryAbelian.isPGroup 2 W) hWD hpair.1 hQW (by
      rw [commutator_comm]; exact hpair.2.1) hO
  let f := q.subgroupMap D
  have hfk : f.ker = centralizer (W.subgroupOf D : Set D) := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact hk.symm
  let e := (QuotientGroup.quotientMulEquivOfEq hfk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (q.subgroupMap_surjective D))
  let ρ := (Representation.centralizerQuotient (W.subgroupOf D)).comp
    (e.symm.toMonoidHom.comp L.subtype)
  have hi : Function.Injective (Representation.centralizerQuotient (W.subgroupOf D)) := by
    intro a b hab
    apply Representation.centralizerQuotient_faithful _
    exact Units.ext hab
  have hf : Function.Injective ρ := hi.comp (e.symm.injective.comp L.subtype_injective)
  have hd := six_pair_span_rank (U K) hU g D hWD
  exact ChapterA.Section03.NoncentralFitting.fitting_le_center_of_binary_degree_le_twelve
    hSQTK hO hL ρ hf hd
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
