module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.Block
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.LocalAction

/-!
# The genuine paired symmetric-five branch of C.1.28

The original marked quotient selects its first alternating component. Its
normalizing Sylow supplement and original moved module yield the full local
S5 action, using the same odd Thompson element. The external C.1.23 theorem
then gives an A5 block. Actual Sylow-conjugate generation forces this selected
component outside every proper characteristic-normalizer control subgroup;
its intrinsic block module is exactly [U,L].

Every component, quotient, action, Sylow, and block witness is constructed
from the original source hypotheses. The sole earlier input is genuine A.3.6.
Source: Aschbacher–Smith C.1.23 and C.1.26–28, pp.129–130,132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction Chapter1.Section02
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
theorem paired_five_outside_moved_chi
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := (alternatingGroup (Fin 5)).map (SymmetricFive.Paired.leftFactorMap Y c.action.groupEquiv)
  let := offenderSubgroup_normal α
  obtain ⟨L,hL,hi,⟨eL⟩,hcan,hUL,hBL,hfitN,R,hR⟩ :=
    first_five_component_geometry h36 hG T hP U hU hJ q hq hk hs hfit d c hexchange
  let N := PairedFive.localJoin (T : Subgroup G) L
  let V := PairedFive.localMoved (T : Subgroup G) U L
  have hLN : L ≤ N := le_sup_left
  have hWL : (⁅U,L⁆ : Subgroup G) ≤ L := le_normalizer_iff_commutator_le_right.mp hUL
  have hV : V.map N.subtype = ⁅U,L⁆ := map_subgroupOf_eq_of_le (hWL.trans hLN)
  have hJA : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ Y :=
    RankOneBaumann.thompson_image_le_offender_layer T U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) Y le_rfl
  have hout := selected_component_outside_control T hP U hU hJ q hq hk Y A hJA
    (five_first_axis_normalized Y c.action.groupEquiv) L hL hcan M hcpu hM
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  obtain ⟨p,hp,hpk,f,hLp,he,hJR⟩ :=
    PairedFive.first_local_action T hP U hU hJ q hq hk d c hexchange L hi hUL hBL R hR
  have hBR : baumann (T : Subgroup G) ≤ (R : Subgroup N).map N.subtype := by
    rw [hR]
    exact le_inf inf_le_left hBL
  have hRT : (R : Subgroup N).map N.subtype ≤ T := by rw [hR]; exact inf_le_left
  have hprod : L.subgroupOf N ⊔ (R : Subgroup N) = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLN,hR,←MonoidHom.range_eq_map,range_subtype]
  let a : L.subgroupOf N ≃* L := subgroupOfEquivOfLe hLN
  let e : ((L.subgroupOf N) ⧸ pCore 2 (L.subgroupOf N)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eL
  have hb := selected_five_block_of_external_action T hTne U L hL M hcpu hout N hLN
    R hBR hRT hfitN hprod e V hV p hp hpk hLp f he hJR
  exact ⟨L,hout,hb⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
