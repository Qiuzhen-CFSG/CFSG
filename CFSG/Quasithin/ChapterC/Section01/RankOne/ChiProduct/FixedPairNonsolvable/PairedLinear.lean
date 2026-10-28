module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairNonsolvable.PairedControl
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearSource

/-!
# The original universal pair in the nonsolvable paired linear branch

The actual component of the first factor preimage belongs to the local
class with the original Baumann subgroup as Sylow subgroup. Its escape
from the original fixed-pair control excludes both normal alternatives
for that same pair. The resulting ambient chi-block has full original
Thompson movement and its module is the original module commutator.

Source: Aschbacher--Smith C.1.26--28 and 14.1.11, pp.132--134,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairNonsolvable
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
open GlaubermanNiles SelectedRankOne FixedPairSolvable
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_linear_moved_chi_of_fixed_pair_escape
    {C : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (P : CharacteristicPair (baumann (T : Subgroup G))) (hPpair : P.Universal.{u,u})
    (hM : control T P ≠ ⊤) :
    ∃ L : Subgroup G, ¬ L ≤ control T P ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U := by
  let M := control T P
  have hTM : (T : Subgroup G) ≤ M := (T : Subgroup G).le_normalizer.trans (normalizer_le_control T P)
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := d.first.map Y.subtype
  let B := baumann (T : Subgroup G)
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let := offenderSubgroup_normal α
  let := d.product.first_normal
  let : Nontrivial d.first := d.firstCase.nontrivial
  let : Nontrivial A := (d.first.equivMapOfInjective Y.subtype Y.subtype_injective).injective.nontrivial
  obtain ⟨L,hL,hi,hcan,hUL,hBL,hlocal,hv⟩ :=
    first_component_localClass h36 hG T hP U hU hJ q hq hk hs hfit d F c hexchange
  let := hL.perfect
  have hpL : IsPPerfect 2 L := by
    intro N hN hp
    let := hN
    let : Group.IsNilpotent (L ⧸ N) := hp.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := L)]
    exact solvableResidual_le_of_solvable_quotient N
  obtain ⟨ρ,hρ,hnat,heρ,⟨hJq,hBq⟩,hfix⟩ :=
    source_images_and_fixedSpace T hP U hU hJ q hq hk d F c hexchange
  have hYA : Y ≤ normalizer (A : Set H) := by
    have hh := d.first.le_normalizer_map Y.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hout := selected_component_outside_sylow_overgroup T hP U hU hJ q hq hk Y A
    (hJq.le.trans inf_le_right) hYA L hL hcan M hTM hM
  have hb := FixedPair.fixed_pair_block_of_escape T P hPpair ⊤ (L ⊔ B) le_top le_sup_right hlocal (by
    simpa only [M,FixedPairSolvable.control,top_inf_eq] using
      (show ¬ L ⊔ B ≤ M from fun h => hout (le_sup_left.trans h)))
  have hchi := selected_component_chi_of_blockAlternative T L hL hpL hBL hb
  let D := Matrix.SpecialLinearGroup (Fin 2) F.Carrier
  let e : A ≃* D := first_axis_equiv Y d.first c.action.groupEquiv c.first_eq
  have hF := paired_linear_field_large T hP U hU hJ q hq hk hs d F c
  have hlarge : 3 < Nat.card F.Carrier := by
    rw [F.card_eq] at hF ⊢
    have hd : 2 ≤ F.degree := by
      by_contra! hh
      have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
      norm_num at hp
      omega
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    norm_num at hp
    omega
  let : Group.IsPerfect D := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier hlarge
  let : IsQuasisimple D := ⟨Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)⟩
  let : IsQuasisimple A := IsQuasisimple.of_mulEquiv e.symm
  let eA : d.first ≃* D := (d.first.equivMapOfInjective Y.subtype Y.subtype_injective).trans e
  let : IsQuasisimple d.first := IsQuasisimple.of_mulEquiv eA.symm
  have hz : center d.first = ⊥ := GorensteinWalter.center_eq_bot_of_mulEquiv eA
    Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot
  obtain ⟨S,hS⟩ := (T.mapSurjective hq).exists_sylow_map_eq_inf_of_normal Y
  have hmove : ⁅L.map q,J.map q⁆ = L.map q := by
    have hS' : (S : Subgroup Y).map Y.subtype = (T : Subgroup G).map q ⊓ Y := hS
    rw [hi,hJq,←hS']
    exact normal_quasisimple_factor_sylow_commutator Y d.first hz S
  have hJL : J ≤ normalizer (L : Set G) := selected_component_normalized q A L J hcan
    ((hJq.le.trans inf_le_right).trans hYA)
  have hnsol : ¬ Group.IsSolvable (L.map q) := by
    rw [hi]
    exact Group.IsPerfect.not_isSolvable A
  have hmovement := component_moved_of_image q L J hL hJL hmove hnsol
  have hWne : ⁅U,L⁆ ≠ ⊥ := by
    intro hz
    have hLU : L ≤ centralizer (U : Set G) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hz)
    have hbot : L.map q = ⊥ := (map_eq_bot_iff L).mpr (hk.symm ▸ hLU)
    have ha : A = ⊥ := hi.symm.trans hbot
    exact (Subgroup.nontrivial_iff_ne_bot A).mp inferInstance ha
  have hsupport := blockU_eq_nontrivial_normal_module_commutator L U hchi.1 hWne
  exact ⟨L,hout,hchi,hmovement,hsupport,hsupport.le.trans (commutator_le_left _ _)⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairNonsolvable
