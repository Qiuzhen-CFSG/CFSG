module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearLocalClass
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedBlockSteps
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedMovement
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.UniformPair
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Support
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
/-!
# An outside chi-block from the original paired linear source

Select the genuine component of the original first-factor preimage.
Its actual Baumann join lies in the C.1.17 local class. The single uniform
C.1.18 pair eliminates both normal alternatives by characteristic-normalizer
control, leaving a chi-block. The same quotient Sylow moves this component,
and the nonzero original module commutator is its intrinsic block module.

Source: Aschbacher–Smith C.1.26, printed p.132, using B.6.9–10.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
theorem paired_linear_outside_moved_chi
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
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U := by
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
  have hout := selected_component_outside_control T hP U hU hJ q hq hk Y A
    (hJq.le.trans inf_le_right) hYA L hL hcan M hcpu hM
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  obtain ⟨P,hPpair⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  have hb := blockAlternative_of_selected_outside (T : Subgroup G) (L ⊔ B) M le_sup_right
    hcpu (fun h => hout (le_sup_left.trans h)) P hPpair hlocal
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
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
