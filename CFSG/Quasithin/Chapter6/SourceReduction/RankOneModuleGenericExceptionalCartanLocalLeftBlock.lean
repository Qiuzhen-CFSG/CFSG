module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLeftFixed
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairSolvable.Subtype
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.SeedControl
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.QuasisimpleCoordinates
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.RankOneFieldSize
/-!
# The left block alternative with the original characteristic pair

The original escaping cubic and Thompson normalization force the natural
left FF branch. Its actual omega-span supplies the Glauberman–Niles local
class inside LT. Transport one uniform pair on Baum(T) through this
inclusion. Left fixed-space vanishing excludes the first characteristic
alternative; the second gives normalization by LT, while the block branch
retains the original L and its complete chi-block action.

Local uniqueness controls the full ambient normalizer of the second
characteristic subgroup. Thus a nonblock left side makes the original
right residual escape that normalizer. The final theorem uses the proved
FF reduction under the original universal Input and both Hall conditions.
The companion RightBlock module supplies the second application. Both
block exclusions remain necessary.

Source: Aschbacher–Smith 5.1.13, printed pp.637–638, using C.1.18 and C.1.28.
-/

public noncomputable section
universe u v
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.QuasisimpleSource ChapterB.SourceInduction
variable {G : Type u} {H : Type v} [Group G] [Finite G] [Group H] [Finite H]
attribute [local instance] RankOneBaumann.semilinear_moved_elementary

private theorem quasisimple_natural_localClass
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (s : MovedSection ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)
      (generalizedFitting (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))))
    (F : BinaryField)
    (hnatural : IsLinearNatural (s.action.comp (generalizedFitting
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker))).subtype) F 2)
    (hseed : U ≤ normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hfit : generalizedFitting G = pCore 2 G) :
    GlaubermanNiles.InLocalClass (inclusion (show baumann (T : Subgroup G) ≤
      pResidual 2 G ⊔ baumann (T : Subgroup G) from le_sup_right)) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let A := generalizedFitting Y
  let := offenderSubgroup_normal α
  let := hqs
  let : IsSimpleGroup (A ⧸ center A) := hqs.simple
  let : Nontrivial A := Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (center A))
  obtain ⟨e⟩ := hnatural
  have hF := perfect_linear_two_field_large F e.groupEquiv
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [← pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hn : q.ker ≠ ⊤ := by
    intro he
    exact hJ (hker ▸ (he ▸ (le_top : elementaryAbelianMaxJ (T:Subgroup G) ≤ ⊤)))
  have hp := (minimalParabolic_reduced_image T hP q hq hcore hn).2
  have hff : IsFFModule α := by
    obtain hf | ⟨_,hff,_,_,_⟩ := lemma_B_2_7 U q hq hker T
    · exact (hJ ((elementaryAbelianMaxJ_sylow_le_top T).trans hf.1)).elim
    · exact hff
  have hL := (source_quasisimple_fitting_eq_residual (T.mapSurjective hq) hp Y
    (offender_generation (T.mapSurjective hq) hp α hff hcore).2 hqs).1
  have hX : A.map Y.subtype = (pResidual 2 G).map q := by
    rw [map_pResidual_of_surjective 2 q hq]
    exact hL
  let L := A.map Y.subtype
  let : L.Normal := by change (A.map Y.subtype).Normal; infer_instance
  let eg := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm.trans e.groupEquiv
  apply normal_layer_seed_localClass T hP U hU hJ q hq hker
    L eg hF (sourceMovedQuotientMap U q hq hker Y A s (pResidual 2 G) hX _ e)
    (sourceMovedQuotientMap_surjective U q hq hker Y A s (pResidual 2 G) hX _ e) ?_
    (sourceMovedQuotientMap_kernel U q hq hker Y A s (pResidual 2 G) hX _ e)
    hseed hfit
  intro g hg v
  let a := (A.equivMapOfInjective Y.subtype Y.subtype_injective).symm ⟨q g,hg⟩
  have ha : q g = (a:Y) := (congrArg Subtype.val
    ((A.equivMapOfInjective Y.subtype Y.subtype_injective).apply_symm_apply ⟨q g,hg⟩)).symm
  exact sourceMovedQuotientMap_conjugation U q hq hker Y A s (pResidual 2 G) hX _ e g a ha v

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterC.GlaubermanNiles
variable {G : Type u} [Group G] [Finite G]
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary
private theorem natural_left_localClass
    {T : Sylow 2 G} {L W D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hDL : D ≤ L) (hDc : Nat.card D = 3)
    (hn : D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hseed : W.subgroupOf (L ⊔ (T : Subgroup G)) ≤ normalClosure
      (omegaOneCenterAmbient ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))) :
        Set (L ⊔ (T : Subgroup G) : Subgroup G)))
    (hfit : generalizedFitting (L ⊔ (T : Subgroup G) : Subgroup G) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) :
    let M := L ⊔ (T : Subgroup G)
    let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
    InLocalClass (inclusion (show ChapterB.baumann (P : Subgroup M) ≤
      pResidual 2 M ⊔ ChapterB.baumann (P : Subgroup M) from le_sup_right)) := by
  classical
  let M := L ⊔ (T : Subgroup G)
  let U := W.subgroupOf M
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let := h.reduced_internal.normal
  let := h.reduced_internal.elementary
  have hSQ : IsSQTK KnownSimple.IsKnownSimple M := by
    have hMM : M ≤ normalizer (L : Set G) := sup_le L.le_normalizer h.sylow_normalizes
    exact (IsSQTK.equiv (subgroupOfEquivOfLe hMM)).mp
      ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (M.subgroupOf (normalizer (L : Set G))))
  have hns : ¬ Group.IsSolvable M := by
    intro hs
    let := hs
    exact Chapter1.mem_L_not_isSolvable h.maximal_local.1
      (Group.isSolvable_of_isSolvable_injective
        (inclusion_injective (show L ≤ M from le_sup_left)))
  have hSm : (S : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hjm : (elementaryAbelianMaxJ (S : Subgroup M)).map M.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective M.subtype M.subtype_injective,hSm]
  have hjS : ¬ elementaryAbelianMaxJ (S : Subgroup M) ≤ centralizer (U : Set M) := by
    intro hc
    apply hj
    rw [←hjm]
    rintro _ ⟨x,hx,rfl⟩ v hv
    exact congrArg M.subtype (hc hx ⟨v,h.reduced.1 hv⟩ hv)
  let C := centralizer (U : Set M)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  rcases ChapterE.ThompsonAction.source_nonsolvable_natural_factors
      hSQ S h.local_minimal_parabolic U h.reduced_internal hns hjS with
    ⟨hqs,c,hlin|hfive⟩ | ⟨d,_,_⟩
  · obtain ⟨F,hF⟩ := hlin
    exact ChapterC.RankOne.ChiProduct.SelectedRankOne.quasisimple_natural_localClass
      S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData F hF
      hseed hfit
  · obtain ⟨e⟩ := hfive
    have hf := ChapterE.ThompsonAction.quasisimple_five_source_marker
      S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData e
    have hf' : let V := ⁅U,pResidual 2 M⁆
      ∃ p : M →* Equiv.Perm (Fin 5), ∃ hp : Function.Surjective p,
        ∃ hk : p.ker = centralizer (V : Set M),
        ∃ f : Additive V →ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
          Function.Surjective f ∧
          (∀ g v, f (NormalElementaryQuotient.representation V p hp hk g v) =
            BinaryPermutation.coreRepresentation (Fin 5) g (f v)) ∧
          f.ker = fixedSpace (NormalElementaryQuotient.representation V p hp hk)
            ((pResidual 2 M).map p) := hf
    exact (h.cubic_not_normalizes_thompson_of_five_section hj (hDL.trans le_sup_left)
      hDc hf' hn).elim
  · have hrank : primeRank 3 M ≤ 1 := by
      rw [←ResidualCentralizerRank.primeRank_residual (by decide : Nat.Coprime 2 3)]
      let e : (pResidual 2 M) ≃* L :=
        (equivMapOfInjective (pResidual 2 M) M.subtype M.subtype_injective).trans
          (MulEquiv.subgroupCongr h.local_residual_eq)
      rw [primeRank_congr 3 e]
      exact Chapter4.Section03.RankOneUniqueness.odd_primeRank_le_one h.linear (by decide)
    let P : Sylow 3 M := Classical.choice inferInstance
    have hr : primeRank 3 (M ⧸ C) ≤ 1 :=
      P.primeRank_quotient_le_one (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hrank) C
    have hy := (primeRank_subgroup_le 3 (offenderSubgroup α)).trans hr
    have hd := d.two_le_three_rank
    change 2 ≤ primeRank 3 (offenderSubgroup α) at hd
    omega

/-- The actual left omega-span supplies the selected Baumann local class. -/
theorem LocalA7Configuration.left_baumann_localClass
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D) :
    let M := L ⊔ (T : Subgroup G)
    let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
    InLocalClass (inclusion (show ChapterB.baumann (P : Subgroup M) ≤
      pResidual 2 M ⊔ ChapterB.baumann (P : Subgroup M) from le_sup_right)) := by
  have hLC : ¬ L ≤ omegaCentralizer T := by
    intro hc
    have he := h.omega_fixed_eq_bot_of_centralizer_escape
      (a.omega_centralizer_escape h hH hgen c d)
    rw [inf_eq_left.mpr (le_centralizer_iff.mp hc)] at he
    have hh := (a.omega_four_geometry h hH hgen c d).2.1
    rw [he] at hh
    simp at hh
  have hs := h.omega_span_input hLC
  let M := L ⊔ (T : Subgroup G)
  let P := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  have hPm : (P : Subgroup M).map M.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le le_sup_right
  have hZm : (omegaOneCenterAmbient (P : Subgroup M)).map M.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective M.subtype M.subtype_injective,hPm]
  let V := normalClosure (omegaOneCenterAmbient (P : Subgroup M) : Set M)
  have hZV : omegaOneCenterAmbient (T : Subgroup G) ≤ V.map M.subtype := by
    rw [←hZm]
    exact map_mono le_normalClosure
  have hMn : M ≤ normalizer (V.map M.subtype : Set G) := by
    have hh := V.le_normalizer_map M.subtype
    rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
  have hseed : (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L).subgroupOf M ≤ V := by
    intro x hx
    have hh := conjugateSpanBy_le hZV (le_sup_left.trans hMn) hx
    exact (Subgroup.mem_map_iff_mem M.subtype_injective).mp hh
  have hf : generalizedFitting M = pCore 2 M :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T
        (h.qtke.evenCharacteristic T) ⟨h.maximal_local.1.2.2,fun _ hx =>
          (le_sup_right : (T : Subgroup G) ≤ M) hx⟩))
  have hn : D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    (le_sup_right.trans le_sup_left).trans
      (a.four_cubic_normalizes_thompson h hH hgen c d (a.four h hH hgen c d))
  exact natural_left_localClass hs (a.left_thompson_moves hs)
    (((d.cubic_le.trans inf_le_left).trans c.left_le).trans inf_le_left)
    d.cubic_card hn hseed hf


/-- The same uniform pair gives the literal left block or its second
characteristic subgroup normalized by LT. The first alternative is impossible. -/
theorem LocalA7Configuration.left_characteristic_or_block
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (P : CharacteristicPair (ChapterB.baumann (T : Subgroup G))) (hP : P.Universal.{u,u}) :
    L ⊔ (T : Subgroup G) ≤ normalizer
      (P.second.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∨
      ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) := by
  let M := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ M from le_sup_right)
  let E := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair T P M le_sup_right
  have hE := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair_universal
    T P hP M le_sup_right
  let B₀ := ChapterB.baumann (S : Subgroup M)
  let N := pResidual 2 M ⊔ B₀
  have hlocal := a.left_baumann_localClass h hH hgen c d
  have hR : pResidual 2 M = L.subgroupOf M := by
    apply map_injective M.subtype_injective
    rw [map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left)]
    exact h.local_residual_eq
  rcases hE N (inclusion (show B₀ ≤ N from le_sup_right)) hlocal with hc | hn | hb
  · exfalso
    apply ChapterC.RankOne.ChiProduct.FixedPair.firstSeed_ne_bot T P
    apply bot_unique
    intro z hz
    apply (h.omega_fixed_eq_bot_of_centralizer_escape
      (a.omega_centralizer_escape h hH hgen c d)).le
    refine ⟨hz.1,?_⟩
    have hm := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair_member_map
      T M (show (T : Subgroup G) ≤ M from le_sup_right) P.first
    obtain ⟨v,hv,hvz⟩ := hm.ge hz.2
    obtain ⟨b,hb,rfl⟩ := hv
    intro l hl
    let r : M := ⟨l,mem_sup_left hl⟩
    have hr : r ∈ pResidual 2 M := hR.symm ▸ hl
    let rN : N := ⟨r,mem_sup_left hr⟩
    have hh := mem_center_iff.mp (hc (mem_map_of_mem
      (inclusion (show B₀ ≤ N from le_sup_right)) hb)) rN
    have hh' := congrArg (M.subtype.comp N.subtype) hh
    change l * (b.val : G) = (b.val : G) * l at hh'
    change (b.val : G) = z at hvz
    rwa [hvz] at hh'
  · left
    let C := P.second.map (ChapterB.baumann (T : Subgroup G)).subtype
    let C' := E.second.map (inclusion (show B₀ ≤ N from le_sup_right))
    let := hn
    have hm : C'.map (M.subtype.comp N.subtype) = C := by
      rw [map_map]
      have hh := ChapterC.RankOne.ChiProduct.FixedPairSolvable.subtypePair_member_map
        T M (show (T : Subgroup G) ≤ M from le_sup_right) P.second
      rw [map_map] at hh
      exact hh
    have hN : N.map M.subtype ≤ normalizer (C : Set G) := by
      have hh := C'.le_normalizer_map (M.subtype.comp N.subtype)
      rw [normalizer_eq_top,←MonoidHom.range_eq_map,MonoidHom.range_comp,
        range_subtype,hm] at hh
      exact hh
    have hL : L ≤ normalizer (C : Set G) := by
      rw [←h.local_residual_eq]
      exact (map_mono le_sup_left).trans hN
    let := P.second_characteristic
    exact sup_le hL (((T : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_baumann (T : Subgroup G))).trans
        (normalizer_le_normalizer_characteristic_image _ P.second))
  · right
    rw [←hR]
    exact ChapterC.RankOne.ChiProduct.SelectedRankOne.chi_residual_of_selected_block S hb

/-- In the nonblock left case, the right residual must escape the same
second characteristic normalizer. This is the remaining right block premise. -/
theorem LocalA7Configuration.residual_escapes_second_of_left_nonblock
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (P : CharacteristicPair (ChapterB.baumann (T : Subgroup G))) (hP : P.Universal.{u,u})
    (hnb : ¬ ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G)))) :
    ¬ residual H ≤ normalizer
      (P.second.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) := by
  have hn := (a.left_characteristic_or_block h hH hgen c d P hP).resolve_right hnb
  intro hr
  let := P.second_characteristic
  have hC := h.common_normalized_twoGroup_eq_bot hH
    (P.second.map (ChapterB.baumann (T : Subgroup G)).subtype)
    (((T.isPGroup'.to_le (show ChapterB.baumann (T : Subgroup G) ≤ T from inf_le_left)).to_subgroup
      P.second).map (ChapterB.baumann (T : Subgroup G)).subtype)
    (le_sup_left.trans hn) (le_sup_right.trans hn) hr
  exact P.second_ne_bot ((P.second.map_eq_bot_iff_of_injective
    (ChapterB.baumann (T : Subgroup G)).subtype_injective).mp hC)


/-- The original nonblock left side yields a concrete nontrivial
characteristic subgroup, with its full ambient normalizer controlled by N_G(L). -/
theorem LocalA7Configuration.left_nonblock_characteristic_control
    {T : Sylow 2 G} {L W H A B Y X D K : Subgroup G} {n : ℕ}
    (a : LocalA7Configuration T L H X K)
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (d : LocalCartanWitness T H A Y X D)
    (hnb : ¬ ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G)))) :
    ∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic ∧ C ≠ ⊥ ∧
      L ⊔ (T : Subgroup G) ≤ normalizer
        (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
      ¬ residual H ≤ normalizer
        (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
      normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ≤
        normalizer (L : Set G) := by
  have ht : (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hz : W = ⊥ := bot_unique (h.reduced_le_sylow.trans_eq he)
    exact h.noncentral (by rw [hz,commutator_bot_left])
  obtain ⟨P,hP⟩ := ChapterC.RankOne.ChiProduct.SelectedRankOne.exists_baumann_universal_pair.{u,u}
    (T : Subgroup G) T.isPGroup' ht
  have hn := (a.left_characteristic_or_block h hH hgen c d P hP).resolve_right hnb
  have he := a.residual_escapes_second_of_left_nonblock h hH hgen c d P hP hnb
  refine ⟨P.second,P.second_characteristic,P.second_ne_bot,hn,he,?_⟩
  have hq := ((T.isPGroup'.to_le (show ChapterB.baumann (T : Subgroup G) ≤ T from inf_le_left)).to_subgroup
    P.second).map (ChapterB.baumann (T : Subgroup G)).subtype
  have hne : P.second.map (ChapterB.baumann (T : Subgroup G)).subtype ≠ ⊥ := by
    intro hh
    exact P.second_ne_bot ((P.second.map_eq_bot_iff_of_injective
      (ChapterB.baumann (T : Subgroup G)).subtype_injective).mp hh)
  exact normalizer_le_of_unique_maximalTwoLocal h.unique_local_join hq hne hn

/-- Apply the proved FF reduction and the uniform characteristic-pair
construction to the original noncentral source inputs. -/
theorem localCartan_noncentral_left_block_alternative
    {T : Sylow 2 G} {L W H A B Y X D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X D) (hXC : ¬ X ≤ omegaCentralizer T) :
    ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G))) ∨
      ∃ C : Subgroup (ChapterB.baumann (T : Subgroup G)), C.Characteristic ∧ C ≠ ⊥ ∧
        L ⊔ (T : Subgroup G) ≤ normalizer
          (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
        ¬ residual H ≤ normalizer
          (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ∧
        normalizer (C.map (ChapterB.baumann (T : Subgroup G)).subtype : Set G) ≤
          normalizer (L : Set G) := by
  obtain ⟨K,a⟩ := localCartan_ffReduction T L W n h H hH hgen A B c Y hY X D d hXC
  by_cases hb : ChapterC.IsChiBlockIn (L.subgroupOf (L ⊔ (T : Subgroup G)))
  · exact Or.inl hb
  · exact Or.inr (a.left_nonblock_characteristic_control h hH hgen c d hb)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
