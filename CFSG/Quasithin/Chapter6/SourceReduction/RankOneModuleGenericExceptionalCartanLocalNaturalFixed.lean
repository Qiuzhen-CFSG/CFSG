module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson
public import Theory.SpecificGroups.SL2.CubicFixedVectors

/-!
# Cubic fixed spaces in the original natural-left action

The genuine FF alternatives and the original Thompson normalizer exclude
the symmetric-five row. In the remaining row the entire quotient by its
fixed space is natural, and the literal residual image is the offender
group. The original cubic injects through the two-core. Its order-three
matrix fixes only zero, so its fixed subgroup in W is exactly C_W(L).
No splitting of W or module coordinates are assumed.

Source: Aschbacher–Smith 5.1.13, printed p.637, using 5.1.2 and B.4.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

private theorem Input.natural_reduced_centralizer_core
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    centralizer (W.subgroupOf (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
  let M := L ⊔ (T : Subgroup G)
  let B := L.subgroupOf M
  let U := W.subgroupOf M
  have hr : IsPReduced 2 U := h.reduced_internal
  let := hr.normal
  let : B.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer h.sylow_normalizes)
  let e := QuotientGroup.congr (pCore 2 B) (pCore 2 L)
    (subgroupOfEquivOfLe (show L ≤ M from le_sup_left))
    (pCore_map_iso 2 (subgroupOfEquivOfLe (show L ≤ M from le_sup_left)))
  let := h.quotient_quasisimple
  let : IsQuasisimple (B ⧸ pCore 2 B) := IsQuasisimple.of_mulEquiv e.symm
  have hz : center (B ⧸ pCore 2 B) = ⊥ := by
    apply bot_unique
    intro b hb
    have hh : e b ∈ center (L ⧸ pCore 2 L) := MulEquivClass.apply_mem_center e hb
    rw [h.quotient_center_eq_bot] at hh
    exact e.injective (by simpa only [mem_bot,map_one] using hh)
  have hm : ⁅U,B⁆ ≠ ⊥ := by
    intro hh
    apply h.noncentral
    have he := congrArg (map M.subtype) hh
    have hu : U.map M.subtype = W := map_subgroupOf_eq_of_le h.reduced.1
    have hb : B.map M.subtype = L := map_subgroupOf_eq_of_le le_sup_left
    simpa only [map_commutator,hu,hb,Subgroup.map_bot] using he
  apply reduced_quasisimple_centralizer_eq_pCore U B hr hz hm
  apply isPGroup_quotient_of_sup_eq_top B ((T : Subgroup G).subgroupOf M) T.isPGroup'.comap_subtype
  rw [←subgroupOf_sup (show L ≤ M from le_sup_left) (show (T : Subgroup G) ≤ M from le_sup_right)]
  exact subgroupOf_self M

/-- A cubic in the original left component fixes precisely its fixed kernel
when it normalizes the original Thompson subgroup. -/
theorem Input.cubic_fixed_eq_of_normalizes_thompson
    {T : Sylow 2 G} {L W D : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hDL : D ≤ L) (hDc : Nat.card D = 3)
    (hn : D ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    W ⊓ centralizer (D : Set G) = W ⊓ centralizer (L : Set G) := by
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
    have hall := ChapterE.ThompsonAction.quasisimple_linear_whole_source
      S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData F hF
    let N := offenderSubgroup α
    let eN : generalizedFitting N ≃* N :=
      (MulEquiv.subgroupCongr hall.2.1).trans Subgroup.topEquiv
    let := hqs
    let : Group.IsPerfect N := Group.IsPerfect.ofSurjective (f := eN.toMonoidHom) eN.surjective
    have hres : (pResidual 2 M).map q = N := by
      apply le_antisymm
      · change (pResidual 2 M).map q ≤ offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
        rw [←hall.1]
        exact map_mono (ChapterE.ThompsonAction.residual_le_thompson S
          h.local_minimal_parabolic U h.reduced_internal hjS).1
      · rw [map_pResidual_of_surjective 2 q hq]
        have hh := map_pResidual_le 2 N.subtype
        rwa [pResidual_eq_top_of_isPerfect 2,←MonoidHom.range_eq_map,range_subtype] at hh
    have hD : D ≤ M := hDL.trans le_sup_left
    let E := D.subgroupOf M
    have hEc : Nat.card E = 3 := (Nat.card_congr (subgroupOfEquivOfLe hD).toEquiv).trans hDc
    have hdis : Disjoint E q.ker :=
      (IsPGroup.of_card (p := 3) (n := 1) hEc).disjoint_of_coprime
        ((hk.trans h.natural_reduced_centralizer_core).symm ▸ pCore_isPGroup) (by decide)
    have hqi : Function.Injective (q.comp E.subtype) := by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      apply bot_unique
      intro x hx
      exact Subtype.ext (mem_bot.mp (hdis.le_bot ⟨x.property,hx⟩))
    obtain ⟨d,hd⟩ := exists_prime_orderOf_dvd_card' (G := E) 3 (by rw [hEc])
    have hdN : q d.val ∈ N := by
      rw [←hres]
      have hR : pResidual 2 M = L.subgroupOf M := by
        apply map_injective M.subtype_injective
        rw [map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left)]
        exact h.local_residual_eq
      exact mem_map_of_mem q (hR.symm ▸ hDL d.property)
    let dN : N := ⟨q d.val,hdN⟩
    let dA : generalizedFitting N := eN.symm dN
    have hdA : orderOf dA = 3 := by
      rw [←eN.orderOf_eq dA,eN.apply_symm_apply]
      rw [←Subgroup.orderOf_coe dN]
      exact (orderOf_injective (q.comp E.subtype) hqi d).trans hd
    obtain ⟨e⟩ := hall.2.2.2
    apply le_antisymm ?_ (inf_le_inf_left W (centralizer_le hDL))
    intro w hw
    let v : Additive U := Additive.ofMul ⟨⟨w,h.reduced.1 hw.1⟩,hw.1⟩
    let σ := α.comp N.subtype
    let C := fixedSpace σ (generalizedFitting N)
    have hvd : σ dA.val v = v := by
      change α (q d.val) v = v
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change ((NormalElementaryQuotient.representation U q hq hk (q d.val) v).toMul : G) = w
      rw [NormalElementaryQuotient.representation_apply]
      change (d.val : G) * w * (d.val : G)⁻¹ = w
      rw [hw.2 d.val d.property,mul_inv_cancel_right]
    have hz : e.linearEquiv (C.mkQ v) = 0 := by
      apply Matrix.SL2.cubic_fixed_eq_zero (e.groupEquiv dA)
        ((e.groupEquiv.orderOf_eq dA).trans hdA)
      change ChapterB.QuasisimpleSource.linearNatural F 2 (e.groupEquiv dA)
        (e.linearEquiv (C.mkQ v)) = e.linearEquiv (C.mkQ v)
      rw [←e.intertwines]
      change e.linearEquiv (C.mkQ (σ dA.val v)) = e.linearEquiv (C.mkQ v)
      rw [hvd]
    have hvC : v ∈ C := (Submodule.Quotient.mk_eq_zero C).mp
      (e.linearEquiv.injective (hz.trans e.linearEquiv.map_zero.symm))
    have hvR : v ∈ fixedSpace α ((pResidual 2 M).map q) := by
      rw [hres]
      intro x
      exact hvC (eN.symm x)
    have hwR := (NormalElementaryQuotient.mem_fixedSpace_image U q hq hk (pResidual 2 M) v).mp hvR
    refine ⟨hw.1,?_⟩
    intro l hl
    obtain ⟨r,hr,hrl⟩ := h.local_residual_eq.ge hl
    have hh := congrArg M.subtype (hwR r hr)
    change (r:G)*w = w*(r:G) at hh
    change (r : G) = l at hrl
    rwa [hrl] at hh
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


end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
