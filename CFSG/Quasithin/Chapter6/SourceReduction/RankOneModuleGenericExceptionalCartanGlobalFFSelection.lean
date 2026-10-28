module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalLayer
public import Theory.SpecificGroups.SL2.FieldCardinality
public import Theory.GroupTheory.CharacteristicTwoCenterJoin
-- Continue the internal quotient-kernel argument without changing its visibility.
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# Selecting the Cartan module row from actual Thompson movement

Apply the genuine FF classifier to the original reduced module. The
three-rank bound of L/O₂(L) excludes paired factors. In the linear row,
the offender group equals the image of the original residual. Its
quotient marking therefore yields an isomorphism from the literal
L/O₂(L) to SL₂(F). Comparing group orders recovers |F| = 2ⁿ.

The coefficient map on W has exactly C_W(L) as kernel: the whole FF
fixed quotient is transported through the original inclusion of L in LT.
This proves the natural quotient alternative without assuming its model.
The symmetric-five row gives n = 2 and Borel fixation of omega whenever
W contains the original omega-center.

For the actual L-span of omega, Thompson movement itself proves its
noncentrality, so B.2.14 supplies the reselected reduced input. The natural
row then uses the completed kernel-removal and degree argument. In the
five row, zero core of AH makes Z(H) trivial. Thus both moving rows give
small Cartan generation and the literal Chapter12 prime-pair application.
The stationary-Thompson rows and later zero-core recognition remain open.

Source: Aschbacher--Smith 5.1.2, 5.1.6(2--3), printed pp.630,632,
using B.4.2 and E.2.3, and 5.2.2, p.647 (`refs/quasithin.pdf`).
-/
set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
attribute [local instance] ChapterB.RankOneBaumann.semilinear_moved_elementary

omit [Finite G] in
private theorem natural_fixed_quotient_of_binaryField
    {L W : Subgroup G} {n : ℕ} (F : BinaryField)
    (hcard : Nat.card F.Carrier = 2^n)
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F.Carrier))
    (m : ConjugationQuotientModel L W (linearNatural F 2))
    (hm : m.actor = e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))) :
    IsNaturalFixedQuotient L W n := by
  rcases F with @⟨F,hF,hfinite,hchar,halg,d,hd,hFd⟩
  have he : halg = ZMod.algebra F 2 := Subsingleton.elim _ _
  cases he
  exact ⟨F,hF,hfinite,hchar,hcard,e,m,hm⟩

/-- Actual Thompson movement selects a natural fixed quotient on the whole
original reduced module or the degree-two symmetric-five Borel alternative. -/
theorem Input.natural_quotient_or_five_of_thompson_moves
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    IsNaturalFixedQuotient L W n ∨
      (n = 2 ∧ (omegaOneCenterAmbient (T : Subgroup G) ≤ W →
        localBorel T L ≤ omegaCentralizer T)) := by
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
    have hR : pResidual 2 M = L.subgroupOf M := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left)]
      exact h.local_residual_eq
    let r : L →* N :=
      { toFun := fun l => ⟨q ⟨l,mem_sup_left l.property⟩, hres ▸
          mem_map_of_mem q (hR.symm ▸ l.property)⟩
        map_one' := Subtype.ext q.map_one
        map_mul' := fun a b => Subtype.ext (q.map_mul ⟨a,mem_sup_left a.property⟩ ⟨b,mem_sup_left b.property⟩) }
    have hrs : Function.Surjective r := by
      intro x
      have hx : x.val ∈ (pResidual 2 M).map q := hres.symm ▸ x.property
      obtain ⟨l,hl,he⟩ := hx
      refine ⟨⟨l,hR.le hl⟩,Subtype.ext he⟩
    let B := L.subgroupOf M
    let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ M from le_sup_left)
    let : B.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer h.sylow_normalizes)
    have hrk : r.ker = pCore 2 L := by
      ext l
      simp only [MonoidHom.mem_ker,Subtype.ext_iff]
      change q ⟨l,mem_sup_left l.property⟩ = 1 ↔ l ∈ pCore 2 L
      change (⟨l,mem_sup_left l.property⟩ : M) ∈ q.ker ↔ _
      have hkcore : q.ker = pCore 2 M := hk.trans h.reduced_centralizer_core
      rw [hkcore,←pCore_map_iso 2 eb]
      rw [mem_map_equiv]
      change (⟨l,mem_sup_left l.property⟩ : M) ∈ pCore 2 M ↔ eb.symm l ∈ pCore 2 B
      rw [pCore_eq_comap_of_normal 2 B]
      rfl
    let eR : (L ⧸ pCore 2 L) ≃* N :=
      (QuotientGroup.quotientMulEquivOfEq hrk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective r hrs)
    obtain ⟨e⟩ := hall.2.2.2
    let eL := eR.trans (eN.symm.trans e.groupEquiv)
    have hfield : Nat.card F.Carrier = 2^n := by
      obtain ⟨E,_,_,hE,⟨eE⟩⟩ := h.linear
      let : Fintype E := Fintype.ofFinite E
      let : CharP E 2 := charP_of_card_eq_prime_pow (p:=2) (f:=n) (by
        simpa only [Nat.card_eq_fintype_card] using hE)
      exact (Matrix.SL2.field_card_eq_of_equiv
        (eL.symm.trans (eE.trans (Theory.PSL2.sl2QuotientEquiv E).symm))).trans hE
    let σ := α.comp N.subtype
    let C₀ := fixedSpace σ (generalizedFitting N)
    let wU : W ≃* U := (subgroupOfEquivOfLe h.reduced.1).symm
    let f : W →* Multiplicative (Fin 2 → F.Carrier) :=
      { toFun := fun w => Multiplicative.ofAdd (e.linearEquiv (C₀.mkQ (Additive.ofMul (wU w))))
        map_one' := by
          change e.linearEquiv (C₀.mkQ (Additive.ofMul (wU 1))) = 0
          rw [wU.map_one]
          change e.linearEquiv (C₀.mkQ 0) = 0
          rw [map_zero,map_zero]
        map_mul' := fun a b => by
          change e.linearEquiv (C₀.mkQ (Additive.ofMul (wU (a*b)))) =
            e.linearEquiv (C₀.mkQ (Additive.ofMul (wU a))) +
              e.linearEquiv (C₀.mkQ (Additive.ofMul (wU b)))
          rw [wU.map_mul]
          change e.linearEquiv (C₀.mkQ (Additive.ofMul (wU a) + Additive.ofMul (wU b))) = _
          rw [map_add,map_add] }
    have hfs : Function.Surjective f := by
      intro v
      obtain ⟨a,ha⟩ := C₀.mkQ_surjective (e.linearEquiv.symm v.toAdd)
      refine ⟨wU.symm a.toMul,?_⟩
      change e.linearEquiv (C₀.mkQ (Additive.ofMul (wU (wU.symm a.toMul)))) = v.toAdd
      rw [wU.apply_symm_apply]
      exact (congrArg e.linearEquiv ha).trans (e.linearEquiv.apply_symm_apply _)
    have hfker : f.ker = (centralizer (L : Set G)).subgroupOf W := by
      ext w
      change e.linearEquiv (C₀.mkQ (Additive.ofMul (wU w))) = 0 ↔ _
      rw [e.linearEquiv.map_eq_zero_iff]
      change (Submodule.Quotient.mk (Additive.ofMul (wU w)) : Additive U ⧸ C₀) = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      have heq : C₀ = fixedSpace α ((pResidual 2 M).map q) := by
        rw [hres]
        ext v
        constructor
        · intro hv x
          exact hv (eN.symm x)
        · intro hv x
          exact hv x.val
      rw [heq,NormalElementaryQuotient.mem_fixedSpace_image]
      constructor
      · intro hw l hl
        let lM : M := ⟨l,mem_sup_left hl⟩
        have hh := congrArg M.subtype (hw lM (hR.symm ▸ hl))
        exact hh
      · intro hw l hl
        apply M.subtype_injective
        exact hw l (hR.le hl)
    let hn : L ≤ normalizer (W : Set G) := le_sup_left.trans (reduced_normalizes h.reduced)
    let m : ConjugationQuotientModel L W (linearNatural F 2) :=
      { normalizes := hn
        actor := eL.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
        quotient := f
        surjective := hfs
        kernel := hfker
        equivariant := by
          intro l w
          let a : generalizedFitting N := eN.symm (r l)
          have ha : (a.val : M ⧸ C) = q ⟨l,mem_sup_left l.property⟩ := by
            have hh := congrArg (fun x : N => (x : M ⧸ C)) (eN.apply_symm_apply (r l))
            exact hh
          change e.linearEquiv (C₀.mkQ (Additive.ofMul
            (wU (W.normalizerMonoidHom ⟨l,hn l.property⟩ w)))) =
              linearNatural F 2 (e.groupEquiv a) (e.linearEquiv (C₀.mkQ (Additive.ofMul (wU w))))
          rw [←e.intertwines]
          change e.linearEquiv (C₀.mkQ _) = e.linearEquiv (C₀.mkQ (α a.val.val _))
          congr 2
          rw [ha]
          apply Additive.toMul.injective
          apply U.subtype_injective
          exact (NormalElementaryQuotient.representation_apply U q hq hk
            ⟨l,mem_sup_left l.property⟩ (Additive.ofMul (wU w))).symm }
    exact Or.inl (natural_fixed_quotient_of_binaryField F hfield eL m rfl)
  · obtain ⟨e⟩ := hfive
    have hmarker := ChapterE.ThompsonAction.quasisimple_five_source_marker
        S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData e
    have hfix : omegaOneCenterAmbient (T : Subgroup G) ≤ W →
        localBorel T L ≤ omegaCentralizer T :=
      fun hZ => h.borel_fixes_omega_of_five_section hZ hmarker
    obtain ⟨p,hp,hpk,f,hf,he,hfk⟩ := hmarker
    have hcore : p.ker = pCore 2 M := hpk.trans
      ((h.reduced_internal.centralizer_moved_eq U).trans h.reduced_centralizer_core)
    exact Or.inr ⟨(h.degree_two_of_symmetric_five p hp hcore).1,
      hfix⟩
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

/-- Source 5.1.6 in the Thompson-moving omega-span branch. The natural
quotient and symmetric-five alternatives are selected, rather than assumed. -/
theorem Input.cartan_thompson_moving_omega_alternatives
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hz : (A ⊔ H).pCoreIn 2 = ⊥)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G)) :
    (n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n ∧
      ((H ≤ omegaCentralizer T ∧
        IsNaturalModule L (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n) ∨
       (n = 2 ∧ A ≤ omegaCentralizer T ∧ center H = ⊥)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have hLC : ¬ L ≤ omegaCentralizer T := by
    intro hc
    have hu : conjugateSpanBy Z L = Z := le_antisymm
      (conjugateSpanBy_le le_rfl (hc.trans (Subgroup.centralizer_le_normalizer _)))
      (le_conjugateSpanBy Z L)
    apply hj
    rw [hu]
    exact (sSup_le fun _ he => he.1).trans sylow_le_omegaCentralizer
  let hs := h.omega_span_input hLC
  rcases hs.natural_quotient_or_five_of_thompson_moves hj with hm | ⟨hn,hb⟩
  · obtain ⟨hdegree,hsmall⟩ := h.natural_quotient_cartan_degree_and_smallGeneration hH hgen c hm hz
    have hHC := h.natural_quotient_cartan_omega_centralizes_all_degrees hH hgen c hm hz
    have hf := hs.reduced_fixed_eq_bot_of_outside_centralizes hH hHC
    exact ⟨hdegree,hsmall,Or.inl ⟨hHC,hm.natural_of_fixed_eq_bot hf⟩⟩
  · have hA := c.left_le.trans (hb (le_conjugateSpanBy Z L))
    have hcenter : center H = ⊥ := center_eq_bot_of_join_core_eq_bot T H A hH.1.1.2
      (Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.qtke.evenCharacteristic T) hH.1.1))
      hA (by simpa only [sup_comm] using hz)
    exact ⟨Or.inl hn,h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inl hn),
      Or.inr ⟨hn,hA,hcenter⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
