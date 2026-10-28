module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalFFSelection
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarE23
import all CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalThompson

/-!
# Selecting the natural quotient in the Thompson-moving branch of 6.1.4

The actual FF classifier has a single linear row or a symmetric-five row;
the PSL₂ quotient excludes paired factors. In the five row the completed
class-sum construction identifies the whole original moved module, not
merely its central quotient. Its marking therefore contradicts the literal
A₅-module exclusion in Hypothesis 6.1.1. The natural quotient is consequently
forced whenever the original Thompson subgroup moves the reduced module.

The stationary Thompson branch still requires the weak-closure arguments
for doubled-natural and orthogonal modules on printed pp.664–666.
Source: Aschbacher--Smith, 5.1.2 and Remark 6.1.2, pp.630,663–664.
-/
set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source
namespace RankOneGeneric
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

/-- Actual Thompson movement selects a natural fixed quotient or the full
A₅ model on the literal moved layer. Both actor markings are retained. -/
theorem Input.natural_quotient_or_a5_of_thompson_moves
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    IsNaturalFixedQuotient L W n ∨ IsConjugationModel L (layer L W) a5Module := by
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
    obtain ⟨p,hp,hpk,f,he⟩ :=
      ChapterE.ThompsonAction.quasisimple_five_source_natural_module
        S h.local_minimal_parabolic U h.reduced_internal hjS q hq hk hqs c.sectionData e
    let V := ⁅U,pResidual 2 M⁆
    have hcore : p.ker = pCore 2 M := hpk.trans
      ((h.reduced_internal.centralizer_moved_eq U).trans h.reduced_centralizer_core)
    let B := L.subgroupOf M
    let eb : B ≃* L := subgroupOfEquivOfLe (show L ≤ M from le_sup_left)
    let : B.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer h.sylow_normalizes)
    have hR : pResidual 2 M = B := by
      apply map_injective M.subtype_injective
      rw [map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left)]
      exact h.local_residual_eq
    have hBp : B.map p = alternatingGroup (Fin 5) := by
      rw [←hR, map_pResidual_of_surjective 2 p hp, Equiv.Perm.twoResidual_eq_alternating]
    have hkerB : (p.subgroupMap B).ker = pCore 2 B := by
      rw [Subgroup.ker_subgroupMap,hcore,pCore_eq_comap_of_normal 2 B]
      rfl
    let eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5) :=
      ((QuotientGroup.quotientMulEquivOfEq hkerB.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective (p.subgroupMap B)
          (p.subgroupMap_surjective B))).trans (MulEquiv.subgroupCongr hBp)
    let eL : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5) :=
      (QuotientGroup.congr (pCore 2 B) (pCore 2 L) eb (pCore_map_iso 2 eb)).symm.trans eB
    let vG : V ≃* layer L W :=
      (equivMapOfInjective V M.subtype M.subtype_injective).trans
        (MulEquiv.subgroupCongr h.local_moved_map)
    let c5 := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
    let fv : layer L W ≃* Multiplicative (BinaryPermutation.natural (Fin 5)) :=
      vG.symm.trans (f.toAddEquiv.toMultiplicative.trans c5.toAddEquiv.toMultiplicative)
    refine Or.inr ⟨eL,fv,?_⟩
    intro l v
    let lM : M := ⟨l,mem_sup_left l.property⟩
    have hactor : (eL (QuotientGroup.mk' (pCore 2 L) l)).val = p lM := by
      rfl
    let u : Additive V := Additive.ofMul (vG.symm v)
    have hact := he (p lM) u
    have hh := congrArg c5 hact
    rw [BinaryPermutation.coreEquivNatural_equivariant] at hh
    have hnormal : L ≤ normalizer (layer L W : Set G) := normalizer_commutator_ge_right W L
    let vl : layer L W := (layer L W).normalizerMonoidHom ⟨l,hnormal l.property⟩ v
    have hcoords : fv vl = Multiplicative.ofAdd
        (a5Module (eL (QuotientGroup.mk' (pCore 2 L) l)) (fv v).toAdd) := by
      apply Multiplicative.toAdd.injective
      change c5 (f (Additive.ofMul (vG.symm vl))) =
        BinaryPermutation.naturalRepresentation (Fin 5)
          (eL (QuotientGroup.mk' (pCore 2 L) l)).val (c5 (f u))
      rw [hactor]
      have hu : Additive.ofMul (vG.symm vl) =
          NormalElementaryQuotient.representation V p hp hpk (p lM) u := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change ((vG.symm vl : V) : M) =
          ((NormalElementaryQuotient.representation V p hp hpk (p lM) u).toMul : M)
        rw [NormalElementaryQuotient.representation_apply]
        apply Subtype.ext
        have hvG (w : layer L W) : ((vG.symm w : V) : G) = (w : G) :=
          congrArg Subtype.val (vG.apply_symm_apply w)
        change ((vG.symm vl : V) : G) =
          (l:G) * ((vG.symm v : V) : G) * (l:G)⁻¹
        rw [hvG, hvG]
        rfl
      rw [hu]
      exact hh
    have hf := congrArg fv.symm hcoords
    rw [fv.symm_apply_apply] at hf
    exact (congrArg Subtype.val hf).symm
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

end RankOneGeneric

namespace Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The original A₅ exclusion removes the five row of the actual FF classifier. -/
theorem natural_fixed_quotient_of_thompson_moves
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    IsNaturalFixedQuotient L V n := by
  rcases (h.rankOneInput hout).natural_quotient_or_a5_of_thompson_moves hj with hm | hm
  · exact hm
  · exact (h.not_a5 (Or.inl hm)).elim

/-- The same moving hypothesis gives the literal moved-layer quotient of 6.1.4. -/
theorem moved_natural_fixed_quotient_of_thompson_moves
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hj : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G)) :
    IsNaturalFixedQuotient L (layer L V) n := by
  let hi := h.rankOneInput hout
  have hj' : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (layer L V : Set G) := by
    intro hc
    apply hj
    exact (le_inf (sSup_le fun _ he => he.1) hc).trans
      (hi.sylow_centralizer_commutator_eq.le.trans inf_le_right)
  rcases hi.commutator_input.natural_quotient_or_a5_of_thompson_moves hj' with hm | hm
  · exact hm
  · have hid : layer L (layer L V) = layer L V := by
      let := h.V_mem.2.1
      exact commutator_isPPerfect_idempotent L V h.local_mem.2.2.1
        (IsElementaryAbelian.isPGroup 2 V) (le_sup_left.trans (reduced_normalizes h.V_mem))
    exact (h.not_a5 (Or.inl (hid ▸ hm))).elim

/-- Every remaining failure of the natural quotient is Thompson stationary. -/
theorem thompson_centralizes_of_not_natural_fixed_quotient
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : ¬ IsNaturalFixedQuotient L V n) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  by_contra hj
  exact hm (h.natural_fixed_quotient_of_thompson_moves hout hj)

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
