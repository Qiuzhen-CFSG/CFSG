module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore
public import CFSG.Quasithin.ChapterA.Section01.RankActions.SourceActions
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.Frattini.OmegaProducts


/-!
# From quasisimple component actions to the source Frattini action

For a normal subgroup Y of a strongly quasithin local group H, pass to
H/O₂(H). The hypothesis Φ(P)≤O₂(H) makes the image of P elementary;
A.1.26 makes it centralize the odd core. Ordinary components of the image
of Y lift through the two-core quotient to C-components whose intrinsic
two-core quotients are quasisimple. Fixing just those components therefore
makes P centralize the layer. A.1.9 detects its whole action on Y/O₂(Y).

The original stronger APIs requiring all C-component actions are preserved.
The Geometry consumer constructs the relative normality and literal quotient
transports. `FieldDetection.Frattini` discharges the required quasisimple
actions for both field parities; nilpotent-Fitting C-components need not be
excluded for 11.5.6(4).
Source: Aschbacher--Smith 11.5.6(4), printed p.781; A.1.9 and A.1.26.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions

private theorem odd_twoPerfect {A : Type*} [Group A] [Finite A]
    (hodd : Odd (Nat.card A)) : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have ho : Odd (Nat.card (A ⧸ N)) := hodd.of_dvd_nat N.index_dvd_card
  have hc : Nat.card (A ⧸ N) = 1 := hp.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat
  exact N.index_eq_one.mp hc

private theorem elementary_image {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hA : IsPGroup 2 A) (hphi : frattini A ≤ f.ker) :
    IsElementaryAbelian 2 f.range := by
  let : Fact (IsPGroup 2 A) := ⟨hA⟩
  let : IsElementaryAbelian 2 (A ⧸ frattini A) := isElementaryAbelian_quotient_frattini
  let g : A ⧸ frattini A →* f.range :=
    QuotientGroup.lift (frattini A) f.rangeRestrict (by
      intro a ha
      exact Subtype.ext (hphi ha))
  apply IsElementaryAbelian.of_surjective g
  intro b
  obtain ⟨a, rfl⟩ := f.rangeRestrict_surjective b
  exact ⟨QuotientGroup.mk' (frattini A) a, rfl⟩

/-- Only C-components whose two-core quotients are quasisimple are needed
for the Frattini action. Ordinary components of the quotient lift to exactly
these C-components; the Fitting action follows independently from A.1.26. -/
theorem frattini_action_of_quasisimple_components {H : Type*} [Group H] [Finite H]
    (hsqt : IsStronglyQuasithin H) (X P Y : Subgroup H) [Y.Normal]
    (hX : Odd (Nat.card X)) (hP : IsPGroup 2 P) (hPX : P = ⁅P, X⁆)
    (hphi : (frattini P).map P.subtype ≤ pCore 2 H)
    (hcomponents : ∀ I : Subgroup Y, I.IsCComponent → IsQuasisimple (I ⧸ pCore 2 I) →
      ⁅I.map Y.subtype, X⁆ ≤ pCore 2 H) :
    ⁅P, Y⁆ ≤ Y.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let Xb := X.map q
  let Pb := P.map q
  let Yb := Y.map q
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : Yb.Normal := Subgroup.Normal.map inferInstance q hq
  have hcore : pCore 2 (H ⧸ pCore 2 H) = ⊥ := pCore_quotient_pCore_eq_bot 2
  have hcoreY : pCore 2 Yb = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : Yb.Normal).isSubnormal, hcore]
    exact Yb.subtype.ker_eq_bot_iff.mpr Yb.subtype_injective
  have hPb : IsPGroup 2 Pb := hP.map q
  have hXP : Pb = ⁅Pb, Xb⁆ := by
    change P.map q = ⁅P.map q, X.map q⁆
    rw [← map_commutator, ← hPX]
  let : IsElementaryAbelian 2 Pb := by
    have hr := elementary_image (q.comp P.subtype) hP (by
      intro a ha
      exact (QuotientGroup.eq_one_iff _).mpr (hphi (mem_map_of_mem P.subtype ha)))
    have he : (q.comp P.subtype).range = Pb := by
      rw [MonoidHom.range_comp, range_subtype]
    exact he ▸ hr
  have hodd : Odd (Nat.card Xb) := hX.of_dvd_nat (card_map_dvd X q)
  have hsqtb : IsStronglyQuasithin (H ⧸ pCore 2 H) := by
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans (hsqt p hp ho)
  have hoddFix : Pb ≤ centralizer (pPrimeCore 2 (H ⧸ pCore 2 H) : Set _) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (ChapterA.lemma_A_1_26_1_of_stronglyQuasithin hsqtb Xb Pb
        (odd_twoPerfect hodd) hXP.symm)
  have hfit : (fittingSubgroup Yb).map Yb.subtype ≤
      pPrimeCore 2 (H ⧸ pCore 2 H) := by
    apply le_trans _ (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore)
    apply le_sSup
    exact ⟨fittingSubgroupOf_normal Yb inferInstance, fittingSubgroupOf_isNilpotent Yb⟩
  have hfitFix : Pb ≤ centralizer ((fittingSubgroup Yb).map Yb.subtype : Set _) :=
    hoddFix.trans (centralizer_le hfit)
  let f : Y →* Yb := q.subgroupMap Y
  have hf : Function.Surjective f := q.subgroupMap_surjective Y
  have hk : f.ker = pCore 2 Y := by
    rw [ker_subgroupMap, QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 (inferInstance : Y.Normal).isSubnormal).symm
  let : Group.IsNilpotent (pCore 2 Y) := pCore_isPGroup.isNilpotent
  let e : (Y ⧸ pCore 2 Y) ≃* Yb :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have he : e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y)) = f := by
    ext y
    rfl
  have hlayer : (componentLayer Yb).map Yb.subtype ≤ centralizer (Xb : Set _) := by
    apply map_le_iff_le_comap.mpr
    apply sSup_le
    intro J hJ
    let : IsQuasisimple J := hJ.2
    obtain ⟨K,hK,hKq⟩ := (hJ.isCComponent.map_equiv e.symm).exists_map_quotient_eq (pCore 2 Y)
    have hKf : K.map f = J := by
      rw [← he, ← map_map, hKq, map_map]
      have hi : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Yb := by
        apply MonoidHom.ext
        intro x
        exact e.apply_symm_apply x
      rw [hi, map_id]
    let eK : (K ⧸ pCore 2 K) ≃* J :=
      (cComponentTwoCoreQuotientEquiv hK).trans
        ((e.subgroupMap (K.map (QuotientGroup.mk' (pCore 2 Y)))).trans
          (MulEquiv.subgroupCongr (by
            rw [map_map]
            change K.map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 Y))) = J
            rw [he, hKf])))
    have hKsimple : IsQuasisimple (K ⧸ pCore 2 K) :=
      IsQuasisimple.of_mulEquiv eK.symm
    have hfix : ⁅J.map Yb.subtype, Xb⁆ = ⊥ := by
      rw [← hKf, map_map]
      change ⁅K.map (q.comp Y.subtype), X.map q⁆ = ⊥
      rw [← map_map, ← map_commutator]
      apply (Subgroup.map_eq_bot_iff _).mpr
      simpa only [q, QuotientGroup.ker_mk'] using hcomponents K hK hKsimple
    exact map_le_iff_le_comap.mp (commutator_eq_bot_iff_le_centralizer.mp hfix)
  let C := centralizer ((componentLayer Yb).map Yb.subtype : Set (H ⧸ pCore 2 H))
  let : ((componentLayer Yb).map Yb.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  let : C.Normal := inferInstance
  have hXC : Xb ≤ C := le_centralizer_iff.mp hlayer
  have hPC : Pb ≤ C := by
    rw [hXP]
    exact (commutator_mono le_rfl hXC).trans (commutator_le_right _ _)
  have hstar : Pb ≤ centralizer ((generalizedFitting Yb).map Yb.subtype : Set _) := by
    apply le_centralizer_iff.mpr
    rw [generalizedFitting, Subgroup.map_sup]
    exact sup_le (le_centralizer_iff.mp hfitFix)
      (le_centralizer_iff.mp hPC)
  have hfix : ⁅Pb, Yb⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (ChapterA.lemma_A_1_9 2 Pb Yb hPb (by rw [normalizer_eq_top]; exact le_top) hcoreY hstar)
  have hcomm : ⁅P, Y⁆ ≤ pCore 2 H := by
    rw [← map_commutator] at hfix
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hfix
  have hle : ⁅P, Y⁆ ≤ Y := commutator_le_right _ _
  rintro g hg
  exact ⟨⟨g, hle hg⟩, (pCore_subnormal_eq_comap 2
    (inferInstance : Y.Normal).isSubnormal).symm ▸ hcomm hg, rfl⟩


/-- The original stronger component-action criterion, retained unchanged. -/
theorem frattini_action_of_components {H : Type*} [Group H] [Finite H]
    (hsqt : IsStronglyQuasithin H) (X P Y : Subgroup H) [Y.Normal]
    (hX : Odd (Nat.card X)) (hP : IsPGroup 2 P) (hPX : P = ⁅P, X⁆)
    (hphi : (frattini P).map P.subtype ≤ pCore 2 H)
    (hcomponents : ∀ I : Subgroup Y, I.IsCComponent →
      ⁅I.map Y.subtype, X⁆ ≤ pCore 2 H) :
    ⁅P, Y⁆ ≤ Y.pCoreIn 2 := by
  exact frattini_action_of_quasisimple_components hsqt X P Y hX hP hPX hphi
    (fun I hI _ => hcomponents I hI)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanActions

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Original-geometry consumer using only components with quasisimple
two-core quotients. Relative normality and every quotient transport are
constructed on the literal Y and G₁. -/
theorem frattini_action_of_quasisimple_component_actions (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hodd : Odd (Nat.card E.X))
    (hcomponents : ∀ I : Subgroup G, Source.ComponentIn E.Y I → IsQuasisimple (I ⧸ pCore 2 I) →
      ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2)
    (P : Subgroup G) (hP : P ≤ T) (hPX : P = ⁅P, E.X⁆)
    (hphi : (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2) :
    ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2 := by
  let H := E.G₁
  let X₀ := E.X.subgroupOf H
  let P₀ := P.subgroupOf H
  let Y₀ := E.Y.subgroupOf H
  have hPH : P ≤ H := hP.trans hT
  let : Y₀.Normal := (normal_subgroupOf_iff_le_normalizer E.Y_le_G₁).mpr E.G₁_normalizes_Y
  have hsqt : IsStronglyQuasithin H :=
    isQuasithin_iff_twoLocal.mp E.input.source.simpleQTKE.quasithin E.G₁
      (D.centralQuotientPreimage_twoLocal E.point hp)
  have hodd₀ : Odd (Nat.card X₀) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv]
  have hP₀ : IsPGroup 2 P₀ := (T.isPGroup'.to_le hP).comap_subtype
  have hPX₀ : P₀ = ⁅P₀, X₀⁆ := by
    apply map_injective H.subtype_injective
    rw [map_commutator, map_subgroupOf_eq_of_le hPH, map_subgroupOf_eq_of_le hX]
    exact hPX
  have hphi₀ : (frattini P₀).map P₀.subtype ≤ pCore 2 H := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := ha
    have hb' : subgroupOfEquivOfLe hPH b ∈ frattini P := by
      rw [← frattini_map_equiv (subgroupOfEquivOfLe hPH)]
      exact mem_map_of_mem _ hb
    have hg := hphi (mem_map_of_mem P.subtype hb')
    obtain ⟨c, hc, he⟩ := hg
    have he' : c = (b : H) := Subtype.ext he
    change (b : H) ∈ pCore 2 H
    rw [← he']
    exact hc
  have hcomp₀ (J : Subgroup Y₀) (hJ : J.IsCComponent) (hs : IsQuasisimple (J ⧸ pCore 2 J)) :
      ⁅J.map Y₀.subtype, X₀⁆ ≤ pCore 2 H := by
    let e : Y₀ ≃* E.Y := subgroupOfEquivOfLe E.Y_le_G₁
    let I₀ := J.map e.toMonoidHom
    let I := I₀.map E.Y.subtype
    have hI : Source.ComponentIn E.Y I := by
      refine ⟨map_subtype_le _, ?_⟩
      change (I₀.map E.Y.subtype |>.comap E.Y.subtype).IsCComponent
      rw [comap_map_eq_self_of_injective E.Y.subtype_injective]
      exact hJ.map_equiv e
    let eI : J ≃* I := (e.subgroupMap J).trans
      (I₀.equivMapOfInjective E.Y.subtype E.Y.subtype_injective)
    let : IsQuasisimple (J ⧸ pCore 2 J) := hs
    have hsI : IsQuasisimple (I ⧸ pCore 2 I) :=
      IsQuasisimple.of_mulEquiv (QuotientGroup.congr _ _ eI (pCore_map_iso 2 eI))
    have hc := hcomponents I hI hsI
    have hcore : E.Y.pCoreIn 2 ≤ (pCore 2 H).map H.subtype := by
      have hm := map_mono (f := H.subtype)
        (pCoreIn_le_of_subnormal 2 (inferInstance : Y₀.Normal).isSubnormal)
      rw [map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
        map_subgroupOf_eq_of_le E.Y_le_G₁] at hm
      exact hm
    have he : (J.map Y₀.subtype).map H.subtype = I := by
      rw [map_map]
      change J.map (H.subtype.comp Y₀.subtype) = (J.map e.toMonoidHom).map E.Y.subtype
      rw [map_map]
      rfl
    have hm : (⁅J.map Y₀.subtype, X₀⁆).map H.subtype ≤
        (pCore 2 H).map H.subtype := by
      rw [map_commutator, he, map_subgroupOf_eq_of_le hX]
      exact hc.trans hcore
    exact (map_le_map_iff_of_injective H.subtype_injective).mp hm
  have hc := CartanActions.frattini_action_of_quasisimple_components hsqt X₀ P₀ Y₀
    hodd₀ hP₀ hPX₀ hphi₀ hcomp₀
  have hm := map_mono (f := H.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le hPH,
    map_subgroupOf_eq_of_le E.Y_le_G₁,
    map_pCoreIn_of_injective 2 _ _ H.subtype_injective,
    map_subgroupOf_eq_of_le E.Y_le_G₁] at hm
  exact hm


/-- The original full-component consumer, with its public statement preserved. -/
theorem frattini_action_of_component_actions (hp : E.point ≠ ⊥)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : E.X ≤ E.G₁)
    (hodd : Odd (Nat.card E.X))
    (hcomponents : ∀ I : Subgroup G, Source.ComponentIn E.Y I →
      ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2)
    (P : Subgroup G) (hP : P ≤ T) (hPX : P = ⁅P, E.X⁆)
    (hphi : (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2) :
    ⁅P, E.Y⁆ ≤ E.Y.pCoreIn 2 := by
  exact E.frattini_action_of_quasisimple_component_actions hp hT hX hodd
    (fun I hI _ => hcomponents I hI) P hP hPX hphi

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
