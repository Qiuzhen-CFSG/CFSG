module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureInnerLinearData
public import Theory.SpecificGroups.BinaryLinear.SylowNormalizedCubicResidual
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.GroupTheory.PPerfectCubicImage

/-!
# The literal degree-four point residual is a marked parabolic residual

The unchanged original quotient representation is put in binary four-space
coordinates. Its full kernel and R-image are retained. The original J-image
is two-perfect with cubic core quotient, and the image of the original T is
a full Sylow normalizing it. Thus their literal join is a minimal parabolic
in that same Sylow flag, with J-image exactly the embedded two-residual.

Source: Aschbacher--Smith 12.7.16, printed p.844.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Degree four supplies the actual same-Sylow parabolic marking of the
original point residual, with the complete original conjugation kernel. -/
theorem original_tripleSix_central_closure_degreeFour_parabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z:G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z:G)} : Set G)).pCoreIn 2)
    (hinner : inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G)))) ≤ inducedAutomizer U K)
    (hW32 : Nat.card (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z:G)} : Set G))))=32) :
    let C := centralizer ({(z:G)} : Set G)
    let J := tripleSixWeightFourResidual K z
    let R := conjugateSpanBy U C
    let H := R ⊔ J ⊔ (T : Subgroup G)
    let W := conjugateSpanBy (tripleSixPoint D a z) R
    let Z := zpowers (z:G)
    ∃ (hHW : H≤normalizer (W : Set G)) (hZN : (Z.subgroupOf W).Normal),
      letI := hZN
      ∃ he : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        letI := he
        ∃ (e : Additive (W ⧸ Z.subgroupOf W) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
          (r : H →* BinaryLinear.OuterCyclic.LinearGroup 4), Function.Surjective r ∧
          (∀ (g : H) (w : W), r g (e (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w))) =
            e (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩))) ∧
          (∀ g : H, g∈r.ker ↔ ∀ w∈W, ⁅w,(g:G)⁆∈Z) ∧
          (R.subgroupOf H).map r=⊤ ∧ Nat.card ((U.subgroupOf H).map r)=4 ∧
          ∃ b : BinaryLinear.InvariantNodeActions.Basis 3,
            ((T : Subgroup G).subgroupOf H).map r=
              BinaryLinear.InvariantNodeActions.cutStabilizer b Set.univ ∧
            ∃ i : Fin 3, (J.subgroupOf H).map r=
              BinaryLinear.OrderedResidualConjugators.nodeResidual b i := by
  let C := centralizer ({(z:G)} : Set G)
  let J := tripleSixWeightFourResidual K z
  let R := conjugateSpanBy U C
  let H := R ⊔ J ⊔ (T : Subgroup G)
  let W := conjugateSpanBy (tripleSixPoint D a z) R
  let Z := zpowers (z:G)
  obtain ⟨hHW,hZN,hrest⟩ := original_tripleSix_central_closure_inner_linear_data
    h structural D a z hz hzT hnot hinner
  let : (Z.subgroupOf W).Normal := hZN
  obtain ⟨he,φ,hformula,hker,hwhole,hR,hcarddim,hcard,_⟩ := hrest
  let := he
  let V := Additive (W ⧸ Z.subgroupOf W)
  have hp := tripleSixPoint_properties D a z hz
  let : IsElementaryAbelian 2 U := D.elementary
  have hzorder : orderOf (z:G)=2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) (fun hh=>hz (Subtype.ext hh))
  have hZW : Z≤W := (zpowers_le.mpr hp.1).trans
    (le_conjugateSpanBy (tripleSixPoint D a z) R)
  have hc := (Z.subgroupOf W).index_mul_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv,Nat.card_zpowers,hzorder] at hc
  change Nat.card (W ⧸ Z.subgroupOf W)*2=Nat.card W at hc
  change Nat.card W=32 at hW32
  have hv := Module.natCard_eq_pow_finrank (K:=ZMod 2) (V:=V)
  rw [Nat.card_zmod] at hv
  change Nat.card (W ⧸ Z.subgroupOf W)=_ at hv
  have hd : Module.finrank (ZMod 2) V=4 := by
    rcases hcarddim with hd | hd
    · rw [hd] at hv
      norm_num at hv
      omega
    · exact hd
  let e := (Module.finBasisOfFinrankEq (ZMod 2) V hd).equivFun
  let eG := BinaryLinear.SmallParabolicLevi.linearGroupCongr e
  let r := eG.toMonoidHom.comp φ
  have hr : Function.Surjective r := eG.surjective.comp (MonoidHom.range_eq_top.mp hwhole)
  obtain ⟨N,hN,hmem,_,_,_,_,_,_,hJcard⟩ :=
    original_tripleSix_central_closure_rank h structural D a z hz hzT hnot
  let : N.Normal := hN
  have hk : r.ker=N := by
    ext g
    change eG (φ g)=1 ↔ g∈N
    rw [eG.map_eq_one_iff]
    change φ g=1 ↔ g∈N
    exact (hker g).trans (hmem g).symm
  let Jbar := (J.subgroupOf H).map (QuotientGroup.mk' N)
  let Jmodel := (J.subgroupOf H).map r
  have hJne : Jmodel≠⊥ := by
    intro hb
    have hJN : J.subgroupOf H≤N := hk ▸ ((J.subgroupOf H).map_eq_bot_iff.mp hb)
    have hb' : Jbar=⊥ := (J.subgroupOf H).map_eq_bot_iff.mpr (by rwa [QuotientGroup.ker_mk'])
    have hbound := Nat.card_le_card_of_surjective (QuotientGroup.mk' (pCore 2 Jbar))
      (QuotientGroup.mk'_surjective _)
    change Nat.card (Jbar ⧸ pCore 2 Jbar)=3 at hJcard
    rw [hJcard,hb',card_bot] at hbound
    omega
  have hJH : J≤H := le_sup_right.trans le_sup_left
  let f : J →* Jmodel := (r.subgroupMap (J.subgroupOf H)).comp
    (subgroupOfEquivOfLe hJH).symm.toMonoidHom
  have hf : Function.Surjective f := (r.subgroupMap_surjective (J.subgroupOf H)).comp
    (subgroupOfEquivOfLe hJH).symm.surjective
  have hfn : f≠1 := by
    intro he
    apply hJne
    apply _root_.eq_bot_iff.mpr
    intro y hy
    obtain ⟨b,hb⟩ := hf ⟨y,hy⟩
    have hy1 : (⟨y,hy⟩ : Jmodel)=1 := hb.symm.trans (congrArg (fun k : J →* Jmodel => k b) he)
    exact congrArg Subtype.val hy1
  have hJ := original_tripleSix_weightFour_cubic_residual D a z hz hzT
  have hperfect : IsPPerfect 2 Jmodel := hJ.2.2.1.of_surjective f hf
  have hcubic : Nat.card (Jmodel ⧸ pCore 2 Jmodel)=3 :=
    cubic_core_quotient_of_twoPerfect_image hJ.2.2.1 hJ.2.2.2.1 f hf hfn
  let S := (T.subtype (show (T : Subgroup G)≤H from le_sup_right)).mapSurjective hr
  have hnorm : ((T : Subgroup G).subgroupOf H)≤normalizer (J.subgroupOf H : Set H) :=
    (comap_mono hJ.2.1).trans (le_normalizer_comap H.subtype)
  have hS : (S : Subgroup (BinaryLinear.OuterCyclic.LinearGroup 4))≤normalizer (Jmodel : Set _) := by
    change ((T : Subgroup G).subgroupOf H).map r≤normalizer (Jmodel : Set _)
    exact (map_mono hnorm).trans (le_normalizer_map r)
  obtain ⟨b,hb,i,_,hmark⟩ := BinaryLinear.SylowFlagOvergroups.sylow_normalized_cubic_residual
    Jmodel S hperfect hcubic hS
  have hformula' (g : H) (w : W) :
      r g (e (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W) w)))=
        e (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf W)
          ⟨(g:G)*w*(g:G)⁻¹,(mem_normalizer_iff.mp (hHW g.property) w).mp w.property⟩)) := by
    change e (φ g (e.symm (e _)))=_
    rw [e.symm_apply_apply,hformula]
  have hker' (g : H) : g∈r.ker ↔ ∀ w∈W, ⁅w,(g:G)⁆∈Z := by
    change eG (φ g)=1 ↔ _
    rw [eG.map_eq_one_iff]
    exact hker g
  have hR' : (R.subgroupOf H).map r=⊤ := by
    rw [show r=eG.toMonoidHom.comp φ from rfl,←map_map,hR,map_top_of_surjective _ eG.surjective]
  have hcard' : Nat.card ((U.subgroupOf H).map r)=4 := by
    rw [show r=eG.toMonoidHom.comp φ from rfl,←map_map,card_map_of_injective eG.injective]
    exact hcard
  exact ⟨hHW,hZN,he,e,r,hr,hformula',hker',hR',hcard',b,hb,i,hmark⟩

end CFSG.Quasithin.Chapter12.Section07
