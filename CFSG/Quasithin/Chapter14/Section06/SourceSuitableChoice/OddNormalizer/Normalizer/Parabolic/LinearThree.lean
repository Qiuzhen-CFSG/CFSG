module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Closure.Models.LinearThreeSource
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Normalizer.Parabolic.Four
public import Theory.SpecificGroups.PSL3Two.Parabolics.WreathNormalizer
public import Theory.GroupTheory.PCoreInRestriction

/-!
# The original normalizer in the binary linear-three wreath branch

The original H-image is a solvable Sylow overgroup with order divisible
by nine. The strengthened square theorem marks it as the actual line
parabolic wreath, so its core is weakly closed and its normalizer is H.
Both statements lift through the literal map Mc → Mc/O₂(Mc).

The source application retains the original relative component, inverse
exchanger, full layer, and exchanged factors. Weak closure applied to
Q_H ≤ S = N_T(H₁) forces N_Mc(S) into H, where its normalizer is already T.
The resulting index and equality are exactly original 14.6.16 in this row.
The full PSL₂(16) image and the invariant higher-linear parabolic branches
remain with qt-e-suitable-odd-normalizer. Earlier primitive and exchanged
inputs retain their existing producers; suitable-choice assembly remains
with qt-e-suitable-existence.

Source: Aschbacher--Smith 14.6.14(3), 14.6.16, printed pp.1033,1035.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
local notation "L3" => Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)

/-- The actual marked closure square determines the original H-core's
normalizer and weak closure through the literal two-core quotient. -/
theorem linear_three_closure_core_normalizer
    (T : Sylow 2 G) {H Mc K L : Subgroup G} (hTH : (T : Subgroup G) ≤ H)
    (hHMc : H ≤ Mc) (hHsol : Group.IsSolvable H)
    (hcard : Nat.card (H ⧸ pCore 2 H) = 72)
    (hlayer : StrictClosureLayer Mc K) {s : Mc}
    (ha : MarkedExchangedWreath Mc K L s L3) :
    Mc ⊓ normalizer (H.pCoreIn 2 : Set G) = H ∧
      ∀ g ∈ Mc, (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
        (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 := by
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  have hproper := marked_exchanged_square_ne_top ha
  obtain ⟨_e,k,_hl,_hr,_ρ,_hi,_hin,_hact⟩ := ha
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let N := (K.subgroupOf Mc).map q
  let B := (H.subgroupOf Mc).map q
  have hN : N = generalizedFitting (Mc ⧸ pCore 2 Mc) := hlayer.image_eq_generalizedFitting
  let : N.Normal := hN.symm ▸ inferInstance
  let ep := Matrix.PSL3Two.equiv.symm
  let k' := k.trans (ep.prodCongr ep)
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  let : Group.IsPerfect Matrix.PSL3Two.SL := Atlas.sl_perfect 3 (by decide)
  let : IsQuasisimple Matrix.PSL3Two.SL := {
    simple := ((QuotientGroup.quotientMulEquivOfEq Matrix.PSL3Two.center_eq_bot).trans
      QuotientGroup.quotientBot).isSimpleGroup }
  have hc := AutomorphismSquare.square_layer_centralizer N k' Matrix.PSL3Two.center_eq_bot hN
  let P := (T.subtype (hTH.trans hHMc)).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Mc))
  have hPB : (P : Subgroup (Mc ⧸ pCore 2 Mc)) ≤ B := map_mono (subgroupOf_mono Mc hTH)
  obtain ⟨hquot,hgen⟩ := AutomorphismSquare.square_layer_two_extension N k'
    Matrix.PSL3Two.center_eq_bot hN Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup P
  let h := subgroupOfEquivOfLe hHMc
  let := hHsol
  let : Group.IsSolvable (H.subgroupOf Mc) :=
    Group.isSolvable_of_isSolvable_injective (f := h.toMonoidHom) h.injective
  have hs : Group.IsSolvable B := Group.isSolvable_of_surjective (q.subgroupMap_surjective _)
  let f := q.subgroupMap (H.subgroupOf Mc)
  have hk : IsPGroup 2 f.ker := by
    rw [show f.ker = (pCore 2 Mc).comap (H.subgroupOf Mc).subtype by
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      rfl]
    exact pCore_isPGroup.comap_subtype
  let eh := QuotientGroup.congr _ _ h (pCore_map_iso 2 h)
  let eqB := f.pCoreQuotientEquiv (q.subgroupMap_surjective _) hk
  have hbcard : Nat.card (B ⧸ pCore 2 B) = 72 := by
    rw [←Nat.card_congr eqB.toEquiv,Nat.card_congr eh.toEquiv]
    exact hcard
  have h9 : 9 ∣ Nat.card B := (show 9 ∣ Nat.card (B ⧸ pCore 2 B) by rw [hbcard]; decide).trans
    (card_dvd_of_surjective _ (QuotientGroup.mk'_surjective (pCore 2 B)))
  obtain ⟨E,hE⟩ := Matrix.PSL3Two.SquareParabolic.full_wreath_marking_of_solvable_overgroup
    N B k' hc hquot P hgen hPB hs h9 hproper
  let f := E.toMonoidHom.comp q
  have hf : Function.Surjective f := E.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkf : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ E.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hTMc := hTH.trans hHMc
  have hmark : (H.subgroupOf Mc).map f = Matrix.PSL3Two.WreathPair.line := by
    rw [show f = E.toMonoidHom.comp q from rfl,←Subgroup.map_map]
    exact hE
  obtain ⟨hn,hw⟩ := Matrix.PSL3Two.WreathPair.cover_core_normalizer f hf hkf
    (T.subtype hTMc) (H.subgroupOf Mc) (fun _ hx => hTH hx) hmark
  have hC : (H.subgroupOf Mc).pCoreIn 2 = (H.pCoreIn 2).subgroupOf Mc := pCoreIn_subgroupOf 2 H Mc hHMc
  have hCMc : H.pCoreIn 2 ≤ Mc := (pCoreIn_le 2 H).trans hHMc
  have hCG : ((H.subgroupOf Mc).pCoreIn 2).map Mc.subtype = H.pCoreIn 2 := by
    rw [hC,map_subgroupOf_eq_of_le hCMc]
  refine ⟨?_,?_⟩
  · rw [hC,←subgroupOf_normalizer_eq hCMc] at hn
    have hh := congrArg (map Mc.subtype) hn
    change ((normalizer (H.pCoreIn 2 : Set G)).subgroupOf Mc).map Mc.subtype =
      (H.subgroupOf Mc).map Mc.subtype at hh
    simpa only [subgroupOf_map_subtype,map_subgroupOf_eq_of_le hHMc,inf_comm] using hh
  · intro g hg hle
    let t : Mc := ⟨g,hg⟩
    have hconj : (((H.subgroupOf Mc).pCoreIn 2).map (MulAut.conj t).toMonoidHom).map Mc.subtype =
        (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
      rw [map_map,←hCG,map_map]
      rfl
    have hcT : ((H.subgroupOf Mc).pCoreIn 2).map (MulAut.conj t).toMonoidHom ≤
        (T.subtype hTMc : Subgroup Mc) := by
      intro x hx
      change (x : G) ∈ (T : Subgroup G)
      exact hle (hconj ▸ mem_map_of_mem Mc.subtype hx)
    have hh := congrArg (map Mc.subtype) (hw t hcT)
    rwa [hconj,hCG] at hh

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open scoped IsMulCommutative
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
variable [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
include hG hempty hM hunique hmany hcard e hab hH

/-- Apply the parabolic marking and weak closure to the original component row. -/
theorem source_linear_three_core_normalizer
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc))
    (hb : ClassicalGroup.IsPSL ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2) :
    Mc ⊓ normalizer (H.pCoreIn 2 : Set G) = H ∧
      ∀ g ∈ Mc, (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
        (H.pCoreIn 2).map (MulAut.conj g).toMonoidHom = H.pCoreIn 2 := by
  have hHMc : H ≤ Mc :=
    (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH).H_centralizes.trans
      (InitialSource.centralizer_le_partner T hunique)
  have hTMc : (T : Subgroup G) ≤ Mc := hH.1.2.trans hHMc
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hb
  let : Fintype F := Fintype.ofFinite F
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  let eA := eF.trans (Atlas.fieldEquivPSL 3 ef)
  let ec : XiQuotient L ≃* (L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc)) :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hL)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hL))).symm.trans (cComponentTwoCoreQuotientEquiv hcomp)
  let := hq
  let : IsQuasisimple L3 := IsQuasisimple.of_mulEquiv (ec.trans eA)
  have ho : IsPGroup 2 (MulAut.Outer L3) :=
    Matrix.PSL3Two.Automorphisms.outer_sl_isTwoGroup.of_equiv
      (MulAut.outerCongr Matrix.PSL3Two.equiv)
  obtain ⟨_,s,_hs,_hsn,_hprod,ha⟩ := exchanged_closure_wreath_action hTMc hL hcomp
    ⟨T.subtype hTMc,by simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc]⟩
    hm.1 hlayer eA Matrix.PSL3Two.Automorphisms.center_psl_eq_bot ho
  exact linear_three_closure_core_normalizer T hH.1.2 hHMc (primitiveResidual_isSolvable H hprim)
    (by simpa using OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 3 H0 H1 H2 d)
    hlayer ha
/-- Original 14.6.16 in the PSL₃(2) exchanged-component row. -/
theorem source_normalizer_linear_three_component
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc))
    (hb : ClassicalGroup.IsPSL ((L.subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))) 3 2) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  obtain ⟨hi,hHN,hQS,hTN⟩ := source_exchanged_normalizer_initial
    hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 d
  obtain ⟨hQ,hw⟩ := source_linear_three_core_normalizer
    hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d L hL hcomp hq hm hlayer hb
  let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
  refine ⟨hi,le_antisymm ?_ hTN⟩
  intro g hg
  rw [←hHN]
  refine ⟨?_,hg.2⟩
  rw [←hQ]
  refine ⟨hg.1,mem_normalizer_iff_map_conj_eq.mpr (hw g hg.1 ?_)⟩
  have hn : S.map (MulAut.conj g).toMonoidHom = S := mem_normalizer_iff_map_conj_eq.mp hg.2
  exact ((map_mono (f := (MulAut.conj g).toMonoidHom) hQS).trans_eq hn).trans inf_le_left

/-- All cubic exchanged components now give original 14.6.16. The source
maximal-prime sieve supplies the model; no model premise is added here. -/
theorem source_normalizer_cubic_exchanged_component
    (H0 H1 H2 : Subgroup G) (hprim : PrimitiveResidual H 3)
    (d : ExchangedFactorSetup a (T : Subgroup G) 3 H0 H1 H2)
    (hmax : MaximalOddPrime (T : Subgroup G) M 3)
    (L : Subgroup G) (hL : L ≤ Mc) (hcomp : (L.subgroupOf Mc).IsCComponent)
    (hq : IsQuasisimple (XiQuotient L))
    (hm : StrictExchangedModel (T : Subgroup G) Mc (residualClosure H Mc) L 3)
    (hlayer : StrictClosureLayer Mc (residualClosure H Mc)) :
    let S := (T : Subgroup G) ⊓ normalizer (H1 : Set G)
    S.relIndex (T : Subgroup G) = 2 ∧ Mc ⊓ normalizer (S : Set G) = (T : Subgroup G) := by
  rcases source_strict_exchanged_component_models
      hG T hempty hM hunique hmany hcard e hab H hH a 3 H0 H1 H2 hprim d hmax L hcomp hm with
    ⟨_,hfour⟩ | ⟨hfalse,_⟩ | ⟨_,hthree⟩
  · obtain ⟨⟨eW⟩,_⟩ := source_four_closure_alternative
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d L hL hcomp hq hm hlayer hfour
    exact source_normalizer_four_closure_case
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d eW
  · norm_num at hfalse
  · exact source_normalizer_linear_three_component
      hG T hempty hM hunique hmany hcard e hab H hH a H0 H1 H2 hprim d
      L hL hcomp hq hm hlayer hthree

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer
