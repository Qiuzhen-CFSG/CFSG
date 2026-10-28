module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedSetup
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPointTI
public import Theory.Representation.HexacodeAction.PairQuotientIrreducible
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import Theory.GroupTheory.PResidual.SylowCentralizer
public import Theory.GroupTheory.ConjugateSpanNormalizer

/-!
# The original weight-four point and G.2.1

For the original Sylow-fixed z, its literal scalar field point is the
X-conjugate span of z. Thus the original T normalizes this point.
The actual even pair stabilizer is irreducible on U/V1; transport through
the original chart gives the invariant subgroup interval.
The G.2.1 local group remains the literal embedded O²(N_K(V1)).
Residual--Sylow generation gives the same action as the full point
stabilizer joined with T. G.2.2 then places the whole original U in
the two-core of N_G(V1).

Source: Aschbacher--Smith12.7.2(3),12.7.13, printed pp.839,843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Representation.BinaryOffender Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem point_sylow_normalizes (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    (T : Subgroup G) ≤ normalizer (tripleSixPoint D a z : Set G) := by
  let V := tripleSixPoint D a z
  let X := tripleSixScalarResidual K
  let Z := zpowers (z : G)
  have hp := tripleSixPoint_properties D a z hz
  have hZ : Z ≤ V := zpowers_le.mpr hp.1
  obtain ⟨hXN,htrans⟩ := tripleSixScalarResidual_point_transitive D a z
  have hspan : conjugateSpanBy Z X = V := by
    apply le_antisymm (conjugateSpanBy_le hZ hXN)
    intro v hv
    by_cases hv1 : v = 1
    · exact hv1 ▸ one_mem _
    · obtain ⟨x,hx,he⟩ := htrans z hp.1 (fun he => hz (Subtype.ext he)) v hv hv1
      exact subset_closure ⟨x,hx,z,mem_zpowers _,he⟩
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer (Z : Set G))
    simpa only [Z,zpowers_eq_closure,centralizer_closure] using hzT
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := by
    let C := centralPreimage (pCore 2 K)
    let R := (pResidual 2 C).map C.subtype
    let : R.Characteristic := inferInstance
    exact D.sylow_normalizes_component.trans
      (normalizer_le_normalizer_characteristic_image K R)
  change (T : Subgroup G) ≤ normalizer (V : Set G)
  rw [←hspan]
  exact normalizes_conjugateSpanBy Z X (T : Subgroup G) hTZ hTX

private theorem point_pair (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    ∃ s : BinaryPermutation.SixPairsQuadratic.Pair,
      (Submodule.span Hexacode.F {(tripleSixPointCoordinates D a z).toAdd}).restrictScalars
        (ZMod 2) = Hexacode.zeroPairPlane s := by
  let f := tripleSixPointCoordinates D a
  have h0 : (f z).toAdd ≠ 0 := by
    intro he
    exact hz (f.injective (show f z = f 1 from he.trans f.map_one.symm))
  have hodd : ¬ 2 ∣ (centralizer ({(z : G)} : Set G)).relIndex K := by
    obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T K D.sylow_normalizes_component
    intro hi
    apply P.not_dvd_index
    apply hi.trans
    apply index_dvd_of_le
    rw [hP]
    exact fun k hk => hzT hk
  have hw : hammingNorm (f z).toAdd.val = 4 := by
    have hc := Hexacode.evenAction_orbit_card (f z).toAdd h0
    rw [tripleSixPoint_orbit_card D a z] at hc
    by_contra hn
    rw [if_neg hn] at hc
    exact hodd (hc ▸ (by norm_num : 2 ∣ 18))
  rcases Hexacode.fieldPoint_full_or_pair (Submodule.span Hexacode.F {(f z).toAdd})
    (finrank_span_singleton h0) with hfull | hpair
  · have hh := hfull.2.2 ⟨(f z).toAdd,Submodule.mem_span_singleton_self _⟩
      (fun he => h0 (congrArg Subtype.val he))
    change hammingNorm (f z).toAdd.val = 6 at hh
    omega
  · exact hpair

private theorem point_interval (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (A : Subgroup G) (hVA : tripleSixPoint D a z ≤ A) (hAU : A ≤ U)
    (hA : K ⊓ normalizer (tripleSixPoint D a z : Set G) ≤ normalizer (A : Set G)) :
    A = tripleSixPoint D a z ∨ A = U := by
  let f := tripleSixPointCoordinates D a
  let P := Submodule.span Hexacode.F {(f z).toAdd}
  let E : Subgroup U ≃o Submodule (ZMod 2) hexacode :=
    f.mapSubgroup.trans (Subgroup.toAddSubgroup'.trans (AddSubgroup.toZModSubmodule 2))
  let W := E (A.subgroupOf U)
  have hp := tripleSixPoint_properties D a z hz
  have hpoint : E ((tripleSixPoint D a z).subgroupOf U) = P.restrictScalars (ZMod 2) := by
    have hm : ((tripleSixPoint D a z).subgroupOf U).map f.toMonoidHom =
        P.toAddSubgroup.toSubgroup := by
      change (((P.toAddSubgroup.toSubgroup.comap f.toMonoidHom).map U.subtype).comap
        U.subtype).map f.toMonoidHom = _
      rw [comap_map_eq_self_of_injective U.subtype_injective,
        map_comap_eq_self_of_surjective f.surjective]
    change AddSubgroup.toZModSubmodule 2
      (Subgroup.toAddSubgroup' (((tripleSixPoint D a z).subgroupOf U).map f.toMonoidHom)) = _
    rw [hm]
    rfl
  obtain ⟨s,hs⟩ := point_pair D a z hz hzT
  have hPW : Hexacode.zeroPairPlane s ≤ W := by
    rw [←hs,←hpoint]
    exact E.monotone (subgroupOf_mono U hVA)
  have hstable (g : HexEvenAutomorphisms)
      (hg : g.val ∈ subspaceStabilizer Hexacode.action (Hexacode.zeroPairPlane s)) :
      g.val ∈ subspaceStabilizer Hexacode.action W := by
    obtain ⟨k,hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm g)
    have hkV : (k : G) ∈ normalizer (tripleSixPoint D a z : Set G) := by
      apply mem_normalizer_fintype
      rintro v ⟨u,hu,rfl⟩
      have he := tripleSixPointCoordinates_conjugate D a k u
      rw [hk,a.groupEquiv.apply_symm_apply] at he
      change (k : G)*(u : G)*(k : G)⁻¹ ∈ tripleSixPoint D a z
      rw [←he]
      refine ⟨f.symm (Multiplicative.ofAdd (Hexacode.evenAction g (f u).toAdd)),?_,rfl⟩
      change (f (f.symm (Multiplicative.ofAdd (Hexacode.evenAction g (f u).toAdd)))).toAdd ∈ P
      rw [f.apply_symm_apply]
      have hmem : (f u).toAdd ∈ Hexacode.zeroPairPlane s := hs ▸ hu
      change Hexacode.action g.val (f u).toAdd ∈ P.restrictScalars (ZMod 2)
      rw [hs]
      exact (hg (f u).toAdd).mpr hmem
    have hforward (g : HexEvenAutomorphisms) (k : K)
        (hk : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k) = g)
        (hkn : (k : G) ∈ normalizer (A : Set G)) (v : hexacode) (hv : v ∈ W) :
        Hexacode.evenAction g v ∈ W := by
      change Multiplicative.ofAdd v ∈ (A.subgroupOf U).map f.toMonoidHom at hv
      obtain ⟨u,hu,huv⟩ := hv
      have he := tripleSixPointCoordinates_conjugate D a k u
      rw [hk] at he
      have hf : (f u).toAdd = v := congrArg Multiplicative.toAdd huv
      rw [hf] at he
      change Multiplicative.ofAdd (Hexacode.evenAction g v) ∈ (A.subgroupOf U).map f.toMonoidHom
      refine ⟨f.symm (Multiplicative.ofAdd (Hexacode.evenAction g v)),?_,f.apply_symm_apply _⟩
      change ((f.symm (Multiplicative.ofAdd (Hexacode.evenAction g v))) : G) ∈ A
      rw [he]
      exact (mem_normalizer_iff.mp hkn u).mp hu
    have hkn := hA ⟨k.property,hkV⟩
    have hkg : a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k) = g := by
      rw [hk,a.groupEquiv.apply_symm_apply]
    intro v
    constructor
    · intro hv
      have hh := hforward g⁻¹ k⁻¹ (by rw [map_inv,map_inv,hkg])
        ((normalizer (A : Set G)).inv_mem hkn) (Hexacode.evenAction g v) hv
      simpa only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply] using hh
    · exact hforward g k hkg hkn v
  rcases Hexacode.zeroPairPlane_invariant_interval s W hPW hstable with he | he
  · left
    rw [←map_subgroupOf_eq_of_le hAU,←map_subgroupOf_eq_of_le hp.2.1]
    congr 1
    apply E.injective
    exact he.trans (hpoint.trans hs).symm
  · right
    have hh : A.subgroupOf U = ⊤ := E.injective (he.trans E.map_top.symm)
    have hm := congrArg (map U.subtype) hh
    simpa only [map_subgroupOf_eq_of_le hAU,←MonoidHom.range_eq_map,range_subtype] using hm

/-- G.2.1 for the actual original field point and any of its displayed
local overgroups. The local seed is the literal embedded two-residual. -/
theorem original_tripleSix_weightFour_point_g21_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1) (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (H : Subgroup G)
    (hlocal : (K ⊓ normalizer (tripleSixPoint D a z : Set G)) ⊔ (T : Subgroup G) ≤ H)
    (hHN : H ≤ normalizer (tripleSixPoint D a z : Set G)) :
    (show ChapterG.Section02.Setup G from
      {V:=U,V₁:=tripleSixPoint D a z,L:=K,T:=T,H:=H}).Hypothesis := by
  let V := tripleSixPoint D a z
  let N := normalizer (V : Set G)
  let P := K ⊓ N
  let R := (pResidual 2 P).map P.subtype
  let S : ChapterG.Section02.Setup G := {V:=U,V₁:=V,L:=K,T:=T,H:=H}
  change S.Hypothesis
  have hp := tripleSixPoint_properties D a z hz
  have hVne : V ≠ ⊥ := by
    intro he
    exact hz (Subtype.ext (mem_bot.mp (he ▸ hp.1)))
  have hTV : (T : Subgroup G) ≤ N := point_sylow_normalizes D a z hz hzT
  have hTU := ((structural K h).2.2 U D).1
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans hlocal
  have hUH : U ≤ H := D.le_sylow.trans hTH
  have hVH : V ≤ H := hp.2.1.trans hUH
  have hTP : (T : Subgroup G) ≤ normalizer (P : Set G) :=
    (le_inf D.sylow_normalizes_component (hTV.trans N.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hRT : R ⊔ (T : Subgroup G) = P ⊔ (T : Subgroup G) :=
    embedded_pResidual_sup_sylow_of_normalizes T P hTP
  have hcore : V ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    (by let := hp.2.2.2.1; exact IsElementaryAbelian.isPGroup 2 V) hVH hHN
  have hHchar : H ∈ Chapter1.He G :=
    Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
      ⟨(fun he => hVne (bot_unique (hcore.trans_eq he))),hTH⟩
  have hsylLT : ∃ P : Sylow 2 (K ⊔ (T : Subgroup G) : Subgroup G),
      (P : Subgroup (K ⊔ (T : Subgroup G) : Subgroup G)).map (K ⊔ (T : Subgroup G)).subtype = T := by
    refine ⟨T.subtype (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right),?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le
      (show (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) from le_sup_right)]
  have hsylH : ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = T := by
    refine ⟨T.subtype hTH,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  refine {
    elementary := D.elementary
    point_ne_bot := hVne
    point_le := hp.2.1
    residual := (pResidual_eq_top_iff 2 K).mpr h.maximal_faithful.2.1.2.1
    V_le_T := D.le_sylow
    T_normalizes_point := hTV
    T_normalizes_V := hTU
    T_normalizes_L := D.sylow_normalizes_component
    sylow_LT := hsylLT
    H_le := hHN
    local_le := ?_
    sylow_H := hsylH
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr (Chapter1.mem_He_iff.mp hHchar)
    local_normalizes_V := ?_
    quotient_nonzero := ?_
    irreducible := ?_ }
  · change R ⊔ (T : Subgroup G) ≤ H
    exact hRT ▸ hlocal
  · change R ⊔ (T : Subgroup G) ≤ normalizer (U : Set G)
    exact sup_le (((map_subtype_le _).trans inf_le_left).trans D.normalizes) hTU
  · intro he
    have hc : Nat.card U = 64 :=
      (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans hexacode_card
    have hvc : Nat.card V = 4 := hp.2.2.1
    change V = U at he
    rw [he,hc] at hvc
    contradiction
  · intro A hVA hAU hn
    apply point_interval D a z hz hzT A hVA hAU
    change R ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) at hn
    rw [hRT] at hn
    exact le_sup_left.trans hn

/-- The entire original U lies in the two-core of the actual point normalizer. -/
theorem original_tripleSix_weightFour_point_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1) (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    U ≤ (normalizer (tripleSixPoint D a z : Set G)).pCoreIn 2 := by
  have hn := point_sylow_normalizes D a z hz hzT
  have hs := original_tripleSix_weightFour_point_g21_at h structural D a z hz hzT
    (normalizer (tripleSixPoint D a z : Set G)) (sup_le inf_le_right hn) le_rfl
  exact (le_conjugateSpanBy _ _).trans hs.U_le_core

end CFSG.Quasithin.Chapter12.Section07
