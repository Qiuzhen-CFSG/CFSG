module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldPointTI
public import CFSG.Quasithin.ChapterG.Section02.CentralClosureConsequences
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedSetup
import Theory.GroupTheory.ConjugateSpanNormalizer
import Theory.GroupTheory.CharacteristicCentralizerFusion
import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The actual central-point closure in the triple-six source

For a nonidentity original Sylow-fixed z, the field point V1 is the orbit
span of z under the literal scalar residual X. It is therefore normalized
by the original T. The interval [<z>,V1] has prime index, so G.2.1 applies
with L=X and H=C_G(z). Its local residual remains literally O²(N_X(<z>)).
G.2.2 gives the original closure <V1^C_G(z)>, its full two-core containment,
and its Frattini and reduced-quotient conclusions.

Source: Aschbacher--Smith12.7.15(1), printed p.843, using G.2.1--2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The original scalar residual and field point satisfy G.2.1 over the
centralizer of the unchanged Sylow-fixed involution. -/
theorem original_tripleSix_central_point_g21
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    (show ChapterG.Section02.Setup G from
      {V:=tripleSixPoint D a z,V₁:=zpowers (z:G),L:=tripleSixScalarResidual K,
       T:=T,H:=centralizer ({(z:G)} : Set G)}).Hypothesis := by
  let V := tripleSixPoint D a z
  let Z := zpowers (z:G)
  let X := tripleSixScalarResidual K
  let H := centralizer ({(z:G)} : Set G)
  let S : ChapterG.Section02.Setup G := {V:=V,V₁:=Z,L:=X,T:=T,H:=H}
  change S.Hypothesis
  have hp := tripleSixPoint_properties D a z hz
  have hZV : Z ≤ V := zpowers_le.mpr hp.1
  have hz1 : (z:G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hZne : Z ≠ ⊥ := zpowers_ne_bot.mpr hz1
  let := D.elementary
  let : IsElementaryAbelian 2 V := hp.2.2.2.1
  have hzorder : orderOf (z:G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) hz1
  have hNH : normalizer (Z : Set G) = H :=
    normalizer_zpowers_eq_centralizer_of_order_two (z:G) hzorder
  have hTX : (T : Subgroup G) ≤ normalizer (X : Set G) := by
    let C := centralPreimage (pCore 2 K)
    let R := (pResidual 2 C).map C.subtype
    let : R.Characteristic := inferInstance
    exact D.sylow_normalizes_component.trans
      (normalizer_le_normalizer_characteristic_image K R)
  obtain ⟨hXV,htrans⟩ := tripleSixScalarResidual_point_transitive D a z
  have hspan : conjugateSpanBy Z X = V := by
    apply le_antisymm (conjugateSpanBy_le hZV hXV)
    intro v hv
    by_cases hv1 : v = 1
    · exact hv1 ▸ one_mem _
    · obtain ⟨x,hx,he⟩ := htrans z hp.1 hz1 v hv hv1
      exact subset_closure ⟨x,hx,z,mem_zpowers _,he⟩
  have hTZ : (T : Subgroup G) ≤ normalizer (Z : Set G) := hNH.symm ▸ hzT
  have hTV : (T : Subgroup G) ≤ normalizer (V : Set G) := by
    rw [←hspan]
    exact normalizes_conjugateSpanBy Z X (T : Subgroup G) hTZ hTX
  have hXperfect : IsPPerfect 2 X := by
    let C := centralPreimage (pCore 2 K)
    let R := (pResidual 2 C).map C.subtype
    exact (isPPerfect_embedded_pResidual 2 C).of_surjective
      (K.subtype.subgroupMap R) (K.subtype.subgroupMap_surjective R)
  have hZH : Z ≤ H := hZV.trans (hp.2.1.trans (D.le_sylow.trans hzT))
  have hcore : Z ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 V).to_le hZV) hZH hNH.symm.le
  have hHchar : H ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (h.simpleQTKE.evenCharacteristic T)
    ⟨(fun he => hZne (bot_unique (hcore.trans_eq he))),hzT⟩
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers,hzorder]
  have hindex : Z.relIndex V = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) Z V bot_le hZV
    rw [relIndex_bot_left,relIndex_bot_left,hZcard,hp.2.2.1] at hh
    omega
  have hXTSyl : ∃ P : Sylow 2 (X ⊔ (T : Subgroup G) : Subgroup G),
      (P : Subgroup (X ⊔ (T : Subgroup G) : Subgroup G)).map
        (X ⊔ (T : Subgroup G)).subtype = T := by
    have hTXjoin : (T : Subgroup G) ≤ X ⊔ (T : Subgroup G) := le_sup_right
    refine ⟨T.subtype hTXjoin,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTXjoin]
  have hHSyl : ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = T := by
    have hTH : (T : Subgroup G) ≤ H := hzT
    refine ⟨T.subtype hTH,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  refine {
    elementary := inferInstance
    point_ne_bot := hZne
    point_le := hZV
    residual := (pResidual_eq_top_iff 2 X).mpr hXperfect
    V_le_T := hp.2.1.trans D.le_sylow
    T_normalizes_point := hTZ
    T_normalizes_V := hTV
    T_normalizes_L := hTX
    sylow_LT := hXTSyl
    H_le := hNH.symm.le
    local_le := ?_
    sylow_H := hHSyl
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (Chapter1.mem_He_iff.mp hHchar)
    local_normalizes_V := ?_
    quotient_nonzero := ?_
    irreducible := ?_ }
  · apply sup_le _ hzT
    exact ((map_subtype_le _).trans inf_le_right).trans hNH.le
  · apply sup_le _ hTV
    exact ((map_subtype_le _).trans inf_le_left).trans hXV
  · intro he
    have hh : Nat.card V = 4 := hp.2.2.1
    change Z = V at he
    rw [←he,hZcard] at hh
    contradiction
  · intro A hZA hAV _
    have hh := relIndex_mul_relIndex Z A V hZA hAV
    rw [hindex] at hh
    have hd : Z.relIndex A ∣ 2 := ⟨A.relIndex V,hh.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hone | htwo
    · exact Or.inl (le_antisymm (relIndex_eq_one.mp hone) hZA)
    · have hone : A.relIndex V = 1 := by rw [htwo] at hh; omega
      exact Or.inr (le_antisymm hAV (relIndex_eq_one.mp hone))

/-- The literal original point closure has the complete G.2.2 structure;
its kernel remains the actual cyclic subgroup generated by z. -/
theorem original_tripleSix_central_point_closure
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G)) :
    let S : ChapterG.Section02.Setup G :=
      {V:=tripleSixPoint D a z,V₁:=zpowers (z:G),L:=tripleSixScalarResidual K,
       T:=T,H:=centralizer ({(z:G)} : Set G)}
    letI : (S.V₁.subgroupOf S.G₁).Normal := S.point_normal
    S.U ≤ S.QH ∧ (frattini S.U).map S.U.subtype ≤ zpowers (z:G) ∧
      S.U ≤ (T : Subgroup G) ∧ ⁅S.U,S.QH⁆ ≤ zpowers (z:G) ∧
      IsPReduced 2 ((S.tilde S.U).subgroupOf (S.tilde S.H)) := by
  have hs := original_tripleSix_central_point_g21 h D a z hz hzT
  exact ⟨hs.U_le_core,hs.frattini_U_le_point,hs.U_normal_in_T.1,
    hs.commutator_U_core_le_point,hs.tilde_U_reduced⟩

end CFSG.Quasithin.Chapter12.Section07
