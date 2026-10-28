module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralPointClosure

/-!
# Retaining the actual smaller central-point overgroup

An element of the scalar residual fixing a nonzero original vector has
trivial central character. Hence it belongs to the original component
two-core. The literal local residual in the central-point G.2.1 setup
therefore lies in T, so the same setup restricts to every actual subgroup
between T and C_G(z). No equality of different conjugate closures is used.

Source: Aschbacher--Smith12.7.15(1), printed p.843.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Scalar residual elements fixing any original nonzero vector belong
to the full original component two-core. -/
theorem tripleSixScalarResidual_point_centralizer_le_core
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1) :
    tripleSixScalarResidual K ⊓ centralizer ({(z:G)} : Set G) ≤ K.pCoreIn 2 := by
  intro x hx
  have hXK : tripleSixScalarResidual K ≤ K := map_subtype_le _
  let xK : K := ⟨x,hXK hx.1⟩
  let q := a.groupEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : q xK ∈ center HexEvenAutomorphisms :=
    (tripleSixScalarResidual_image D a) ▸ mem_map_of_mem q hx.1
  let v := (tripleSixPointCoordinates D a z).toAdd
  have hv : v ≠ 0 := by
    intro he
    exact hz ((tripleSixPointCoordinates D a).injective
      (show tripleSixPointCoordinates D a z = tripleSixPointCoordinates D a 1 from
        he.trans (tripleSixPointCoordinates D a).map_one.symm))
  have hfix : Hexacode.evenAction (q xK) v = v :=
    (tripleSixPoint_actor_fixes_iff D a z xK).mpr hx.2
  have hscalar := Hexacode.centerCharacter_action Hexacode.evenFieldRepresentation
    (fun w => Hexacode.scalar_eq_omega_smul w) ⟨q xK,hq⟩ v
  change Hexacode.evenAction (q xK) v = _ at hscalar
  have hvalue : (Hexacode.centerCharacter ⟨q xK,hq⟩ : Hexacode.F) = 1 :=
    (smul_left_injective Hexacode.F hv)
      (hscalar.symm.trans (hfix.trans (one_smul _ _).symm))
  have hunit : Hexacode.centerCharacter ⟨q xK,hq⟩ = 1 := Units.ext hvalue
  have hqone : q xK = 1 := congrArg Subtype.val
    (Hexacode.centerCharacter.injective (hunit.trans Hexacode.centerCharacter.map_one.symm))
  have hxcore : xK ∈ pCore 2 K := by
    apply (QuotientGroup.eq_one_iff xK).mp
    exact a.groupEquiv.injective (hqone.trans a.groupEquiv.map_one.symm)
  exact mem_map_of_mem K.subtype hxcore

/-- G.2.1 on the literal actual local overgroup between T and C_G(z).
Its closure is formed inside that same H, with no ambient-closure substitution. -/
theorem original_tripleSix_central_point_g21_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hHC : H ≤ centralizer ({(z:G)} : Set G)) :
    (show ChapterG.Section02.Setup G from
      {V:=tripleSixPoint D a z,V₁:=zpowers (z:G),L:=tripleSixScalarResidual K,
       T:=T,H:=H}).Hypothesis := by
  have hs := original_tripleSix_central_point_g21 h D a z hz hzT
  let Z := zpowers (z:G)
  let X := tripleSixScalarResidual K
  let S : ChapterG.Section02.Setup G :=
    {V:=tripleSixPoint D a z,V₁:=Z,L:=X,T:=T,H:=H}
  change S.Hypothesis
  let := D.elementary
  have hz1 : (z:G) ≠ 1 := fun he => hz (Subtype.ext he)
  have hzorder : orderOf (z:G) = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (z:G) z.property) hz1
  have hNC : normalizer (Z : Set G) = centralizer ({(z:G)} : Set G) :=
    normalizer_zpowers_eq_centralizer_of_order_two (z:G) hzorder
  have hHN : H ≤ normalizer (Z : Set G) := hHC.trans_eq hNC.symm
  have hZH : Z ≤ H := (zpowers_le.mpr (D.le_sylow z.property)).trans hTH
  have hcore : Z ≤ H.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((IsElementaryAbelian.isPGroup 2 U).to_le (zpowers_le.mpr z.property)) hZH hHN
  have hHchar : H ∈ Chapter1.He G := Chapter1.lemma_1_1_4_6 T
    (h.simpleQTKE.evenCharacteristic T)
    ⟨(fun he => (zpowers_ne_bot.mpr hz1) (bot_unique (hcore.trans_eq he))),hTH⟩
  have hQT : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    have hTJ : (T : Subgroup G) ≤ K ⊔ (T : Subgroup G) := le_sup_right
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTJ] using
      pCoreIn_le_sylow (K ⊔ (T : Subgroup G)) (T.subtype hTJ)
  have hKT : K.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le K.le_normalizer D.sylow_normalizes_component)).trans hQT
  have hL1T : S.L₁ ≤ (T : Subgroup G) := by
    have hh : X ⊓ normalizer (Z : Set G) ≤ K.pCoreIn 2 := by
      rw [hNC]
      exact tripleSixScalarResidual_point_centralizer_le_core D a z hz
    exact (map_subtype_le _).trans (hh.trans hKT)
  have hSyl : ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = T := by
    refine ⟨T.subtype hTH,?_⟩
    simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  exact {
    elementary := hs.elementary
    point_ne_bot := hs.point_ne_bot
    point_le := hs.point_le
    residual := hs.residual
    V_le_T := hs.V_le_T
    T_normalizes_point := hs.T_normalizes_point
    T_normalizes_V := hs.T_normalizes_V
    T_normalizes_L := hs.T_normalizes_L
    sylow_LT := hs.sylow_LT
    H_le := hHN
    local_le := (sup_le hL1T le_rfl).trans hTH
    sylow_H := hSyl
    characteristic_two := (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
      (Chapter1.mem_He_iff.mp hHchar)
    local_normalizes_V := hs.local_normalizes_V
    quotient_nonzero := hs.quotient_nonzero
    irreducible := hs.irreducible }

end CFSG.Quasithin.Chapter12.Section07
