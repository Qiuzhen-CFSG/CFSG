module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableAmalgam
public import Theory.GroupTheory.SymmetricThreeResidualKernel
public import Theory.GroupTheory.PCoreLocalKernel
public import Theory.GroupTheory.PCoreInRestriction
public import Stellmacher.CentralizerQuotientRepresentation
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The literal solvable Goldschmidt quotient and its FF module

The kernel on KT is a two-group. Otherwise it contains O²(KT), hence
O²(K) centralizes the marked plane. Since H normalizes O²(K), it then
centralizes its H-span U. The original action-kernel bound makes O²(K),
and thus K, a two-group, contradicting the actual escape from N_G(L).

The two local kernel comparisons preserve both S₃ quotients, the Sylow
overlap, and the distinct embedded cores in Ke/C_Ke(Ue). The original
Thompson escape survives on Ue and supplies an actual binary FF offender.
The final theorem constructs all these data from the literal S₃×S₃ model
and original contrary center hypothesis, with no kernel or offender callback.

The characteristic-two vertex argument, F.6.18 model exclusions and final
dimension contradiction remain with qt-d-hs-centerless-source, as does
source_centerless. The later action theorem assumes centerlessness and is
not used. Source: Aschbacher--Smith 14.3.31, printed p.1003; B.2.5--7, p.76.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- The actual orbit-module action has a two-group kernel on KT. -/
theorem source_amalgam_actor_kernel (K : Subgroup G) (hKH : K ≤ F.H)
    (hKN : F.H ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ normalizer (L : Set G))
    (model : Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let A := (K ⊔ (T : Subgroup G)).subgroupOf E
    IsPGroup 2 (q.subgroupMap A).ker := by
  let E := amalgamGroup F L K
  let Ue := amalgamModule F L K
  let A0 := K ⊔ (T : Subgroup G)
  let A := A0.subgroupOf E
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let f := q.subgroupMap A
  obtain ⟨em⟩ := model
  let j : A ≃* A0 := subgroupOfEquivOfLe le_sup_left
  let emA := (QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans em
  rcases SymmetricThreeTwoCore.normal_twoGroup_or_residual_le emA f.ker with hp | hr
  · exact hp
  · exfalso
    let R := (pResidual 2 K).map K.subtype
    have hRH : R ≤ F.H := (map_subtype_le _).trans hKH
    have hRN : F.H ≤ normalizer (R : Set G) :=
      hKN.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))
    have hKE : K ≤ E := le_sup_left.trans le_sup_left
    let i : K →* A := {
      toFun := fun k => ⟨⟨k,hKE k.property⟩,(show K ≤ A0 from le_sup_left) k.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
    have h1E : F.Vi 1 ≤ E := (F.le_seed 1).trans
      (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K))
    have hUE : Ue ≤ E := conjugateSpanBy_le_self h1E
    have hplane : F.Vi 2 ≤ Ue :=
      (source_amalgam_plane_image_and_overlap d earlier hq chosen structural alternatives F hne K hKH).1
    have hRC : R ≤ centralizer (F.Vi 2 : Set G) := by
      rintro r ⟨k,hk,rfl⟩ v hv
      have hri : i k ∈ pResidual 2 A := map_pResidual_le 2 i (mem_map_of_mem i hk)
      have hq : q ((i k : A) : E) = 1 := congrArg Subtype.val (hr hri)
      have hc : ((i k : A) : E) ∈ amalgamKernel F L K := (QuotientGroup.eq_one_iff _).mp hq
      exact congrArg Subtype.val (hc ⟨v,hUE (hplane hv)⟩ (hplane hv))
    have hRU : R ≤ centralizer (F.U : Set G) := by
      rw [(source_seed_geometry d earlier hq chosen F).2.1]
      exact le_centralizer_conjugateSpanBy_of_normalizes R (F.Vi 2) F.H hRN hRC
    have hRp : IsPGroup 2 R := by
      apply ((pCore_isPGroup (p := 2) (G := F.H)).map F.H.subtype).to_le
      intro r hr
      apply mem_map.mpr
      refine ⟨⟨r,hRH hr⟩,?_,rfl⟩
      apply source_center_centralizing_kernel_le_core d earlier hq chosen structural alternatives F hne
      refine ⟨(centralizer_le (map_subtype_le (center F.U))) (hRU hr),?_⟩
      apply (F.mem_uhatAction_ker_iff _).mpr
      intro v hv
      have hc := (hRU hr) v hv
      change r*v*r⁻¹*v⁻¹ ∈ F.ZU
      rw [←hc]
      simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,one_mul] using F.ZU.one_mem
    have hpr : IsPGroup 2 (pResidual 2 K) := hRp.of_equiv
      ((pResidual 2 K).equivMapOfInjective K.subtype K.subtype_injective).symm
    have hkp : IsPGroup 2 K := isPGroup_of_residual_isPGroup 2 hpr
    have hKT : K ≤ (T : Subgroup G) :=
      hkp.le_sylow_of_normalized T ((F.invariant 1).trans hKN)
    exact hout (hKT.trans ((higherRankHypothesis d earlier hq chosen).sylow_normalizes structural))


/-- Both S₃ vertices and their unequal cores survive the original action quotient. -/
theorem source_amalgam_quotient_goldschmidt (K : Subgroup G) (hKH : K ≤ F.H)
    (hKN : F.H ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ normalizer (L : Set G))
    (model : Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hneq : (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ (K ⊔ (T : Subgroup G)).pCoreIn 2) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let A := (K ⊔ (T : Subgroup G)).subgroupOf E
    let B := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
    ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧
      (B.map q).pCoreIn 2 ≠ (A.map q).pCoreIn 2 := by
  let E := amalgamGroup F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let A := (K ⊔ (T : Subgroup G)).subgroupOf E
  let B := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
  have hG := source_solvable_ambient_goldschmidt d earlier hq chosen structural alternatives F hne K hKH model
  have hBP : B = (F.P L).subgroupOf E := by
    change (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E = _
    rw [←source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne]
  obtain ⟨_,hB,_,hinter⟩ := source_amalgam_plane_image_and_overlap d earlier hq chosen structural alternatives F hne K hKH
  have hA := source_amalgam_actor_kernel d earlier hq chosen structural alternatives F hne K hKH hKN hout model
  rw [←hBP] at hB hinter
  have model_image (C : Subgroup E) (hc : IsPGroup 2 (q.subgroupMap C).ker)
      (hm : Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3))) :
      Nonempty (((C.map q) ⧸ pCore 2 (C.map q)) ≃* Equiv.Perm (Fin 3)) := by
    obtain ⟨ec⟩ := hm
    exact ⟨((q.subgroupMap C).pCoreQuotientEquiv (q.subgroupMap_surjective C) hc).symm.trans ec⟩
  refine ⟨⟨?_,model_image A hA hG.quotient_left,model_image B hB hG.quotient_right,?_⟩,?_⟩
  · rw [←Subgroup.map_sup,hG.generated,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  · exact ⟨(T.subtype (sylow_le_amalgamGroup F L K)).mapSurjective
      (QuotientGroup.mk'_surjective _),hinter⟩
  · apply pCoreIn_image_ne_of_local_kernels 2 q B A hB hA
      (hG.symm.local_twoCore_le_intersection.trans inf_le_right)
      (hG.local_twoCore_le_intersection.trans inf_le_right)
    intro he
    apply hneq
    have hh := congrArg (map E.subtype) he
    rwa [pCoreIn_subgroupOf 2 _ E le_sup_right,pCoreIn_subgroupOf 2 _ E le_sup_left,
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show F.I₂ L ⊔ (T : Subgroup G) ≤ E from le_sup_right)),
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans (show K ⊔ (T : Subgroup G) ≤ E from le_sup_left))] at hh

/-- The literal solvable source configuration supplies a faithful Goldschmidt
triple with distinct cores in Ke/C_Ke(Ue). -/
theorem source_solvable_quotient_amalgam
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let A := (K ⊔ (T : Subgroup G)).subgroupOf E
      let B := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧
      (B.map q).pCoreIn 2 ≠ (A.map q).pCoreIn 2 ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      pCore 2 (AmalgamQuotient F L K) = ⊥ ∧
      ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
        (centralizer (amalgamModule F L K : Set G)) := by
  obtain ⟨g,l,e,_,_,hl,he,heI,heT,_,hKH,hKN,_,_,hKT,hout,hKe,hr,hcore,hJ,hneq⟩ :=
    source_solvable_shifted_quotients d earlier hq chosen structural alternatives F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  obtain ⟨hgold,hunequal⟩ := source_amalgam_quotient_goldschmidt d earlier hq chosen structural alternatives F hne K hKH hKN hout hKT hneq
  refine ⟨l,e,hl,he,heI,heT,hgold,hunequal,hKe,hr,hcore,?_⟩
  intro hJC
  apply hJ
  let E := amalgamGroup F L K
  let A0 := K ⊔ (T : Subgroup G)
  let A := A0.subgroupOf E
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  have hA := source_amalgam_actor_kernel d earlier hq chosen structural alternatives F hne K hKH hKN hout hKT
  have hker : (q.subgroupMap A).ker ≤ pCore 2 A := le_sSup ⟨inferInstance,hA⟩
  intro x hx
  have hJT : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le fun _ h => h.1
  have hxT : x ∈ (T : Subgroup G) := hJT hx
  let a : A := ⟨⟨x,sylow_le_amalgamGroup F L K hxT⟩,(show (T:Subgroup G) ≤ A0 from le_sup_right) hxT⟩
  have hak : a ∈ (q.subgroupMap A).ker := by
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff _).mpr
    intro v hv
    exact Subtype.ext (hJC hx v hv)
  have hm := mem_map_of_mem A.subtype (hker hak)
  change (a:E) ∈ A.pCoreIn 2 at hm
  rw [pCoreIn_subgroupOf 2 A0 E le_sup_left] at hm
  exact hm


omit d earlier hq structural alternatives hne in
/-- The original Thompson escape supplies an FF offender on the orbit module. -/
theorem amalgam_isFFModule (K : Subgroup G)
    (hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)))
    (hJ : ¬ Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (amalgamModule F L K : Set G)) :
    let _ := hr.elementary
    Representation.BinaryOffender.IsFFModule
      (Representation.NormalElementaryQuotient.representation
        ((amalgamModule F L K).subgroupOf (amalgamGroup F L K))
        (QuotientGroup.mk' (amalgamKernel F L K)) (QuotientGroup.mk'_surjective _)
        (QuotientGroup.ker_mk' _)) := by
  let := hr.elementary
  let E := amalgamGroup F L K
  let Ue := amalgamModule F L K
  let S := T.subtype (sylow_le_amalgamGroup F L K)
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  have hU : Ue ≤ E := conjugateSpanBy_le_self
    ((F.le_seed 1).trans (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K)))
  apply Representation.NormalElementaryQuotient.isFFModule_of_thompson_not_le
    (Ue.subgroupOf E) q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) S
    (hr.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal S))
  intro h
  apply hJ
  have hm : (Stellmacher.elementaryAbelianMaxJ (S : Subgroup E)).map E.subtype =
      Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←Stellmacher.elementaryAbelianMaxJ_map_injective E.subtype E.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le (sylow_le_amalgamGroup F L K)
  rw [←hm]
  rintro x ⟨a,ha,rfl⟩ v hv
  have hc : a ∈ amalgamKernel F L K := (QuotientGroup.eq_one_iff _).mp (h ha)
  exact congrArg Subtype.val (hc ⟨v,hU hv⟩ hv)

/-- The actual S₃×S₃ branch produces the faithful FF action and both
Goldschmidt vertices in its original centralizer quotient. -/
theorem source_solvable_goldschmidt_ff
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let A := (K ⊔ (T : Subgroup G)).subgroupOf E
      let B := (F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E
      ∃ hr : IsPReduced 2 ((amalgamModule F L K).subgroupOf E),
      let _ := hr.elementary
      ChapterF.IsGoldschmidtTriple (A.map q) (B.map q) ∧
      (B.map q).pCoreIn 2 ≠ (A.map q).pCoreIn 2 ∧
      pCore 2 (AmalgamQuotient F L K) = ⊥ ∧
      E ≤ centralizer ({e} : Set G) ∧
      Representation.BinaryOffender.IsFFModule
        (Representation.NormalElementaryQuotient.representation
          ((amalgamModule F L K).subgroupOf E) q (QuotientGroup.mk'_surjective _)
          (QuotientGroup.ker_mk' _)) := by
  obtain ⟨l,e,hl,he,heI,heT,hgold,hneq,hE,hr,hcore,hJ⟩ :=
    source_solvable_quotient_amalgam d earlier hq chosen structural alternatives F hne hZ model hI
  exact ⟨l,e,hl,he,heI,heT,hr,hgold,hneq,hcore,hE,amalgam_isFFModule chosen F _ hr hJ⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
