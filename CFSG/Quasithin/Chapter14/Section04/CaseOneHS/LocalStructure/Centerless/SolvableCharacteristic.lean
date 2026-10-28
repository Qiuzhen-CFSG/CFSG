module
public import Theory.GroupTheory.SymmetricThreeOrbitAction
public import Theory.GroupTheory.CharacteristicTwoSectionObstruction
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree.DistinctCores
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvablePrimeQuotient

/-!
# Characteristic two and the solvable Goldschmidt exclusions

The original shifted actor K centralizes Z(U), and its kernel on U is a
two-group. The marked plane has H-span U. Applying the orbit-action
criterion to the literal map K → Ke/C_Ke(Ue) proves that its image K⁺
has F* = O₂ and still has S₃ quotient over O₂.

F.6.11 makes the next quotient by O₃′ injective on K⁺, since it is
contained in an actual Goldschmidt vertex and O₂(Ke/C_Ke(Ue)) = 1.
Thus both properties survive on the same actor in the second quotient.
The distinct cores exclude the cyclic overlap in F.6.18(1). Its two
solvable models in F.6.18(2) have normal three-groups with two-group
quotients, contradicting the characteristic-two S₃ actor.

The source applications choose the original shifted involution only once
and retain its literal centralizer quotient and reduced orbit module.
The F.6.18 cover comparison, remaining nonsolvable alternatives and final
dimension contradiction are still required for source_centerless.
Source: Aschbacher--Smith 14.3.31, printed p.1003, and F.6.18, pp.309--310.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
private theorem prime_actor_structure
    {D : Type u} [Group D] [Finite D] (A B C : Subgroup D)
    (h : ChapterF.IsGoldschmidtTriple A B) (hcore : pCore 2 D = ⊥)
    (hCA : C ≤ A) (hfit : generalizedFitting C = pCore 2 C)
    (model : Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3))) :
    let p := QuotientGroup.mk' (pPrimeCore 3 D)
    generalizedFitting (C.map p) = pCore 2 (C.map p) ∧
      Nonempty (((C.map p) ⧸ pCore 2 (C.map p)) ≃* Equiv.Perm (Fin 3)) := by
  let p := QuotientGroup.mk' (pPrimeCore 3 D)
  have hk : (p.subgroupMap C).ker = ⊥ := by
    rw [h.primeToThreeCore_subgroup_kernel C hCA,hcore,bot_subgroupOf]
  let e : C ≃* C.map p := MulEquiv.ofBijective (p.subgroupMap C)
    ⟨(p.subgroupMap C).ker_eq_bot_iff.mp hk,p.subgroupMap_surjective C⟩
  constructor
  · have hm := congrArg (fun N : Subgroup C => N.map e.toMonoidHom) hfit
    rwa [map_generalizedFitting_equiv,pCore_map_iso] at hm
  · exact ⟨(QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm.trans model.some⟩

variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
include d earlier hq chosen structural alternatives hne

/-- The actual image of the shifted actor is characteristic two with S₃ core quotient. -/
theorem source_amalgam_actor_structure (K : Subgroup G)
    (hKH : K ≤ F.H) (hKN : F.H ≤ normalizer (K : Set G))
    (hKC : K ≤ centralizer (F.ZU : Set G))
    (model : Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3))) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let Kplus := (K.subgroupOf E).map q
    IsPGroup 2 (q.subgroupMap (K.subgroupOf E)).ker ∧
      generalizedFitting Kplus = pCore 2 Kplus ∧
      Nonempty ((Kplus ⧸ pCore 2 Kplus) ≃* Equiv.Perm (Fin 3)) := by
  let := chosen.elementary
  let E := amalgamGroup F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  have hKE : K ≤ E := le_sup_left.trans le_sup_left
  let j : K ≃* K.subgroupOf E := (subgroupOfEquivOfLe hKE).symm
  let f := (q.subgroupMap (K.subgroupOf E)).comp j.toMonoidHom
  have hfaith : IsPGroup 2 ((centralizer (F.U : Set G)).subgroupOf K) := by
    let i := inclusion hKH
    apply (pCore_isPGroup.comap_of_injective i (inclusion_injective hKH)).to_le
    intro k hk
    apply source_center_centralizing_kernel_le_core d earlier hq chosen structural alternatives F hne
    refine ⟨hKC k.property,?_⟩
    apply (F.mem_uhatAction_ker_iff _).mpr
    intro v hv
    have hc : v * (k:G) = (k:G) * v := hk v hv
    change (k:G)*v*(k:G)⁻¹*v⁻¹ ∈ F.ZU
    rw [←hc]
    simpa only [mul_assoc,mul_inv_cancel_left,mul_inv_cancel,one_mul] using F.ZU.one_mem
  have hs := SymmetricThreeTwoCore.orbit_action_structure
    F.H F.U (F.Vi 2) K F.U_le_H hKH (le_normalizer_conjugateSpanBy V F.H) hKN
    (source_closure d earlier hq chosen structural alternatives F hne).1
    (source_seed_geometry d earlier hq chosen F).2.1 hKC hfaith model.some f
    ((q.subgroupMap_surjective _).comp j.surjective) (by
    intro k hk v hv
    have hqk : q (j k : E) = 1 := congrArg Subtype.val hk
    have hcentral : (j k : E) ∈ amalgamKernel F L K := (QuotientGroup.eq_one_iff _).mp hqk
    have hplane : F.Vi 2 ≤ amalgamModule F L K :=
      (source_amalgam_plane_image_and_overlap d earlier hq chosen structural alternatives F hne K hKH).1
    have hUE : amalgamModule F L K ≤ E := conjugateSpanBy_le_self
      ((F.le_seed 1).trans (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K)))
    exact congrArg Subtype.val (hcentral ⟨v,hUE (hplane hv)⟩ (hplane hv))
    )
  refine ⟨?_,hs.2⟩
  let r : f.ker →* (q.subgroupMap (K.subgroupOf E)).ker :=
    j.toMonoidHom.subgroupComap (q.subgroupMap (K.subgroupOf E)).ker
  exact hs.1.of_surjective r
    (j.toMonoidHom.subgroupComap_surjective_of_surjective
      (q.subgroupMap (K.subgroupOf E)).ker j.surjective)

/-- The same shifted actor remains characteristic two with S₃ quotient
in both original action quotients. -/
theorem source_solvable_characteristic_amalgam
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let A := ((K ⊔ (T : Subgroup G)).subgroupOf E).map q
      let B := ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map q
      let C := (K.subgroupOf E).map q
      let p := QuotientGroup.mk' (pPrimeCore 3 (AmalgamQuotient F L K))
      ChapterF.IsGoldschmidtTriple A B ∧ B.pCoreIn 2 ≠ A.pCoreIn 2 ∧
      pCore 2 (AmalgamQuotient F L K) = ⊥ ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      generalizedFitting C = pCore 2 C ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* Equiv.Perm (Fin 3)) ∧
      generalizedFitting (C.map p) = pCore 2 (C.map p) ∧
      Nonempty (((C.map p) ⧸ pCore 2 (C.map p)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨g,l,e,_,_,hl,he,heI,heT,_,hKH,hKN,hKC,hK,hKT,hout,hE,hr,hcore,_,hneq⟩ :=
    source_solvable_shifted_quotients d earlier hq chosen structural alternatives F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  obtain ⟨hg,hn⟩ := source_amalgam_quotient_goldschmidt d earlier hq chosen structural alternatives F hne
    K hKH hKN hout hKT hneq
  obtain ⟨_,hf,hm⟩ := source_amalgam_actor_structure d earlier hq chosen structural alternatives F hne
    K hKH hKN hKC hK
  exact ⟨l,e,hl,he,heI,heT,hg,hn,hcore,hE,hr,hf,hm,
    prime_actor_structure _ _ _ hg hcore (map_mono (comap_mono le_sup_left)) hf hm⟩

/-- The literal prime-to-three quotient cannot have either solvable model
from F.6.18(2), nor the cyclic Sylow overlap from F.6.18(1). -/
theorem source_solvable_primeToThree_row_exclusions
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let A := ((K ⊔ (T : Subgroup G)).subgroupOf E).map q
      let B := ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map q
      let C := (K.subgroupOf E).map q
      let D := AmalgamQuotient F L K ⧸ pPrimeCore 3 (AmalgamQuotient F L K)
      let p := QuotientGroup.mk' (pPrimeCore 3 (AmalgamQuotient F L K))
      ChapterF.IsGoldschmidtTriple (A.map p) (B.map p) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      generalizedFitting (C.map p) = pCore 2 (C.map p) ∧
      Nonempty (((C.map p) ⧸ pCore 2 (C.map p)) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ Nonempty ((A.map p ⊓ B.map p : Subgroup D) ≃* Multiplicative (ZMod 2)) ∧
      ¬ (Nonempty (D ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∨
        ∃ N : Subgroup D, ∃ _ : N.Normal,
          IsExtraspecial 3 N ∧ Nat.card N = 27 ∧ Monoid.exponent N = 3 ∧
          Nonempty ((D ⧸ N) ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) := by
  obtain ⟨l,e,hl,he,heI,heT,hg,hn,hcore,hE,hr,hf,hm,hfp,hmp⟩ :=
    source_solvable_characteristic_amalgam d earlier hq chosen structural alternatives F hne hZ model hI
  refine ⟨l,e,hl,he,heI,heT,hg.quotient_primeToThreeCore_of_distinct_cores (Ne.symm hn),
    hE,hr,hfp,hmp,hg.primeToThreeCore_intersection_not_cyclic_two (Ne.symm hn),?_⟩
  rintro (hp | ⟨N,hN,_,hc,_,⟨eN⟩⟩)
  · exact SymmetricThreeTwoCore.characteristic_two_not_symmetric_three_product _ hfp hmp.some hp
  · let := hN
    have hN3 : IsPGroup 3 N := IsPGroup.of_card (n := 3) hc
    have hQ2 : IsPGroup 2 (_ ⧸ N) := by
      apply (IsPGroup.of_card (n := 2) (G := Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ?_).of_equiv eN.symm
      simp
    exact SymmetricThreeTwoCore.characteristic_two_not_three_by_two _ hfp hmp.some N hN3 hQ2

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
