module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableRecognition
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison.CoreUpgrade
public import Theory.GroupTheory.CComponent.SimpleCoreImage
public import Theory.GroupTheory.SolvableNormalizerObstruction
public import Theory.GroupTheory.PPrimeCoreSurjection

/-!
# The original action quotient and its faithful residual

The solvable action kernel lies in O₃′(Ke), since the latter quotient is
simple and nonsolvable. A perfect subnormal component retains its simple
two-core quotient in both images. The recognized prime-to-three image
therefore gives an actual subnormal PSL₃(2) in the action quotient. The
Goldschmidt comparison removes its remaining odd kernel.

Thus C_Ke(Ue) = O₃′(Ke), the literal action quotient is PSL₃(2), and the
same original component is the solvable residual of Ke. All original actor,
vertex, involution and reduced-module data are retained for H.5.5.
Source: Aschbacher--Smith 14.3.31, printed p.1003; F.6.11 and F.6.18.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
open Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.QuotientComparison

private theorem action_equiv_of_prime_and_component
    {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]
    {A B : Subgroup E} (h : ChapterF.IsGoldschmidtTriple A B)
    (f : E →* D) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hD : ChapterF.IsGoldschmidtTriple (A.map f) (B.map f)) (hc : pCore 2 D = ⊥)
    (e : (E ⧸ pPrimeCore 3 E) ≃* Matrix.PSL3Two.PSL)
    (C : Subgroup E) (hC : C.IsSubnormal) [Group.IsPerfect C]
    [IsSimpleGroup (C ⧸ pCore 2 C)]
    (ht : C.map (QuotientGroup.mk' (pPrimeCore 3 E)) = ⊤) :
    f.ker = pPrimeCore 3 E ∧ Nonempty (D ≃* Matrix.PSL3Two.PSL) ∧
      C = solvableResidual E := by
  let R := pPrimeCore 3 E
  let p := QuotientGroup.mk' R
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect Matrix.PSL3Two.PSL := Atlas.psl_perfect (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup (E ⧸ R) := e.isSimpleGroup
  let : Group.IsPerfect (E ⧸ R) := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hker : f.ker ≤ R := by
    have hh := solvable_normal_le_simple_ker p (QuotientGroup.mk'_surjective _)
      (Group.IsPerfect.not_isSolvable _) f.ker
    rwa [QuotientGroup.ker_mk'] at hh
  let π : D →* E ⧸ R := f.liftOfSurjective hf ⟨p,by simpa only [p,QuotientGroup.ker_mk'] using hker⟩
  have hπf (x : E) : π (f x) = p x :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective R y
    exact ⟨f x,hπf x⟩
  have hπker : π.ker.comap f = R := by
    ext x
    change π (f x) = 1 ↔ x ∈ R
    rw [hπf]
    exact QuotientGroup.eq_one_iff _
  have hmap : R.map f = π.ker := by
    exact (congrArg (map f) hπker).symm.trans (map_comap_eq_self_of_surjective hf _)
  have hcop : Nat.Coprime 3 (Nat.card π.ker) := by
    rw [←hmap]
    exact pPrimeCore_coprime_card.of_dvd_right (card_map_dvd _ _)
  have hpbot : pPrimeCore 3 (E ⧸ R) = ⊥ :=
    pPrimeCore_eq_bot_of_equiv e (pPrimeCore_eq_bot_of_simple
      (by rw [Matrix.PSL3Two.card_PSL]; decide))
  have hkπ : π.ker = pPrimeCore 3 D := by
    have hh := pPrimeCore_comap_eq_of_surjective_coprime 3 π hπ hcop
    rwa [hpbot] at hh
  let ep : (D ⧸ pPrimeCore 3 D) ≃* Matrix.PSL3Two.PSL :=
    (QuotientGroup.quotientMulEquivOfEq hkπ.symm).trans
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).trans e)
  let : Group.IsSolvable p.ker := by
    rw [QuotientGroup.ker_mk']
    exact h.primeToThreeCore_solvable
  let j := hC.simpleCoreImageEquiv C p (QuotientGroup.mk'_surjective _)
    h.primeToThreeCore_quotient_twoCore_eq_bot
  let k := hC.simpleCoreImageEquiv C f hf hc
  let eC : C.map f ≃* Matrix.PSL3Two.PSL :=
    k.symm.trans (j.trans ((MulEquiv.subgroupCongr ht).trans (topEquiv.trans e)))
  obtain ⟨hzero,hmodel⟩ := plus_equiv_of_subnormal_and_bang hD hc ep (C.map f) (hC.map hf) eC
  have hfker : f.ker = R := by
    have hh := pPrimeCore_comap_eq_of_surjective_coprime 3 f hf
      (pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le hker))
    rwa [hzero] at hh
  have hsup : C ⊔ R = ⊤ := by
    change C.map p = ⊤ at ht
    have hh := congrArg (comap p) ht
    simpa only [comap_map_eq,p,QuotientGroup.ker_mk',comap_top] using hh
  let : Group.IsSolvable R := h.primeToThreeCore_solvable
  exact ⟨hfker,hmodel,hC.eq_solvableResidual_of_sup_eq_top R hsup⟩

open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual orbit-action quotient is PSL₃(2); its literal centralizer
kernel equals O₃′(Ke), and the selected component is the solvable residual. -/
theorem source_solvable_action_recognition (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (classification : EarlierFaithfulClassification G (T : Subgroup G))
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      let E := amalgamGroup F L K
      K ≤ F.H ∧ F.H ≤ normalizer (K : Set G) ∧ K ≤ centralizer (F.ZU : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 3)) ∧
      E ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf E) ∧
      amalgamKernel F L K = pPrimeCore 3 E ∧
      Nonempty (AmalgamQuotient F L K ≃* Matrix.PSL3Two.PSL) ∧
      ChapterF.IsGoldschmidtTriple
        (((K ⊔ (T : Subgroup G)).subgroupOf E).map (QuotientGroup.mk' (amalgamKernel F L K)))
        (((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E).map (QuotientGroup.mk' (amalgamKernel F L K))) ∧
      ∃ C : Subgroup G, C ∈ Chapter1.cComponentsIn E ∧
        C ∈ MainForward.faithfulLocalComponents T ∧
        C.subgroupOf E = solvableResidual E := by
  obtain ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hKT,hout,hE,hr,⟨ep⟩,
      C,hC,hfaith,_,_,_,ht⟩ :=
    source_solvable_quotient_recognition_with_actor d earlier hq chosen structural alternatives
      classification F hne hZ model hI
  let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
  let E := amalgamGroup F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  have hs := source_seed_exclusion_of_solvable_model d earlier hq chosen structural alternatives F hne model
  have hneq := (source_contrary_thompson_escape d earlier hq chosen structural alternatives F hne hs hI K hout).2
  have hg := source_solvable_ambient_goldschmidt d earlier hq chosen structural alternatives F hne K hKH hKT
  have hqg := (source_amalgam_quotient_goldschmidt d earlier hq chosen structural alternatives F hne
    K hKH hKN hout hKT hneq).1
  have ha := source_amalgam_actor_kernel d earlier hq chosen structural alternatives F hne K hKH hKN hout hKT
  have hb : IsPGroup 2 (q.subgroupMap ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf E)).ker := by
    have hh := (source_amalgam_plane_image_and_overlap d earlier hq chosen structural alternatives F hne K hKH).2.1
    rwa [source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne] at hh
  let : Group.IsSolvable q.ker := hg.action_kernel_solvable q ha hb
  have hh := (Chapter1.Section02.Adequate.mem_faithfulLocalComponents_iff T C).mp hfaith
  have hm := (classification C hh.1 hh.2).1
  let j : C.subgroupOf E ≃* C := subgroupOfEquivOfLe hC.1
  let jq := QuotientGroup.congr _ _ j (pCore_map_iso 2 j)
  let : IsSimpleGroup ((C.subgroupOf E) ⧸ pCore 2 (C.subgroupOf E)) := by
    rcases hm with ha | ha <;> obtain ⟨a⟩ := ha
    · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
      exact (jq.trans a).isSimpleGroup
    · let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
      exact (jq.trans a).isSimpleGroup
  let := hC.2.perfect
  obtain ⟨hk,hmodel,hres⟩ := action_equiv_of_prime_and_component hg q (QuotientGroup.mk'_surjective _)
    hqg hr.quotient_pCore_eq_bot ep (C.subgroupOf E) hC.2.subnormal ht
  rw [QuotientGroup.ker_mk'] at hk
  exact ⟨l,e,hl,he,heI,heT,hKH,hKN,hKC,hK,hE,hr,hk,hmodel,hqg,C,hC,hfaith,hres⟩
end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
