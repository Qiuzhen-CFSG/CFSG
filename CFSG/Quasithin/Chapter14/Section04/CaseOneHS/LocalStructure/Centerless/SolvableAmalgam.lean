module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.SolvableShiftedRow
public import CFSG.Quasithin.ChapterF.Section06.Basic
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# The original solvable amalgam and its plane image

The marked plane action identifies P/O₂(P) with S₃. Its Sylow index is
three, and the original conjugator escapes H, so P ∩ H is precisely T.
Consequently the two actual Sylow supplements KT and I₂T form a
Goldschmidt triple inside their join Ke, with the original intersection.

The orbit module Ue contains V₂. Its action kernel therefore restricts to
a two-group on the plane vertex, preserving that vertex's S₃ core quotient.
The same kernel centralizes V₁ and hence lies in H. This proves that the
whole overlap in Ke/C_Ke(Ue) is the image of T; no general quotient/intersection
identity is assumed. The final application uses the same shifted involution
and normal closure already constructed from the original S₃×S₃ model.

The KT action-kernel comparison, unequal-core transport to this quotient,
the F.6.18 contradiction and full source_centerless assembly remain with
qt-d-hs-centerless-source. The centerlessness-dependent later action theorem
is not used. Source: Aschbacher--Smith 14.3.31, printed p.1003, and the
preceding plane action in 12.8.9, printed p.853, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
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

omit alternatives hne in
/-- The original plane parabolic quotient is S₃, and its intersection with
the point normalizer is exactly the original Sylow subgroup. -/
theorem source_parabolic_quotient_and_intersection :
    Nonempty ((F.P L ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3)) ∧
      F.P L ⊓ F.H = (T : Subgroup G) := by
  let := chosen.elementary
  let h := higherRankHypothesis d earlier hq chosen
  let f := F.binaryPermutationAction (by decide) L chosen.normalizes
  have hf : Function.Surjective f := F.binaryPermutationAction_surjective
    (by decide) L chosen.normalizes (h.binarySeedAction_surjective F)
  have hk : f.ker = pCore 2 (F.P L) :=
    (F.binaryPermutationAction_ker (by decide) L chosen.normalizes).trans
      (F.binaryPlaneAction_ker_eq_twoCore (by decide) L chosen.normalizes
        (h.binarySeedAction_surjective F) (h.centralizer_LT structural))
  let e : (F.P L ⧸ pCore 2 (F.P L)) ≃* Equiv.Perm (Fin 3) :=
    (QuotientGroup.quotientMulEquivOfEq hk).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  refine ⟨⟨e⟩,?_⟩
  have hTP := F.binary_sylow_le_P L
  have hi : (T : Subgroup G).relIndex (F.P L) = 3 :=
    SymmetricThreeTwoCore.sylow_index_three e (T.subtype hTP)
  have hTC : (T : Subgroup G) ≤ F.P L ⊓ F.H := le_inf hTP (F.invariant 1)
  have hprod := relIndex_mul_relIndex (T : Subgroup G) (F.P L ⊓ F.H) (F.P L) hTC inf_le_left
  rw [hi] at hprod
  have hproper : (F.P L ⊓ F.H).relIndex (F.P L) ≠ 1 := by
    intro hh
    obtain ⟨g,hgP,hgH⟩ := source_conjugator d earlier hq chosen structural F
    exact hgH (((relIndex_eq_one.mp hh) hgP).2)
  have hone : (T : Subgroup G).relIndex (F.P L ⊓ F.H) = 1 := by
    rcases (Nat.prime_mul_iff.mp (hprod ▸ Nat.prime_three)) with hh | hh
    · exact (hproper hh.2).elim
    · exact hh.2
  exact le_antisymm (relIndex_eq_one.mp hone) hTC

omit [Finite G] d earlier hq chosen structural alternatives F hne in
private theorem relative_core_quotient {A E : Subgroup G} (hAE : A ≤ E)
    (model : Nonempty ((A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))) :
    Nonempty (((A.subgroupOf E) ⧸ pCore 2 (A.subgroupOf E)) ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨e⟩ := model
  let j : A.subgroupOf E ≃* A := subgroupOfEquivOfLe hAE
  exact ⟨(QuotientGroup.congr _ _ j (pCore_map_iso 2 j)).trans e⟩

/-- The actual two Sylow supplements form a Goldschmidt triple in Ke.
The later quotient still uses its separate literal action centralizer. -/
theorem source_solvable_ambient_goldschmidt (K : Subgroup G) (hKH : K ≤ F.H)
    (model : Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
      pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* Equiv.Perm (Fin 3))) :
    ChapterF.IsGoldschmidtTriple
      ((K ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K))
      ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)) := by
  let A := K ⊔ (T : Subgroup G)
  let B := F.I₂ L ⊔ (T : Subgroup G)
  let E := amalgamGroup F L K
  have hAE : A ≤ E := le_sup_left
  have hBE : B ≤ E := le_sup_right
  obtain ⟨hP,hPH⟩ := source_parabolic_quotient_and_intersection d earlier hq chosen structural F
  have hBP : B = F.P L := (source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne).symm
  have hAB : A ⊓ B = (T : Subgroup G) := by
    apply le_antisymm
    · have hh : A ⊓ B ≤ F.P L ⊓ F.H :=
        le_inf (inf_le_right.trans hBP.le) (inf_le_left.trans (sup_le hKH (F.invariant 1)))
      exact hPH ▸ hh
    · exact le_inf le_sup_right le_sup_right
  have hBmodel : Nonempty ((B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) := hBP ▸ hP
  refine ⟨?_,relative_core_quotient hAE model,relative_core_quotient hBE hBmodel,?_⟩
  · rw [←subgroupOf_sup hAE hBE]
    exact subgroupOf_self E
  · refine ⟨T.subtype (sylow_le_amalgamGroup F L K),?_⟩
    ext x
    change (x:G) ∈ A ⊓ B ↔ (x:G) ∈ (T : Subgroup G)
    rw [hAB]

/-- The plane vertex keeps its S₃ quotient and the entire overlap remains
the image of T in the literal action quotient Ke/C_Ke(Ue). -/
theorem source_amalgam_plane_image_and_overlap (K : Subgroup G) (hKH : K ≤ F.H) :
    let E := amalgamGroup F L K
    let q := QuotientGroup.mk' (amalgamKernel F L K)
    let A := (K ⊔ (T : Subgroup G)).subgroupOf E
    let B := (F.P L).subgroupOf E
    F.Vi 2 ≤ amalgamModule F L K ∧ IsPGroup 2 (q.subgroupMap B).ker ∧
      Nonempty (((B.map q) ⧸ pCore 2 (B.map q)) ≃* Equiv.Perm (Fin 3)) ∧
      A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf E).map q := by
  let := chosen.elementary
  let E := amalgamGroup F L K
  let Ue := amalgamModule F L K
  let q := QuotientGroup.mk' (amalgamKernel F L K)
  let A := (K ⊔ (T : Subgroup G)).subgroupOf E
  let B := (F.P L).subgroupOf E
  have hPE : F.P L ≤ E := by
    rw [source_parabolic_eq_I₂_sylow d earlier hq chosen structural alternatives F hne]
    exact le_sup_right
  have h1E : F.Vi 1 ≤ E := (F.le_seed 1).trans (chosen.le_sylow.trans (sylow_le_amalgamGroup F L K))
  have hUE : Ue ≤ E := conjugateSpanBy_le_self h1E
  have h1U : F.Vi 1 ≤ Ue := le_conjugateSpanBy _ _
  have hPU : F.Vi 2 ≤ Ue := by
    obtain ⟨g,hgP,hgH⟩ := source_conjugator d earlier hq chosen structural F
    rw [←F.binary_plane_point_span (by decide) L chosen.normalizes g hgP hgH]
    exact sup_le h1U (conjugate_le_of_normalizes h1U g
      (le_normalizer_conjugateSpanBy _ _ (hPE hgP)))
  have hkerC : q.ker ≤ (centralizer (Ue : Set G)).subgroupOf E := by
    rw [QuotientGroup.ker_mk']
    intro x hx v hv
    exact congrArg Subtype.val (hx ⟨v,hUE hv⟩ hv)
  have hkerH : q.ker ≤ F.H.subgroupOf E :=
    hkerC.trans (comap_mono ((centralizer_le h1U).trans (Subgroup.centralizer_le_normalizer _)))
  let r := q.subgroupMap B
  have hkr : IsPGroup 2 r.ker := by
    let j := E.subtype.comp B.subtype
    have hj : Function.Injective j := E.subtype_injective.comp B.subtype_injective
    apply ((isPGroup_pCoreIn 2 (F.P L)).comap_of_injective j hj).to_le
    intro x hx
    change ((x : E) : G) ∈ (F.P L).pCoreIn 2
    let h := higherRankHypothesis d earlier hq chosen
    rw [←(F.binary_parabolic_core (by decide) L chosen.normalizes
      (h.binarySeedAction_surjective F) (h.centralizer_LT structural)).1]
    have hxq : q (x:E) = 1 := congrArg Subtype.val hx
    exact ⟨x.property,fun v hv => hkerC hxq v (hPU hv)⟩
  obtain ⟨hP,hPH⟩ := source_parabolic_quotient_and_intersection d earlier hq chosen structural F
  obtain ⟨eB⟩ := relative_core_quotient hPE hP
  refine ⟨hPU,hkr,⟨(r.pCoreQuotientEquiv (q.subgroupMap_surjective B) hkr).symm.trans eB⟩,?_⟩
  apply le_antisymm
  · rintro x ⟨⟨a,ha,rfl⟩,b,hb,hba⟩
    have hab : a⁻¹ * b ∈ q.ker := by
      change q (a⁻¹*b) = 1
      rw [map_mul,map_inv,hba,inv_mul_cancel]
    have haH : (a:G) ∈ F.H := (sup_le hKH (F.invariant 1)) ha
    have hbH : (b:G) ∈ F.H := by
      have hh := F.H.mul_mem haH (hkerH hab)
      change (a:G) * ((a:G)⁻¹ * (b:G)) ∈ F.H at hh
      simpa only [mul_inv_cancel_left] using hh
    refine ⟨b,?_,hba⟩
    change (b:G) ∈ (T : Subgroup G)
    exact hPH ▸ (show (b:G) ∈ F.P L ⊓ F.H from ⟨hb,hbH⟩)
  · exact le_inf (map_mono (comap_mono le_sup_right))
      (map_mono (comap_mono (F.binary_sylow_le_P L)))

/-- Apply the ambient Goldschmidt triple to the very same shifted actor
constructed from the original solvable model and nontrivial center. -/
theorem source_solvable_ambient_amalgam
    (hZ : F.ZU ≠ F.Vi 1)
    (model : Nonempty (F.TerminalHdot ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))))
    (hI : Chapter12.Section08.centerIn (F.I₂ L) ≠ ⊥) :
    ∃ l e : G, l ∈ L ∧ orderOf e = 2 ∧ e ∈ Chapter12.Section08.centerIn (F.I₂ L) ∧
      e ∈ sylowOmega T ∧
      let K := conjugateSpanBy (zpowers (l⁻¹ * e * l)) F.H
      ChapterF.IsGoldschmidtTriple
        ((K ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K))
        ((F.I₂ L ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)) ∧
      (F.I₂ L ⊔ (T : Subgroup G)).pCoreIn 2 ≠ (K ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      amalgamGroup F L K ≤ centralizer ({e} : Set G) ∧
      IsPReduced 2 ((amalgamModule F L K).subgroupOf (amalgamGroup F L K)) ∧
      pCore 2 (AmalgamQuotient F L K) = ⊥ ∧
      let q := QuotientGroup.mk' (amalgamKernel F L K)
      let A := (K ⊔ (T : Subgroup G)).subgroupOf (amalgamGroup F L K)
      let B := (F.P L).subgroupOf (amalgamGroup F L K)
      F.Vi 2 ≤ amalgamModule F L K ∧ IsPGroup 2 (q.subgroupMap B).ker ∧
        Nonempty (((B.map q) ⧸ pCore 2 (B.map q)) ≃* Equiv.Perm (Fin 3)) ∧
        A.map q ⊓ B.map q = ((T : Subgroup G).subgroupOf (amalgamGroup F L K)).map q := by
  obtain ⟨g,l,e,_,_,hl,he,heI,heT,_,hKH,_,_,_,hKT,_,hKe,hr,hcore,_,hneq⟩ :=
    source_solvable_shifted_quotients d earlier hq chosen structural alternatives F hne hZ model hI
  exact ⟨l,e,hl,he,heI,heT,
    source_solvable_ambient_goldschmidt d earlier hq chosen structural alternatives F hne _ hKH hKT,
    hneq,hKe,hr,hcore,
    source_amalgam_plane_image_and_overlap d earlier hq chosen structural alternatives F hne _ hKH⟩

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Centerless
