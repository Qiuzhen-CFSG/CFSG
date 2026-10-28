module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.PResidual.PerfectCover
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Embedding the actual residual of an involution centralizer

Set B = O²(C_L(z)), flattened into the ambient group. We prove equality
with the literal nested-subgroup construction, then derive T-invariance,
the C-component condition inside BT and its nontrivial two-core. The
central involution itself witnesses that last condition. The A₆ quotient
supplies quasisimplicity without a classification assumption.

The full universal A.3.12 and A.3.8 implications give a unique containing
component inside C_G(z), normal relative to that centralizer. The output
retains the entire 22-case list on the literal images modulo O₂(C_G(z)).
Filtering that list is a separate model calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Proposition 8.2.2(1), p.715, and Lemma 1.2.4, p.505.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

def localResidual (L : Subgroup G) (z : G) : Subgroup G :=
  (pResidual 2 (L ⊓ centralizer ({z} : Set G) : Subgroup G)).map
    (L ⊓ centralizer ({z} : Set G)).subtype

omit [Finite G] in
/-- The embedded residual remains inside the literal centralizer intersection. -/
theorem localResidual_le (L : Subgroup G) (z : G) :
    localResidual L z ≤ L ⊓ centralizer ({z} : Set G) := map_subtype_le _

/-- Flattening agrees with O² of the centralizer taken inside L. -/
theorem localResidual_eq_intrinsic (L : Subgroup G) (z : G) :
    localResidual L z =
      (pResidual 2 ((centralizer ({z} : Set G)).subgroupOf L)).map
        (L.subtype.comp ((centralizer ({z} : Set G)).subgroupOf L).subtype) := by
  rw [← map_map, map_embedded_pResidual, subgroupOf_map_subtype, inf_comm]
  rfl

omit [Finite G] in
/-- T preserves the residual when it normalizes L and centralizes z. -/
theorem localResidual_invariant {T L : Subgroup G} {z : G}
    (hTL : T ≤ normalizer L) (hTC : T ≤ centralizer ({z} : Set G)) :
    T ≤ normalizer (localResidual L z) := by
  let D := L ⊓ centralizer ({z} : Set G)
  have hTD : T ≤ normalizer D := by
    apply le_normalizer_iff.mpr
    intro t ht x hx
    exact ⟨(mem_normalizer_iff.mp (hTL ht) x).mp hx.1,
      (centralizer ({z} : Set G)).mul_mem
        ((centralizer ({z} : Set G)).mul_mem (hTC ht) hx.2)
        ((centralizer ({z} : Set G)).inv_mem (hTC ht))⟩
  have hn : (D.subgroupOf (D ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le D.le_normalizer hTD)
  have hr := normal_embedded_pResidual_subgroupOf 2
    (show D ≤ D ⊔ T from le_sup_left) hn
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer
    ((map_subtype_le _).trans (show D ≤ D ⊔ T from le_sup_left))).mp hr)

omit [Finite G] in
/-- A central involution witnesses the nontrivial two-core of its overgroup. -/
theorem central_involution_core {J : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hzJ : z ∈ J) (hJC : J ≤ centralizer ({z} : Set G)) :
    J.pCoreIn 2 ≠ ⊥ := by
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hz]; rfl)
  have hn : J ≤ normalizer (zpowers z) := by
    apply le_trans ?_ (centralizer_le_normalizer (zpowers z : Set G))
    simpa only [zpowers_eq_closure, centralizer_closure] using hJC
  have hle := le_pCoreIn_of_normalizes hp (zpowers_le.mpr hzJ) hn
  intro hb
  have he : z ∈ (⊥ : Subgroup G) := by
    rw [← hb]
    exact hle (mem_zpowers z)
  have he' : z = 1 := he
  simp [he'] at hz

/-- All three local-family conditions hold for the centralizer residual. -/
theorem localResidual_mem_L (T : Sylow 2 G) (L : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    [IsQuasisimple (localResidual L z ⧸ pCore 2 (localResidual L z))] :
    localResidual L z ∈ Chapter1.L G T := by
  let B := localResidual L z
  let J : Subgroup G := B ⊔ T
  have hBN : (B.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le B.le_normalizer (localResidual_invariant hTL hTC))
  let _ := hBN
  let e : B.subgroupOf J ≃* B := subgroupOfEquivOfLe le_sup_left
  have hp : IsPPerfect 2 B := isPPerfect_embedded_pResidual 2 _
  have hp' : IsPPerfect 2 (B.subgroupOf J) :=
    hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  let _ : IsQuasisimple ((B.subgroupOf J) ⧸ pCore 2 (B.subgroupOf J)) :=
    IsQuasisimple.of_mulEquiv
      (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).symm
  have hc : (B.subgroupOf J).IsCComponent :=
    isCComponent_of_isPPerfect_of_quasisimple_core_quotient
      (inferInstance : (B.subgroupOf J).Normal).isSubnormal hp'
  refine ⟨hc, ⟨T.subtype (show (T : Subgroup G) ≤ J from le_sup_right), ?_⟩,
    central_involution_core hz ((show (T : Subgroup G) ≤ J from le_sup_right) hzT)
      (sup_le ((localResidual_le L z).trans inf_le_right) hTC)⟩
  simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding

namespace CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem a6_quasisimple : IsQuasisimple (alternatingGroup (Fin 6)) := by
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  exact { simple := ((QuotientGroup.quotientMulEquivOfEq
    (alternatingGroup.center_eq_bot (by simp))).trans
      QuotientGroup.quotientBot).isSimpleGroup }

/-- The actual centralizer component and full A.3.12 list, from the universal
earlier appendix implications. Normality is inside C_G(z). -/
theorem localResidual_embedding {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → A312Conclusion B)
    (hA38 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ K : Subgroup Y, K.IsCComponent →
      K.Normal ∨ (normalizer (K : Set Y)).index = 2 ∧ NonnormalCComponentModel K)
    (T : Sylow 2 G) (L : Subgroup G) (z : G)
    (hz : orderOf z = 2) (hzT : z ∈ T)
    (hTL : (T : Subgroup G) ≤ normalizer L)
    (hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hQ : IsSQTK 𝒦 ((centralizer ({z} : Set G)) ⧸
      pCore 2 (centralizer ({z} : Set G))))
    (e : (localResidual L z ⧸ pCore 2 (localResidual L z)) ≃*
      alternatingGroup (Fin 6)) :
    let C := centralizer ({z} : Set G)
    let B := (localResidual L z).subgroupOf C
    let q := QuotientGroup.mk' (pCore 2 C)
    ∃ K : Subgroup C, K.IsCComponent ∧ localResidual L z ≤ K.map C.subtype ∧
      K.Normal ∧ (∀ D : Subgroup C, D.IsCComponent → B ≤ D → D = K) ∧
      A312Embedding (B.map q) (K.map q) := by
  let C := centralizer ({z} : Set G)
  have hBC : localResidual L z ≤ C := (localResidual_le L z).trans inf_le_right
  let _ := a6_quasisimple
  let _ := IsQuasisimple.of_mulEquiv e.symm
  have hB := localResidual_mem_L T L z hz hzT hTL hTC
  have hB' := (mem_LIn_iff_subgroupOf hTC hBC).mp ⟨hBC, hB⟩
  let S : Sylow 2 C := T.subtype hTC
  obtain ⟨K, hK, hBK, hu, hemb, hn⟩ := lemma_1_2_4_of_A_3_12_A_3_8
    hA312 hA38 hQ S hB'
  refine ⟨K, hK, ?_, hn ?_, hu, hemb⟩
  · exact (map_subgroupOf_eq_of_le hBC).symm.le.trans (map_mono (f := C.subtype) hBK)
  · rw [← subgroupOf_normalizer_eq hBC]
    exact fun _ ht => localResidual_invariant hTL hTC ht

end CFSG.Quasithin.Chapter8.Section02.Offenders.Parabolic.Exclusion.CentralizerEmbedding
