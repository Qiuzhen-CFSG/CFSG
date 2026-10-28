module
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.OmegaSpan
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingSupport
/-!
# Generating the full short-block module from a fixed seed

Irreducibility first gives generation modulo the central layer. The identity
[U,K]=U then absorbs that layer, so the full U is generated. The A₅ central
layer is zero, and an elementary two-group action supplies its noncentral
Sylow-fixed seed. For natural covers the full-T seed is I.2.3(2).
Source: Aschbacher–Smith C.5.13, printed p.162; I.2.3(2), printed p.413.
-/
public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterC.Section05.NormalizerControl
open ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]
/-- A noncentral seed generates the entire short-block module, including
its central layer. Irreducibility is used only modulo that layer. -/
theorem block_span_of_noncentral_seed (K Z : Subgroup G) (hK : IsShort K)
    (hZU : Z ≤ U K) (hZ : ¬ Z ≤ centralizer (K : Set G)) :
    conjugateSpanBy Z K = U K := by
  let W := conjugateSpanBy Z K
  let C := (blockU K ⊓ center K).map K.subtype
  have hKU : K ≤ normalizer (U K : Set G) := K.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image K (blockU K))
  have hWU : W ≤ U K := conjugateSpanBy_le hZU hKU
  have hWK : W ≤ K := hWU.trans (map_subtype_le _)
  have hKW : K ≤ normalizer (W : Set G) := le_normalizer_conjugateSpanBy _ _
  have hCC : C ≤ centralizer (K : Set G) := by
    rintro _ ⟨c,hc,rfl⟩ k hk
    exact congrArg K.subtype (mem_center_iff.mp hc.2 ⟨k,hk⟩)
  let D := W.subgroupOf K ⊔ (blockU K ⊓ center K)
  let : (W.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hKW
  have hDU : D ≤ blockU K := sup_le (by
    intro w hw
    obtain ⟨u,hu,he⟩ := hWU hw
    exact (Subtype.ext he : u=w) ▸ hu) inf_le_left
  have hUcomm : ⁅U K,K⁆ = U K := by
    have hh := commutator_isPPerfect_idempotent K (pCoreIn 2 K)
      hK.twoPerfect (isPGroup_pCoreIn 2 K)
      (K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K)))
    simpa only [U,pCoreIn,blockU,map_commutator,← MonoidHom.range_eq_map,range_subtype] using hh
  rcases hK.irreducible.2 D inferInstance le_sup_right hDU with he | he
  · have hWC : W ≤ centralizer (K : Set G) := by
      intro w hw
      have hd : (⟨w,hWK hw⟩ : K) ∈ D := (show W.subgroupOf K ≤ D from le_sup_left) hw
      rw [he] at hd
      exact hCC (mem_map_of_mem K.subtype hd)
    exact (hZ ((le_conjugateSpanBy _ _).trans hWC)).elim
  · have hj : W ⊔ C = U K := by
      have hh := congrArg (Subgroup.map K.subtype) he
      simpa only [D,C,U,Subgroup.map_sup,map_subgroupOf_eq_of_le hWK] using hh
    have hWW : ⁅W,K⁆ ≤ W := le_normalizer_iff_commutator_le_left.mp hKW
    have hCW : ⁅C,K⁆ ≤ W :=
      (commutator_eq_bot_iff_le_centralizer.mpr hCC).le.trans bot_le
    have hjoincomm : ⁅W ⊔ C,K⁆ ≤ W := by
      apply (le_commutatorPreimage_iff (normalizer (W : Set G)) K W (W ⊔ C) le_rfl).mp
        (sup_le (le_commutatorPreimage W.le_normalizer hWW)
          (le_commutatorPreimage ((hCC.trans (centralizer_le hWK)).trans
            (Subgroup.centralizer_le_normalizer _)) hCW)) |>.2
    exact le_antisymm hWU (hUcomm.symm.le.trans (hj ▸ hjoincomm))
/-- I.2.3(2)'s exact noncentral full-Sylow fixed point supplies the
natural-cover span used in C.5.13. -/
theorem omega_span_of_noncentral_fixed (K T : Subgroup G) (hK : IsShort K)
    (hfixed : ¬ U K ⊓ omegaOneCenterAmbient T ≤ centralizer (K : Set G)) :
    U K ≤ conjugateSpanBy (omegaOneCenterAmbient T) K := by
  rw [← block_span_of_noncentral_seed K (U K ⊓ omegaOneCenterAmbient T) hK inf_le_left hfixed]
  exact conjugateSpanBy_mono inf_le_right le_rfl
/-- The A₅ module has no central layer, so its ordinary central Sylow
involution already supplies a noncentral fixed seed. -/
theorem alternating_five_noncentral_fixed (K T : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hT : IsPGroup 2 T)
    (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G)) :
    ¬ U K ⊓ omegaOneCenterAmbient T ≤ centralizer (K : Set G) := by
  have hU : IsElementaryAbelian 2 (U K) := hK.2.1.elementary.map K.subtype
  have hUne : U K ≠ ⊥ := by
    intro hz
    exact hK.2.1.blockU_ne_bot ((map_injective K.subtype_injective)
      (hz.trans (Subgroup.map_bot K.subtype).symm))
  have hfix := CounterexampleCharacteristic.central_witness T (U K) (U K) hT hUT
    (hTK.trans (normalizer_le_normalizer_characteristic_image K (blockU K))) hUne hU le_rfl
  have hd : Disjoint (U K) (centralizer (K : Set G)) :=
    ConjugateSource.alternatingModule_disjoint_of_commuting K _ hK le_rfl
  intro hc
  apply hfix
  exact bot_unique ((le_inf inf_le_left hc).trans (disjoint_iff.mp hd).le)
/-- The actual A₅ source module lies in the K-span of Ω₁Z(T). -/
theorem alternating_five_omega_span (K T : Subgroup G)
    (hK : IsAlternatingBlock K 5) (hT : IsPGroup 2 T)
    (hUT : U K ≤ T) (hTK : T ≤ normalizer (K : Set G)) :
    U K ≤ conjugateSpanBy (omegaOneCenterAmbient T) K :=
  omega_span_of_noncentral_fixed K T hK.2.1 (alternating_five_noncentral_fixed K T hK hT hUT hTK)
end CFSG.Quasithin.ChapterC.Section05.NormalizerControl
