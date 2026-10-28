module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.RankDoubling.Actions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Parabolic.CoreBounds

/-!
# Normalization of the literal doubling subgroup

Put B = ⟨V₃^{K₂}⟩. Interchanging the two conjugate spans gives
U₂ = ⟨B^{L₂}⟩. The source core O₂(G₁) centralizes U_H/V₁, so it
normalizes B, which contains V₁. It also normalizes L₂; hence it
normalizes U₂. Thus I₂ = O₂(G₁)L₂ acts on the literal quotient.
This verifies normalization without assuming an action or a decomposition.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.4, 13.7.3(6), and the conjugate-span calculation in 13.8.6, p.948.
The earlier core, residual and generation conclusions are explicit inputs.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
variable {G : Type*} [Group G]

/-- The two useful orders of generating U₂ agree as literal ambient subgroups. -/
theorem U2_eq_iterated_span (H V V₂ V₃ L₂ : Subgroup G)
    (hgen : V = conjugateSpanBy V₃ L₂)
    (hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G)) :
    Source.U2 H V V₂ = conjugateSpanBy (conjugateSpanBy V₃ (Source.K2 H V₂)) L₂ := by
  have hLV : L₂ ≤ normalizer (V : Set G) := by
    rw [hgen]
    exact le_normalizer_conjugateSpanBy _ _
  apply le_antisymm
  · change conjugateSpanBy V (Source.K2 H V₂) ≤ _
    rw [hgen]
    exact conjugate_span_le_iterated_span V₃ L₂ (Source.K2 H V₂) hKL
  · apply conjugateSpanBy_le
    · exact conjugateSpanBy_mono (hgen ▸ le_conjugateSpanBy V₃ L₂) le_rfl
    · exact actor_normalizes_conjugate_span V L₂ (Source.K2 H V₂) hLV hKL

/-- The point core normalizes the three-space orbit using its actual commutators. -/
theorem core_normalizes_threeOrbit (H V₁ V₂ V₃ Q₁ : Subgroup G)
    (h₁ : V₁ ≤ V₃) (hcomm : ⁅Source.UH H V₃, Q₁⁆ ≤ V₁) :
    Q₁ ≤ normalizer (conjugateSpanBy V₃ (Source.K2 H V₂) : Set G) := by
  apply le_normalizer_iff_commutator_le_left.mpr
  exact ((commutator_mono (conjugateSpanBy_mono le_rfl (Source.K2_le H V₂)) le_rfl).trans
    hcomm).trans (h₁.trans (le_conjugateSpanBy V₃ (Source.K2 H V₂)))

/-- Normalization follows from the earlier local identities, without a quotient-action premise. -/
theorem I2_normalizes_U2 (H V V₁ V₂ V₃ I₂ L₂ Q₁ : Subgroup G)
    (h₁ : V₁ ≤ V₃)
    (hI : I₂ = conjugateSpanBy Q₁ (normalizer (V₂ : Set G)))
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype)
    (hjoin : I₂ = Q₁ ⊔ L₂)
    (hQ₂ : Q₁ ≤ normalizer (V₂ : Set G))
    (hgen : V = conjugateSpanBy V₃ L₂)
    (hcomm : ⁅Source.UH H V₃, Q₁⁆ ≤ V₁) :
    I₂ ≤ normalizer (Source.U2 H V V₂ : Set G) := by
  have hlocal := local_normality I₂ L₂ Q₁ V₂ hI hres
  have hKL : Source.K2 H V₂ ≤ normalizer (L₂ : Set G) :=
    (Source.K2_le_centralizer H V₂).trans
      (inf_le_right.trans ((centralizer_le_normalizer _).trans hlocal))
  have hLU : L₂ ≤ normalizer (Source.U2 H V V₂ : Set G) := by
    exact actor_normalizes_conjugate_span V L₂ (Source.K2 H V₂)
      (by rw [hgen]; exact le_normalizer_conjugateSpanBy _ _) hKL
  rw [hjoin]
  apply sup_le _ hLU
  rw [U2_eq_iterated_span H V V₂ V₃ L₂ hgen hKL]
  exact normalizes_conjugate_span Q₁ _ L₂
    (core_normalizes_threeOrbit H V₁ V₂ V₃ Q₁ h₁ hcomm) (hQ₂.trans hlocal)

/-- The core of the normal local subgroup lies in the core of G₂. -/
theorem local_core_le (I₂ Q₁ V₂ : Subgroup G)
    (hI : I₂ = conjugateSpanBy Q₁ (normalizer (V₂ : Set G)))
    (hQ₂ : Q₁ ≤ normalizer (V₂ : Set G)) :
    I₂.pCoreIn 2 ≤ (normalizer (V₂ : Set G)).pCoreIn 2 := by
  have hI₂ : I₂ ≤ normalizer (V₂ : Set G) := by
    rw [hI]
    exact conjugateSpanBy_le_self hQ₂
  have hnorm : normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) := by
    rw [hI]
    exact le_normalizer_conjugateSpanBy _ _
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 I₂)
    ((pCoreIn_le 2 I₂).trans hI₂)
    (hnorm.trans (normalizer_le_normalizer_characteristic_image I₂ (pCore 2 I₂)))

/-- Restrict the G.2.2 centrality conclusion to U₂ and the source I₂-core. -/
theorem local_core_centrality (H V V₂ I₂ Q₁ : Subgroup G)
    (hI : I₂ = conjugateSpanBy Q₁ (normalizer (V₂ : Set G)))
    (hQ₂ : Q₁ ≤ normalizer (V₂ : Set G))
    (hcentral : ⁅conjugateSpanBy V (normalizer (V₂ : Set G)),
      (normalizer (V₂ : Set G)).pCoreIn 2⁆ ≤ V₂) :
    ⁅Source.U2 H V V₂, I₂.pCoreIn 2⁆ ≤ V₂ := by
  apply le_trans _ hcentral
  exact commutator_mono
    (conjugateSpanBy_mono le_rfl ((Source.K2_le_centralizer H V₂).trans
      (inf_le_right.trans (centralizer_le_normalizer _))))
    (local_core_le I₂ Q₁ V₂ hI hQ₂)

/-- The local residual is normal in I₂, so its core lies in the I₂-core. -/
theorem residual_core_le (I₂ L₂ : Subgroup G)
    (hres : L₂ = (pResidual 2 I₂).map I₂.subtype) :
    L₂.pCoreIn 2 ≤ I₂.pCoreIn 2 := by
  have hLI : L₂ ≤ I₂ := hres ▸ map_subtype_le _
  have hIL : I₂ ≤ normalizer (L₂ : Set G) := by
    rw [hres]
    exact I₂.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image I₂ (pResidual 2 I₂))
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 L₂)
    ((pCoreIn_le 2 L₂).trans hLI)
    (hIL.trans (normalizer_le_normalizer_characteristic_image L₂ (pCore 2 L₂)))

/-- Restrict the actual point-normalizer core to the intermediate local overgroup. -/
theorem point_core_le_Hcore [Finite G] (T : Sylow 2 G) (H V₁ : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hH₁ : H ≤ normalizer (V₁ : Set G)) :
    (normalizer (V₁ : Set G)).pCoreIn 2 ≤ Source.QH H := by
  let G₁ := normalizer (V₁ : Set G)
  have hT₁ : (T : Subgroup G) ≤ G₁ := hTH.trans hH₁
  have hQT : G₁.pCoreIn 2 ≤ T := by
    have h := pCoreIn_le_sylow G₁ (T.subtype hT₁)
    rwa [Sylow.coe_subtype, map_subgroupOf_eq_of_le hT₁] at h
  exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 G₁) (hQT.trans hTH)
    (hH₁.trans (G₁.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image G₁ (pCore 2 G₁))))

end CFSG.Quasithin.Chapter13.Section08.TransvectionParabolic.RankDoubling.SourceAction
