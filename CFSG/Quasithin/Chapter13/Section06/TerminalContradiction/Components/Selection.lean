module

public import CFSG.Quasithin.Chapter13.Section03.LocalSteps
public import CFSG.Quasithin.ChapterE.Defs
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.NormalizerCore

/-!
# The initial subgroup and its two-residual

Starting from the involution z, its full centralizer outside M, and
13.6.25(2), choose a genuine minimal member H₁ of H(T,M) inside C_G(z).
The Sylow supplement theorem gives H₁ = O²(H₁)T. Since T ≤ M and H₁
is outside M, its two-residual K₁ is outside M as well. Characteristic
invariance of the residual proves that T normalizes K₁.

This is the first construction in the proof of 13.6.27. The preceding
source results must supply the displayed inputs; no component or
classification alternative is assumed or proved by this selection lemma.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.6.27,
printed p.934, using 13.3.6 and 13.6.25(2).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components
variable {G : Type*} [Group G] [Finite G]

/-- Select H₁ and construct K₁ = O²(H₁), retaining all ambient embeddings. -/
theorem exists_initial_residual (T : Sylow 2 G) (M : Subgroup G)
    (z : G) (hz : orderOf z = 2)
    (hT : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hTM : (T : Subgroup G) ≤ M)
    (hout : ¬ centralizer ({z} : Set G) ≤ M)
    (h25 : ∀ H ∈ Chapter1.HOutside G (T : Set G) (M : Set G),
      1 < ChapterE.generationParameter H) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) M,
      H ≤ centralizer ({z} : Set G) ∧
      1 < ChapterE.generationParameter H ∧
      (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H ∧
      ¬ (pResidual 2 H).map H.subtype ≤ M ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  obtain ⟨H, hH, hHC⟩ := Section03.exists_HStar_le_involution_centralizer
    (T : Subgroup G) M z hz hT hout
  have hmin : Minimal (fun Y => Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M) H := hH
  have hTH : (T : Subgroup G) ≤ H := hmin.prop.1.2
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH,
    ← MonoidHom.range_eq_map, range_subtype] at he
  refine ⟨H, hH, hHC, h25 H hmin.prop, he, ?_, ?_⟩
  · intro hRM
    exact hmin.prop.2 (he ▸ sup_le hRM hTM)
  · exact hTH.trans (le_normalizer_embedded_pResidual 2 H)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components

