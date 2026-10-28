module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.MinimalReplacement
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingIntrinsic

/-!
# Intrinsic quasisimplicity of the minimal A₇ replacement

The minimum with the original star image inherits the literal A₇ plus
marking. Apply the complete A.3.6 consequence to its C-component inside
K₀ Tᵥ: an A₇ image excludes both nonquasisimple radical alternatives.
The original plus quotient supplies the target's trivial two-core, so no
separate reduced-module premise for the replacement is required.

This proves the source replacement's structural assertion while retaining
the possible central triple cover. The genuinely earlier A.3.6 implication
and component-invariance conclusion remain supplied by the section owner.

Source: Aschbacher--Smith, proof of 13.6.22, printed p.932, first paragraph.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1.Section02
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.MinimalReplacement
open ComponentSelection SourceTransferFields.RankOneBorel
universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}

/-- The original source minimum in the A₇ branch has a quasisimple
intrinsic two-core quotient. The comparison with the original A₇ action
retains the exact quotient maps on representatives of K₀. -/
theorem exists_minimal_same_star_alternating_seven
    (hA36 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ B : Subgroup X,
      B.IsCComponent → A36Conclusion B)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hK : K ∈ Yz L T z v)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (h14 : ∀ D ∈ Yz L T z v, Tv T v ≤ normalizer (D : Set G))
    (hR : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (e : plusImage K L T z v hL hz K ≃* alternatingGroup (Fin 7)) :
    ∃ (K₀ : Subgroup G) (hle : K₀ ≤ K),
      Minimal (fun D => D ∈ Chapter1.LIn (K ⊔ Tv T v) (Tv T v) ∧
        starImage z v D = starImage z v K) K₀ ∧
      K₀ ∈ Yz L T z v ∧ Tv T v ≤ normalizer (K₀ : Set G) ∧
      WK K₀ L T z v = WK K L T z v ∧
      IsQuasisimple (K₀ ⧸ pCore 2 K₀) ∧
      ∃ e₀ : plusImage K₀ L T z v hL hz K₀ ≃* alternatingGroup (Fin 7),
        ∀ k : K₀, e₀ (componentMap K₀ L T z v hL hz k) =
          e (componentMap K L T z v hL hz (inclusion hle k)) := by
  obtain ⟨K₀, hle, hmin, hY, hn, hW, e₀, he₀⟩ :=
    exists_minimal_same_star_marked K L T z v hK hL hz h14 e
  have hplus : pCore 2 (plusImage K L T z v hL hz K) = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (plusImage_K_subnormal K L T z v hL hz hK), hR]
    exact (plusImage K L T z v hL hz K).ker_subtype
  have hseven : pCore 2 (alternatingGroup (Fin 7)) = ⊥ := by
    rw [← pCore_map_iso 2 e, hplus, Subgroup.map_bot]
  let H := K₀ ⊔ Tv T v
  let B := K₀.subgroupOf H
  have hHG : H ≤ Gv v := sup_le hY.1.1 inf_le_right
  have hH : IsSQTK 𝒦 H := (IsSQTK.equiv (subgroupOfEquivOfLe hHG)).mp
    (hlocal.subgroup (H.subgroupOf (Gv v)))
  let a : B ≃* K₀ := subgroupOfEquivOfLe le_sup_left
  let f := e₀.toMonoidHom.comp ((componentMap K₀ L T z v hL hz).comp a.toMonoidHom)
  have hf : Function.Surjective f := e₀.surjective.comp
    ((componentMap_surjective K₀ L T z v hL hz).comp a.surjective)
  let : IsQuasisimple (B ⧸ pCore 2 B) := AlternatingIntrinsic.cComponent_quotient_quasisimple
    hA36 hH B hY.1.2.1 f hf hseven
  have hq : IsQuasisimple (K₀ ⧸ pCore 2 K₀) := IsQuasisimple.of_mulEquiv
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a))
  exact ⟨K₀, hle, hmin, hY, hn, hW, hq, e₀, he₀⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.MinimalReplacement
