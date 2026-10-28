module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixEscapingSource
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldProjectiveResidual
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixHeldLocalIntersection

/-!
# Original escaping-point projective geometry

The final ordinary12.7.5 constructs the same B and Vt, including their full
central quotient marking. All projective extension, centralizer, normalizer,
intersection and residual conclusions therefore hold on the original
escaping source with no component, center or quotient-model premise.
The p.841 extraspecial and Sylow comparison remain separate obligations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
open Theory.GroupAction.ComponentRankAction Matrix.PSL3Four.OuterThreeStructure
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The same original escaping point supplies the full marked projective
extension and exact overlaps, without any supplied ordinary model. -/
theorem original_tripleSix_escaping_projective_geometry
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hout : ¬ centralizer ({(t : G)} : Set G) ≤ normalizer (K : Set G)) :
    let H := centralizer ({(t : G)} : Set G)
    let Lt := (pResidual 2 (K ⊓ H : Subgroup G)).map (K ⊓ H).subtype
    let B := conjugateSpanBy Lt H
    let Vt := tripleSixPoint D a t
    let X := tripleSixScalarResidual K
    let M := normalizer (K : Set G)
    let N := normalizer (B : Set G)
    let W := B ⊔ X
    centralizer (B : Set G) = Vt ∧ N = normalizer (Vt : Set G) ∧
      B ⊓ M = Lt ∧ B ⊓ K = Lt ∧ W ⊓ M = Lt ⊔ X ∧ W ⊓ K = Lt ⊔ X ∧
      (pResidual 2 N).map N.subtype = W ∧ W.relIndex N ∣ 4 ∧
      ∃ e : B ⧸ center B ≃* Matrix.PSL3Four.PSL,
        ∃ hWN : W ≤ N,
          ∃ f : W →* Matrix.ProjGenLinGroup (Fin 3) Matrix.PSL3Four.F,
            Function.Surjective f ∧ f.ker = Vt.subgroupOf W ∧
              ∀ w : W, (pglEquiv (f w)).val = action B e (inclusion hWN w) := by
  obtain ⟨hB,hcenter,hV,hn,he⟩ :=
    original_tripleSix_point_identification_at h structural D a t ht heven hout
  let := hn
  obtain ⟨e₀⟩ := he
  let e := (QuotientGroup.quotientMulEquivOfEq hV.symm).trans e₀
  obtain ⟨hc,_,hN,_⟩ := original_tripleSix_held_component_normalizer
    h structural D a t ht heven hB hcenter e
  obtain ⟨hBM,hBK,hWM,hWK⟩ := original_tripleSix_held_local_intersections
    h structural D a t ht heven hB hcenter e
  obtain ⟨hres,hi⟩ := original_tripleSix_held_projective_residual
    h structural D a t ht heven hB hcenter e
  exact ⟨hc,hN,hBM,hBK,hWM,hWK,hres,hi,e,
    original_tripleSix_held_projective_extension h structural D a t ht heven hB hcenter e⟩

end CFSG.Quasithin.Chapter12.Section07
