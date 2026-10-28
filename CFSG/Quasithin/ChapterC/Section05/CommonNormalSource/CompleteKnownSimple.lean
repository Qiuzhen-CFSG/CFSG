module
public import CFSG.Quasithin.ChapterC.Section05.CommonNormalSource.CounterexampleKnownSimple

/-!
# The original C.5.8 theorem over the complete known-simple catalogue

The original C.5.1 data would produce the counterexample ruled out by the proved known-simple C.5.3–13 argument if every subgroup of R normal in ⟨M₀,H⟩ were trivial. The returned nontrivial subgroup has exactly the original relative normality conclusion, with the actual residual and Sylow maps retained.

Source: Aschbacher–Smith C.5.8–13, printed pp.160–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05
universe u
variable {G : Type u} [Group G] [Finite G]

/-- C.5.8 on the original C.5.1 data and literal common-normal conclusion. -/
theorem theorem_C_5_8_knownSimple
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (P : Sylow 2 G) (H M R : Subgroup G) (hPH : (P : Subgroup G) ≤ H)
    (hf : generalizedFitting H = pCore 2 H)
    (hu : Order.HasUniqueMaximalOver (P.subtype hPH : Subgroup H) ⊤)
    (hRP : R ≤ (P : Subgroup G)) (hPM : (P : Subgroup G) ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (Q : Sylow 2 (R ⊔ (pResidual 2 H).map H.subtype : Subgroup G))
    (hQ : (Q : Subgroup (R ⊔ (pResidual 2 H).map H.subtype : Subgroup G)).map
      (R ⊔ (pResidual 2 H).map H.subtype).subtype = R) :
    ∃ N : Subgroup G, N ≠ ⊥ ∧ N ≤ R ∧ (N.subgroupOf (M ⊔ H)).Normal := by
  by_contra hn
  let d : BlockAnalysis.OriginalHypotheses H M ((pResidual 2 H).map H.subtype) R
      (P : Subgroup G) := {
    fitting := hf
    sylow := P.subtype hPH
    sylow_image := by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPH]
    unique := hu
    residual := rfl
    R_le := hRP
    T_le := hPM
    R_normal := hMR
    residual_sylow := Q
    residual_sylow_image := hQ
    no_common_normal := by
      intro N hNR hN
      by_contra hne
      exact hn ⟨N,hne,hNR,hN⟩ }
  exact d.counterexample_false_knownSimple hG P rfl

end CFSG.Quasithin.ChapterC.Section05
end
