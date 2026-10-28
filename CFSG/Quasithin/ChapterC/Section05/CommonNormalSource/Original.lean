module
public import CFSG.Quasithin.ChapterC.Section05.CommonNormalSource.Counterexample

/-!
# The original C.5.8 common-normal conclusion

If no nontrivial subgroup of R is normal in ⟨M₀,H⟩, the original C.5.1 data
form the counterexample ruled out by the completed source argument. The
returned subgroup therefore satisfies the original relative normality,
with the actual residual and Sylow inclusion maps retained.

Source: Aschbacher–Smith C.5.8, printed pp.160–163. Earlier outside-block,
A.3.12 and normalized-cubic implications remain explicit here and are
instantiated separately for the complete known-simple catalogue.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05
universe u
variable {G : Type u} [Group G] [Finite G]

/-- C.5.8 on the original C.5.1 data and literal common-normal conclusion. -/
theorem common_normal_of_original {𝒦 : GroupClass.{u}}
    (hG : IsSimpleQTKE 𝒦 G) (outside : BlockAnalysis.C128Outside 𝒦)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK 𝒦 Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (hG6 : ChapterG.Section06.NormalizedCubicSourceInput.{u,u} 𝒦)
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
  exact d.counterexample_false hG outside hA312 hG6 P rfl

end CFSG.Quasithin.ChapterC.Section05
end
