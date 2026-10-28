module
public import CFSG.Quasithin.ChapterC.Section05.CommonNormalSource.KnownSimple

/-!
# The KnownSimple C.5.8 consumer on the original counterexample

The ambient Sylow restricts to the same Sylow of H as the original record,
and the literal residual image identifies its supplied Sylow witness.
Applying the completed C.5.8 wrapper produces a nontrivial subgroup of R
normal in ⟨M₀,H⟩, contradicting exactly the original C.5.2 condition.
The genuine A.3.12 implication remains visible; no additional local or
ambient domain assumption is inferred from this adapter.

Source: Aschbacher–Smith C.5.1–2 and C.5.8, printed pp.154,160–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
universe u
variable {G : Type u} [Group G] [Finite G] {H M K R T : Subgroup G}

/-- The literal C.5.1–2 configuration cannot occur in the original
C.5.8 domain once its genuine A.3.12 source implication is supplied. -/
theorem OriginalHypotheses.counterexample_false_knownSimple_of_A312
    (d : OriginalHypotheses H M K R T)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
      B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
    (P : Sylow 2 G) (hP : (P : Subgroup G) = T) : False := by
  have hPH : (P : Subgroup G) ≤ H := hP.le.trans d.T_le_H
  have hSP : (P.subtype hPH : Subgroup H) = (d.sylow : Subgroup H) := by
    apply map_injective H.subtype_injective
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hPH,d.sylow_image,hP]
  have hu : Order.HasUniqueMaximalOver (P.subtype hPH : Subgroup H) ⊤ := hSP ▸ d.unique
  have hQ : ∃ Q : Sylow 2 (R ⊔ (pResidual 2 H).map H.subtype : Subgroup G),
      (Q : Subgroup (R ⊔ (pResidual 2 H).map H.subtype : Subgroup G)).map
        (R ⊔ (pResidual 2 H).map H.subtype).subtype = R := by
    rw [d.residual]
    exact ⟨d.residual_sylow,d.residual_sylow_image⟩
  obtain ⟨Q,hQ⟩ := hQ
  obtain ⟨N,hne,hNR,hN⟩ := theorem_C_5_8_of_A_3_12 hG hA312 P H M R hPH
    d.fitting hu (d.R_le.trans hP.ge) (hP.le.trans d.T_le) d.R_normal Q hQ
  exact hne (d.no_common_normal N hNR hN)

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
end
