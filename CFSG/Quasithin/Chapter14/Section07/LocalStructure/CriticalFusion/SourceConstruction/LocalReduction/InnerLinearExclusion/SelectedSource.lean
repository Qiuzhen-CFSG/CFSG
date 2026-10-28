module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.Source
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.SmallGeometry

/-!
# Original selected-component application of the small parabolic construction

Start with the actual component selected by the proved normal-component
reduction and retain all original 14.7.48 data. A PSL₃(2) or A₆ component
recovers one of the three small full quotients on the original point
normalizer. An inner PSL₄(2) or PSL₅(2) component constructs an escaping
rank-two preimage with full quotient PSL₃(2), excluding the solvable
product row by the proved 14.7.29 containment.

For that same local subgroup, construct the other parabolic and its
escaping two-residual, prove plane centralization, and identify the middle
vertex's actual intersections. This discharges the opening geometric
construction of 14.7.11 at each consumer needed by 14.7.49–51. Its middle
S₃ × S₃ quotient and final I.5 contradiction are completed in
`MiddleSource`, `LinearSource` and `C3Source`; this geometric leaf
retains its original statement. The independent 14.7.47/48 and graph
branches retain their original assembly owners.

Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.1045–1046,
1064–1065. No selected component is identified with O²(I).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- Apply the second-parabolic construction to the selected original component,
including the actual escaping rank-two preimage in either inner linear row.
The original 14.7.48 data remain explicit. The middle-quotient calculation
and I.5 contradiction are not assumed or asserted by this construction. -/
theorem original_exists_component_with_small_parabolic_geometry
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (source48 : ∀ K : Subgroup G, K ≤ F.H → (K.subgroupOf F.H).IsCComponent →
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      (K.subgroupOf F.H).Normal ∧ ¬ K ≤ normalizer (L : Set G) ∧
      Models.F918Models (K ⧸ pCore 2 K) ∧ SylowOvergroupComponentUnique K ∧
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆ ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (K : Set G),
        (ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∨
          Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
          ∃ m : ℕ, (m = 3 ∨ m = 4) ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2 ∧
            ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
              (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
                MulAut.innerSubgroup (K ⧸ pCore 2 K)) →
        ∃ J H₂ Y : Subgroup G, J ∈ F.Hz L (normalizer (L : Set G)) ∧ J ≤ F.H ∧
          H₂ = J ⊓ F.Gi 2 ∧
          RankTwoParabolics J ((T : Subgroup G).subgroupOf J)
            ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J) (H₂.subgroupOf J) ∧
          Nonempty (HStar H₂ ≃* Equiv.Perm (Fin 3)) ∧
          Y = (pResidual 2 H₂).map H₂.subtype ∧ IsPPerfect 2 Y ∧
          (T : Subgroup G) ≤ normalizer (Y : Set G) ∧ Y ⊔ (T : Subgroup G) = H₂ ∧
          (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ Y = J ∧
          ¬ Y ≤ normalizer (L : Set G) ∧ ⁅F.Vi 2,Y⁆ = ⊥ ∧
          (H₂ ⊔ F.P L) ⊓ J = H₂ ∧
          (H₂ ⊔ F.P L) ⊓ (L ⊔ (T : Subgroup G)) = F.P L ∧
          (H₂ ⊔ F.P L) ⊓ J ⊓ (L ⊔ (T : Subgroup G)) = (T : Subgroup G) := by
  obtain ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,hsix,hn,hinner⟩ :=
    original_exists_component_quotient_reduction_with_six d h hab structural previous faithful earlier source48
  refine ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hn,?_⟩
  intro hrow
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  have hlocal : ∃ J : Subgroup G, J ∈ F.Hz L (normalizer (L : Set G)) ∧ J ≤ F.H ∧
      (Nonempty (HStar J ≃* Matrix.PSL3Two.PSL) ∨
        Nonempty (HStar J ≃* alternatingGroup (Fin 6)) ∨
        Nonempty (HStar J ≃* Equiv.Perm (Fin 6))) := by
    rcases hrow with h3 | h6 | ⟨m,hm,hmodel,hi⟩
    · exact ⟨F.H,hH,le_rfl,Or.inl (hthree h3)⟩
    · exact ⟨F.H,hH,le_rfl,Or.inr (hsix h6)⟩
    · obtain ⟨J,hJ,hJH,_,he⟩ := hinner m hm hmodel hi
      exact ⟨J,hJ,hJH,Or.inl he⟩
  obtain ⟨J,hJ,hJH,hsmall⟩ := hlocal
  obtain ⟨H₂,Y,_,_,hR,he,hY,hYp,hYn,hYT,hgenY,hout,hc,h₂eq,hJI,hJLT,hchamber⟩ :=
    small_local_middle_intersections h hab structural previous faithful J hJ hsmall
  exact ⟨J,H₂,Y,hJ,hJH,h₂eq,hR,he,hY,hYp,hYn,hYT,hgenY,hout,hc,hJI,hJLT,hchamber⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
