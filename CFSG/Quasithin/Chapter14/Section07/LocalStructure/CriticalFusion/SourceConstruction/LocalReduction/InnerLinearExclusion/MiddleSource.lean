module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.SelectedSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.MiddleQuotient
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.PointCoreMovement
public import Theory.SpecificGroups.BinaryLinear.ActionCardinality

/-!
# The selected component and the actual middle-vertex quotient

Apply the middle-quotient construction to the original second parabolic,
retaining the original local subgroup, its two-residual and all three literal
intersections. A₆, L₄(2) and L₅(2) components force the necessary point-core
movement: contrary centrality would make their intrinsic two-core quotient
one of the earlier faithful A₅ or L₃(2) models, contradicting its order.
This transport uses Structural1222At and Theorem12213At at the same G,T.
For the small L₃(2) component, the independent original 14.5.21(2) identity
propagates through the plane and seed spans to give the same movement.

The final application uses the actual component selected by
original_exists_normal_component_reduction through SelectedSource. It keeps
all original 14.7.48 data and the universal earlier selection interfaces.
It constructs the S₃ × S₃ quotient and its full rank-two parabolic lattice;
it does not assume either as a callback. The I.5 contradiction and guarded
transport of the earlier selection chain remain required for 14.7.49–51.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.5.21(2), 14.7.4(1),
14.7.11 and 14.7.49–51, printed pp.1019–1020,1043,1045–1046,1064–1065.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Chapter12.Section08 CriticalFusion.Source
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components

/-- The earlier 14.5.21(2) identity forces movement of the original plane.
Its L₁-span is the seed and its H-span is U, so centrality would propagate. -/
theorem plane_moved_of_core_commutator
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hc : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  let := h.chosen.elementary
  let := F.localKernel_tilde_seed_elementary
  intro hz
  have hN : F.H ≤ normalizer (centralizer (F.H.pCoreIn 2 : Set G) : Set G) :=
    (F.H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))).trans
        (normalizer_le_normalizer_centralizer _)
  have hV : V ≤ centralizer (F.H.pCoreIn 2 : Set G) := by
    exact (F.seed_eq_plane_span L (by decide) h.chosen.normalizes
      (F.invariant_subgroup_of_ambient_natural h.naturalMarking (by decide))).ge.trans
        (conjugateSpanBy_le (commutator_eq_bot_iff_le_centralizer.mp hz)
          (((F.Li_le L 1).trans inf_le_right).trans hN))
  have hU : F.U ≤ centralizer (F.H.pCoreIn 2 : Set G) := conjugateSpanBy_le hV hN
  have hb : F.Vi 1 = ⊥ := hc.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr hU)
  have hn := F.card 1 (by decide)
  simp [hb] at hn

/-- Apply the middle-quotient proof to the actual local second parabolic.
The extra source premise is the original point-core movement, not supplied
normality, generation, a quotient or a rank-two residue. -/
theorem small_local_middle_quotient
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hm : Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) ∨
      Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) :
    ∃ H₂ Y : Subgroup G, H₂ = I ⊓ F.Gi 2 ∧
      RankTwoParabolics I ((T : Subgroup G).subgroupOf I)
        ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf I) (H₂.subgroupOf I) ∧
      Nonempty (HStar H₂ ≃* Equiv.Perm (Fin 3)) ∧
      Y = (pResidual 2 H₂).map H₂.subtype ∧ IsPPerfect 2 Y ∧
      (T : Subgroup G) ≤ normalizer (Y : Set G) ∧ Y ⊔ (T : Subgroup G) = H₂ ∧
      (F.Li L 1 ⊔ (T : Subgroup G)) ⊔ Y = I ∧
      ¬ Y ≤ normalizer (L : Set G) ∧ ⁅F.Vi 2,Y⁆ = ⊥ ∧
      (H₂ ⊔ F.P L) ⊓ I = H₂ ∧
      (H₂ ⊔ F.P L) ⊓ (L ⊔ (T : Subgroup G)) = F.P L ∧
      (H₂ ⊔ F.P L) ⊓ I ⊓ (L ⊔ (T : Subgroup G)) = (T : Subgroup G) ∧
      Nonempty (HStar (H₂ ⊔ F.P L) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
      RankTwoParabolics (H₂ ⊔ F.P L : Subgroup G) ((T : Subgroup G).subgroupOf (H₂ ⊔ F.P L))
        (H₂.subgroupOf (H₂ ⊔ F.P L)) ((F.P L).subgroupOf (H₂ ⊔ F.P L)) := by
  obtain ⟨H₂,Y,h₂I,hT₂,hR,he,hY,hYp,hYn,hYT,hgen,hout,hc,h₂eq,hJI,hJLT,hchamber⟩ :=
    small_local_middle_intersections h hab structural previous faithful I hI hm
  have h₂plane : H₂ ≤ F.Gi 2 := h₂eq.le.trans inf_le_right
  obtain ⟨hquot,hline⟩ := middle_quotient_and_parabolics_at h (structural G T)
    hmovement H₂ (h₂I.trans hI.2.1) hT₂ h₂plane he.some
  exact ⟨H₂,Y,h₂eq,hR,he,hY,hYp,hYn,hYT,hgen,hout,hc,hJI,hJLT,hchamber,hquot,hline⟩

private theorem binary_large_card {Q : Type*} [Group Q] {m : ℕ}
    (hm : m = 3 ∨ m = 4) (hmodel : ClassicalGroup.IsPSL Q (m + 1) 2) :
    168 < Nat.card Q := by
  obtain ⟨E,_,_,hE,⟨a⟩⟩ := hmodel
  let := Fintype.ofFinite E
  let f : E ≃+* ZMod 2 := (ZMod.ringEquivOfPrime E Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hE)).symm
  let e := a.trans ((Atlas.fieldEquivPSL (m + 1) f).trans
    (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega : 0 < m + 1)))
  rw [Nat.card_congr e.toEquiv,BinaryLinear.card_SL]
  rcases hm with rfl | rfl <;> norm_num [BinaryLinear.order,Fin.prod_univ_succ]

/-- Movement is discharged for the actual selected A₆, L₄(2) or L₅(2)
component. The subgroupOf equivalence retains its intrinsic two-core quotient. -/
theorem selected_large_component_plane_moved_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (K : Subgroup G) (hKH : K ≤ F.H) (hK : (K.subgroupOf F.H).IsCComponent)
    (hrow : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
      ∃ m : ℕ, (m = 3 ∨ m = 4) ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2) :
    ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
  apply plane_moved_of_large_component_at h structural previous faithful (K.subgroupOf F.H) hK
  let c := subgroupOfEquivOfLe hKH
  rw [Nat.card_congr (QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).toEquiv]
  rcases hrow with hsix | hlin
  · obtain ⟨e⟩ := hsix
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  · obtain ⟨m,hm,hmodel⟩ := hlin
    exact binary_large_card hm hmodel

/-- The selected component supplies the middle quotient and line residue in
all large rows, without a movement input. For the remaining L₃(2) row,
retain the independent earlier 14.5.21(2) identity explicitly. -/
theorem original_exists_component_with_middle_geometry
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
        ((ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∧ ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1) ∨
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
          (H₂ ⊔ F.P L) ⊓ J ⊓ (L ⊔ (T : Subgroup G)) = (T : Subgroup G) ∧
          Nonempty (HStar (H₂ ⊔ F.P L) ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) ∧
          RankTwoParabolics (H₂ ⊔ F.P L : Subgroup G)
            ((T : Subgroup G).subgroupOf (H₂ ⊔ F.P L))
            (H₂.subgroupOf (H₂ ⊔ F.P L)) ((F.P L).subgroupOf (H₂ ⊔ F.P L)) := by
  obtain ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hn,hgeom⟩ :=
    original_exists_component_with_small_parabolic_geometry d h hab structural previous faithful earlier source48
  refine ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hn,?_⟩
  intro hrow
  have hmove : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥ := by
    rcases hrow with ⟨_,hc⟩ | h6 | ⟨m,hm,hmodel,_⟩
    · exact plane_moved_of_core_commutator h hc
    · exact selected_large_component_plane_moved_at h (structural G T) (previous G T)
        faithful K hKH hK (Or.inl h6)
    · exact selected_large_component_plane_moved_at h (structural G T) (previous G T)
        faithful K hKH hK (Or.inr ⟨m,hm,hmodel⟩)
  have hrow' : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∨
      ∃ m : ℕ, (m = 3 ∨ m = 4) ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2 ∧
        ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
          (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
            MulAut.innerSubgroup (K ⧸ pCore 2 K) := hrow.imp And.left id
  obtain ⟨J,H₂,Y,hJ,hJH,h₂eq,hR,he,hY,hYp,hYn,hYT,hgenY,hout,hc,hJI,hJLT,hchamber⟩ := hgeom hrow'
  have h₂J : H₂ ≤ J := h₂eq.le.trans inf_le_left
  have hT₂ : (T : Subgroup G) ≤ H₂ := hYT ▸ le_sup_right
  obtain ⟨hquot,hline⟩ := middle_quotient_and_parabolics_at h (structural G T) hmove
    H₂ (h₂J.trans hJH) hT₂ (h₂eq.le.trans inf_le_right) he.some
  exact ⟨J,H₂,Y,hJ,hJH,h₂eq,hR,he,hY,hYp,hYn,hYT,hgenY,hout,hc,hJI,hJLT,hchamber,hquot,hline⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
