module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.LinearSource
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion.PointCore
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.LocalAction

/-!
# The C₃ contradiction and the original small-component exclusion

The original point-normalizer two-core is contained in each local I:
it lies in the common Sylow subgroup and is normalized by I. The natural
seed, and hence the flag plane, also lies in O₂(I). The marked C₃ point
core is elementary abelian, so it would centralize the original moving
plane. This is the final contradiction of 14.7.11 in the A₆/S₆ cases.

Combine this with the proved A₃ case and literal full-quotient recovery.
The component selected by the original normal-component reduction now
satisfies both exclusions of 14.7.49 and the inner-action exclusions of
14.7.51. Its A₆ hypothesis supplies plane movement internally. The L₃(2)
case retains the earlier original 14.5.21(2) identity. All 14.7.48 outputs,
the full F.9.18 catalogue, relative normality and the actual quotient
actions are preserved. No component is identified with the whole residual.

The universal source APIs remain unchanged. The core contradiction itself
uses Structural1222At; transporting the earlier cubic-actor and solvable
local constructions to guarded inputs remains a separate open step.
Source: Aschbacher–Smith, refs/quasithin.pdf, printed pp.1046,1064–1065,
with the marked I.5.15 recognition on printed p.424.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Quasithin.I5
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
open Chapter12.Section08 CriticalFusion.Source
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section08.Components
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The original moving point core embeds in every local core, together
with the flag plane. Thus the latter core cannot be abelian. This step
uses only the same-G,T structural input. -/
theorem local_core_not_abelian_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ IsMulCommutative (pCore 2 I) := by
  intro habQ
  let := habQ
  let : IsMulCommutative (I.pCoreIn 2) := Subgroup.map_isMulCommutative (pCore 2 I) I.subtype
  have hTI := F.sylow_le_of_mem_Hz hI
  have hQT : F.H.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow F.H (T.subtype (F.invariant 1))
    change F.H.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf F.H).map F.H.subtype at hh
    intro x hx
    obtain ⟨y,hy,rfl⟩ := hh hx
    exact hy
  have hQI : F.H.pCoreIn 2 ≤ I.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 F.H) (hQT.trans hTI)
      (hI.2.1.trans (F.H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image F.H (pCore 2 F.H))))
  have hVQ : F.Vi 2 ≤ I.pCoreIn 2 := (F.le_seed 2).trans
    ((le_conjugateSpanBy V I).trans
      (WholeResidualAssembly.local_f9_hypothesis_at h structural hab I hI).UH_le_QH)
  exact hmovement (commutator_eq_bot_iff_le_centralizer.mpr
    (hVQ.trans ((le_centralizer (I.pCoreIn 2)).trans (Subgroup.centralizer_le hQI))))

/-- The A₆/S₆ full-quotient cases of original 14.7.11. The constructed
C₃ system has an elementary point core, contrary to the original plane
movement. All restrictions use the literal subgroupOf equivalence. -/
theorem small_local_alternatingSix_impossible
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (hmovement : ⁅F.Vi 2,F.H.pCoreIn 2⁆ ≠ ⊥)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (he : Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∨
      Nonempty (HStar I ≃* Equiv.Perm (Fin 6))) : False := by
  obtain ⟨H₂,h₂,S,hS⟩ := small_local_source_system h hab structural previous faithful
    hmovement I hI .C3 (by simp) (fun _ => he)
  let E := (L ⊔ (T : Subgroup G)) ⊔ I
  have hS0 : S.family 0 = I.subgroupOf E := by rw [hS]; rfl
  let e := (MulEquiv.subgroupCongr hS0).trans
    (subgroupOfEquivOfLe (show I ≤ E from le_sup_right))
  let c := ((pCore 2 (S.family 0)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (pCore_map_iso 2 e))
  let := c3_point_core_elementary S
  let : IsElementaryAbelian 2 (pCore 2 I) :=
    IsElementaryAbelian.of_surjective c.toMonoidHom c.surjective
  exact local_core_not_abelian_at h hab (structural G T) hmovement I hI inferInstance

/-- All three literal full-quotient exclusions in original 14.7.11. -/
theorem small_local_full_quotient_exclusions
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G))) :
    ¬ Nonempty (HStar I ≃* Matrix.PSL3Two.PSL) ∧
      ¬ Nonempty (HStar I ≃* alternatingGroup (Fin 6)) ∧
      ¬ Nonempty (HStar I ≃* Equiv.Perm (Fin 6)) := by
  have hm := plane_moved_of_core_commutator h core_commutator
  exact ⟨small_local_linearThree_impossible h hab structural previous faithful hm I hI,
    fun he => small_local_alternatingSix_impossible h hab structural previous faithful hm I hI (Or.inl he),
    fun he => small_local_alternatingSix_impossible h hab structural previous faithful hm I hI (Or.inr he)⟩

/-- On the actual selected component, 14.7.49 and the inner-action branch
of 14.7.51. The A₆ movement is discharged by that same component. The
original 14.5.21(2) identity is retained for the small L₃(2) row. -/
theorem original_exists_component_small_inner_exclusions
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (core_commutator : ⁅F.U,F.H.pCoreIn 2⁆ = F.Vi 1)
    (source48 : ∀ K : Subgroup G, K ≤ F.H → (K.subgroupOf F.H).IsCComponent →
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      (K.subgroupOf F.H).Normal ∧ ¬ K ≤ normalizer (L : Set G) ∧
      Models.F918Models (K ⧸ pCore 2 K) ∧ SylowOvergroupComponentUnique K ∧
      F.Li L 1 ≤ K ∧ F.H = K ⊔ (T : Subgroup G) ∧ F.UH F.H = ⁅F.UH F.H,K⁆ ∧
      ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 2 ∧
      ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) ∧
      ∃ hn : (T : Subgroup G) ≤ normalizer (K : Set G),
        ∀ m : ℕ, (m = 3 ∨ m = 4) → ClassicalGroup.IsPSL (K ⧸ pCore 2 K) (m + 1) 2 →
          ¬ (∀ (t : G) (ht : t ∈ (T : Subgroup G)),
            (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
              MulAut.innerSubgroup (K ⧸ pCore 2 K)) := by
  obtain ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,hn,hinner⟩ :=
    original_exists_component_linear_exclusions d h hab structural previous faithful earlier
      core_commutator source48
  refine ⟨K,hKH,hK,hKn,hKM,hmodels,hunique,hLK,hgen,hcomm,hthree,?_,hn,hinner⟩
  rintro ⟨eK⟩
  have hm := selected_large_component_plane_moved_at h (structural G T) (previous G T)
    faithful K hKH hK (Or.inl ⟨eK⟩)
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  exact small_local_alternatingSix_impossible h hab structural previous faithful hm F.H hH
    (alternatingSix_full_quotient_at h (structural G T) F.H K hH hKH hKn hgen eK)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.InnerLinearExclusion
