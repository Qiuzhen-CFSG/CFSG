module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.ComponentActionComplete
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Conclusion
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.ConjugatePairs
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Commutator
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction

/-!
# The original A₅ Fitting consumer of F.9.5

The actual source context supplies the local strongly quasithin K-group,
faithful binary action and every symmetric-three pair. With the original
13.5.19 residual normalizer facts, the proved Fitting obstruction argument
forces the V-image to centralize the full Fitting subgroup of H/O₂(H).
Source: Aschbacher–Smith13.5.19–20, printed p.923.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction.Fitting.SourceAction Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include d hA312 hH hU


omit hA312 hU [IsElementaryAbelian 2 V] in
/-- The full SQTK hypothesis for the original local overgroup. -/
theorem source_local_sqtk : IsSQTK KnownSimple.IsKnownSimple H := by
  have hZN : H ≤ normalizer (V₁ : Set G) :=
    hH.2.1.trans (Subgroup.centralizer_le_normalizer _)
  have hp : IsPGroup 2 V₁ := IsPGroup.of_card (n := 1) (by simpa using d.flag.one_card)
  have hn : V₁ ≠ ⊥ := by
    intro hz
    have hh := d.flag.one_card
    simp [hz] at hh
  have hl : IsTwoLocal (normalizer (V₁ : Set G)) := ⟨V₁,hn,hp,rfl⟩
  have hs := (d.hypothesis.qtke.twoLocal_sqtk hl).subgroup
    (H.subgroupOf (normalizer (V₁ : Set G)))
  let e := (subgroupOfEquivOfLe hZN).symm
  exact ⟨hs.stronglyQuasithin.of_injective e.toMonoidHom e.injective,
    hs.isKGroup.of_injective e.toMonoidHom e.injective⟩

/-- Original13.5.20 with the independent earlier13.5.19 residual facts visible. -/
theorem source_centralizes_fitting
    (Y : Subgroup G) (hYH : Y ≤ H) (hY : IsPPerfect 2 Y)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hYV : Y ≤ normalizer (V : Set G))
    (himage : Source.starImage H (H ⊓ normalizer (Y : Set G)) =
      normalizer (Source.starImage H Y : Set (Source.Hstar H)))
    (hcore : V ≤ (H ⊓ normalizer (Y : Set G)).pCoreIn 2) :
    Source.starImage H V ≤
      centralizer (fittingSubgroup (Source.Hstar H) : Set (Source.Hstar H)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hr : let := hf.elementary; Module.finrank (ZMod 2) (Additive D.V) = 4 :=
    (card_V_iff_rank_four hf).mp d.module_card
  apply ComponentReduction.Fitting.centralizes_fitting_of_source_action
    source_F95Two source_F95Six KnownSimple.IsKnownSimple D hf (source_local_sqtk d hH)
    V₂ (normalizer (L : Set G)) d.third_index hU hr d.plane_transport
    ?_ ?_ ?_ Y hYH hY hYquot hYV himage hcore
  · intro g hg hp
    have hn := source_plane_normalizes d hA312 hH hU hg hp
    exact Or.inr (le_inf (hn.trans d.module_normalizer) hn)
  · exact inf_le_right.trans ((d.seed_normalizer hA312).trans d.module_normalizer)
  · have hc : normalizer (L : Set G) ⊓ centralizer (V₃ : Set G) ≤ centralizer (V : Set G) :=
      d.third_centralizer_local.le
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hc]
    exact bot_le

end CFSG.Quasithin.Chapter13.Section05.A5Source
