module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.Cover
public import CFSG.Quasithin.ChapterG.Section09.CoverComponents
public import CFSG.Quasithin.Chapter1.Section03.Terminal.Definitions
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# Lifting the original terminal component

The actual point normalizer is an SQTK cover of its terminal action quotient.
Residual generation lifts a prescribed component through that exact map,
without assuming a solvable kernel. The normal point gives nontrivial two-core,
so the lift belongs to the original local family. Its normalizer has index at
most two; hence its T-conjugate closure is normal in the point normalizer.

These are the literal image and orbit clauses needed before the component
sieve in 14.3.15. The row, intrinsic quasisimple quotient and movement outside
M are separate later conclusions.
Source: Aschbacher--Smith 1.2.1,1.2.6 and14.3.15, printed pp.503--506,994.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]

/-- The actual dotted component has at most two conjugates in the literal
terminal actor, by lifting to its original point normalizer. -/
theorem terminal_component_normalizer_index_le_two
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] (hn : 1 ≤ n)
    (L : Subgroup F.TerminalHdot) (hL : IsComponent F.TerminalHdot L) :
    (normalizer (L : Set F.TerminalHdot)).index ≤ 2 :=
  (terminal_sqtkCover hG F hn).component_normalizer_index_le_two hL

/-- Lift a literal terminal component to the ambient source local family.
The map is exactly the defining quotient by terminalHatAction.ker, and the
T-conjugate closure (not the join with T) is normal in the point normalizer. -/
theorem terminal_component_lift
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
    (F : InvariantFlag T V n) [IsElementaryAbelian 2 V] (hn : 1 ≤ n)
    (L : Subgroup F.TerminalHdot) (hL : IsComponent F.TerminalHdot L) :
    ∃ K : Subgroup G, K ≤ F.H ∧ K ∈ MainForward.localComponents T ∧
      (K.subgroupOf F.H).IsCComponent ∧
      (K.subgroupOf F.H).map (QuotientGroup.mk' F.terminalHatAction.ker) = L ∧
      (normalizer (K : Set G)).relIndex F.H ≤ 2 ∧
      ((conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H).Normal := by
  have hh := (terminal_sqtkCover hG F hn).exists_component_lift hL
  change ∃ D : Subgroup F.H, D.IsCComponent ∧
    D.map (QuotientGroup.mk' F.terminalHatAction.ker) = L ∧
    (normalizer (D : Set F.H)).index ≤ 2 at hh
  obtain ⟨D,hD,he,hi⟩ := hh
  let K := D.map F.H.subtype
  have hKH : K ≤ F.H := map_subtype_le D
  have hKD : K.subgroupOf F.H = D :=
    comap_map_eq_self_of_injective F.H.subtype_injective D
  have hTH : (T : Subgroup G) ≤ F.H := F.invariant 1
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  have htwo : IsPGroup 2 (F.Vi 1) := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hpoint : F.Vi 1 ≤ F.H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes htwo (F.Vi 1).le_normalizer le_rfl
  have hcore : F.H.pCoreIn 2 ≠ ⊥ := by
    intro hb
    have hp := le_bot_iff.mp (hb ▸ hpoint)
    simp [hp] at hcard
  have hlocal : K ∈ MainForward.localComponents T := by
    apply (Chapter1.Terminal.mem_L_iff_localComponents T K).mp
    exact (Chapter1.lemma_1_2_6 T ⟨hcore,hTH⟩).1 ⟨hKH,hKD.symm ▸ hD⟩ |>.2
  refine ⟨K,hKH,hlocal,hKD.symm ▸ hD,?_,?_,?_⟩
  · simpa only [hKD] using he
  · change ((normalizer (K : Set G)).subgroupOf F.H).index ≤ 2
    rw [subgroupOf_normalizer_eq hKH]
    simpa only [hKD] using hi
  · let S := T.subtype hTH
    have hnD := conjugateSpanBy_sylow_normal D S
      (Chapter1.Section02.component_normal_or_index_two_source (pointNormalizer_sqtk hG F hn) hD)
    have hmap : (conjugateSpanBy D (S : Subgroup F.H)).map F.H.subtype =
        conjugateSpanBy K (T : Subgroup G) := by
      rw [map_conjugateSpanBy]
      congr 1
      exact map_subgroupOf_eq_of_le hTH
    have hsub : (conjugateSpanBy K (T : Subgroup G)).subgroupOf F.H =
        conjugateSpanBy D (S : Subgroup F.H) := by
      rw [← hmap]
      exact comap_map_eq_self_of_injective F.H.subtype_injective _
    rw [hsub]
    exact hnD

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
