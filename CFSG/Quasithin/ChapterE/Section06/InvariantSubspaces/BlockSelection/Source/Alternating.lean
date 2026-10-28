module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Source.SylowAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.AlternatingLocal.Source
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingThree
public import Theory.GroupAction.InnerActionCardinality

/-!
# The actual action on the alternating E.6.7 factors

For A₅ the intrinsic Sylow-center quotient has order two. For A₃ use
Thompson movement and the original central action to obtain the order-two
bound; the intrinsic quotient itself has order four in that case. The
actual action kernel gives corank one, and escape gives global parameter
one. The full point-stabilizer Borel has the required relative index.

Source: Aschbacher–Smith E.6.7(2), printed p.246.
-/

public section
namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
open Subgroup Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual automorphism image computes the fixed-space corank. -/
theorem fixedSpace_corank_eq_log_range {V L : Subgroup G}
    (hn : V ≤ normalizer (L : Set G)) :
    subgroupCorank V (V ⊓ centralizer (L : Set G)) =
      Nat.log 2 (Nat.card (L.normalizerMonoidHom.comp (inclusion hn)).range) := by
  rw [← index_ker, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  exact congrArg (Nat.log 2) (inf_relIndex_left V (centralizer (L : Set G)))

/-- The complete alternating conclusions for the two selected alternating
types, with their literal Borel premise exposed for C.1.29 to discharge. -/
theorem source_alternating_of_borel {𝒦 : GroupClass} {T : Sylow 2 G}
    {M V W H L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 𝒦 T M V) (hW : W ∈ obstructionFamily M V)
    (hQH : sylowCentralizer (T : Subgroup G) V ≤ H)
    (hHC : H ≤ centralizer (W : Set G)) (hc : HasCharacteristicTwo H)
    (hLH : L ≤ H) (hL : ChapterC.IsBlock (L.subgroupOf H))
    (hout : ¬ L ≤ M)
    (hm : L = ⁅L, elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V)⁆)
    (hType : ChapterC.IsAlternatingBlock L n) (hn : n = 3 ∨ n = 5)
    (hB : AlternatingBlockBorel L (M.subgroupOf L) n) :
    subgroupCorank V (V ⊓ centralizer (L : Set G)) = 1 ∧
      (L ⊓ M).relIndex L = n ∧ globalR V = 1 := by
  obtain ⟨S, _hS, hVN, hi⟩ := source_block_action h hW hQH hHC hc hLH hL
  have hcard : Nat.card (L.normalizerMonoidHom.comp (inclusion hVN)).range ≤ 2 := by
    rcases hn with rfl | rfl
    · obtain ⟨e⟩ := hType.equiv_alternatingFour
      have hJQ : elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V) ≤
          sylowCentralizer (T : Subgroup G) V := sSup_le fun _ hA => hA.1
      have hVJ : V ≤ centralizer
          (elementaryAbelianMaxJ (sylowCentralizer (T : Subgroup G) V) : Set G) :=
        (le_centralizer_iff.mp (inf_le_right : sylowCentralizer (T : Subgroup G) V ≤
          centralizer (V : Set G))).trans (centralizer_le hJQ)
      apply AlternatingLocal.a3_ambient_action_card_le_two L _ V e S hm.symm hVJ hVN
      intro v hv
      obtain ⟨z, ⟨z₀, hz₀, rfl⟩, hz⟩ := hi v hv
      exact ⟨z₀, ⟨z₀, (mem_omegaOneCenterAmbient_iff _ _).mp hz₀ |>.1, rfl⟩, hz⟩
    · let Z := omegaOneCenterAmbient (S : Subgroup L)
      have hh := Theory.GroupAction.card_range_le_inner_quotient
        (L.normalizerMonoidHom.comp (inclusion hVN)) Z (by
          intro v
          obtain ⟨z, ⟨z₀, hz₀, rfl⟩, hz⟩ := hi v v.property
          refine ⟨⟨z₀, hz₀⟩, ?_⟩
          apply MulEquiv.ext
          intro l
          exact Subtype.ext (hz l l.property).symm)
      rw [AlternatingLocal.a5_omega_center_quotient_card_source hType S] at hh
      exact hh
  have hsmall : subgroupCorank V (V ⊓ centralizer (L : Set G)) ≤ 1 := by
    rw [fixedSpace_corank_eq_log_range hVN]
    exact (Nat.log_mono_right hcard).trans (by decide : Nat.log 2 2 ≤ 1)
  obtain ⟨hcor, hr⟩ := h.fixedSpace_corank_eq_one hout hsmall
  refine ⟨hcor, ?_, hr⟩
  rw [inf_relIndex_left]
  exact AlternatingLocal.borel_index hType.1 hB

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection
