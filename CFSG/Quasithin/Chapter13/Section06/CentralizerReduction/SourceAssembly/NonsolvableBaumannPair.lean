module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableCenters
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.BaumannPair

/-!
# The common Baumann pair for the original nonsolvable outside group

The earlier original source constructs a second Context for the literal
embedded O²(H). Full omega movement and the independent guarded Baumann
normalizer bound give Thompson movement on its chosen natural module.
One universal characteristic pair therefore applies to both original
local groups. Local uniqueness excludes every shared normalizer alternative,
leaving a genuine alternating block or opposite normalization of distinct
members. The universal application transports the multiple-overgroup guard
after every original S,I rechoice.

This gives an additional structural reduction of the remaining commuting
case. Neither an alternating block nor the opposite normalizer configuration
is identified with the missing residual four-group lift. Unrestricted
hparameter, earlier source discharge, full 13.2.7/13.6.7 and nonsingular hCv
remain open. Source: Aschbacher--Smith 13.2.8(1), p.880, using C.1.18 and
C.1.24(a), pp.126,130--131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization ChapterB ChapterC
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The same Baumann pair applies to the original component and the embedded
outside residual. All earlier inputs and the full omega movement are retained. -/
theorem original_nonsolvable_baumann_pair
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)),
      D.Universal.{u,u} ∧
      ¬ (L ⊔ (T : Subgroup G) ≤ normalizer
        (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
      ¬ (L ⊔ (T : Subgroup G) ≤ normalizer
        (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∧
      (IsAlternatingBlock L 5 ∨ IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5 ∨
        (D.first ≠ D.second ∧
          ((L ⊔ (T : Subgroup G) ≤ normalizer
              (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
          (L ⊔ (T : Subgroup G) ≤ normalizer
              (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G))))) := by
  obtain ⟨W,W₁,W₂,W₃,⟨e⟩⟩ := original_nonsolvable_residual_context d hc h1332 hcontexts hH hZ hs
  have hn := normalizes_faithful_of_source1332 d h1332
  have hB := OriginalCentralization.baumann_normalizer_of_many d hmany
  have hker := OriginalCentralization.nonsolvable_omega_centralizer_eq_twoCore d hn hH hZ hs
  have hjoin : (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H := by
    have hh := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hH.1.1.2))
    rw [Subgroup.map_sup,←MonoidHom.range_eq_map,range_subtype] at hh
    change (pResidual 2 H).map H.subtype ⊔
      ((T : Subgroup G).subgroupOf H).map H.subtype = H at hh
    rwa [map_subgroupOf_eq_of_le hH.1.1.2] at hh
  have hJd := OriginalCentralization.thompson_moves_of_omega_movement d hH hZ
  have hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
    intro hj
    have hC := (e.local_centralizers e.normalizes_L).1
    rw [hjoin] at hC
    have hcore : elementaryAbelianMaxJ (T : Subgroup G) ≤ H.pCoreIn 2 :=
      (le_inf ((show elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) from
        sSup_le fun _ hA => hA.1).trans hH.1.1.2) hj).trans hC.le
    apply thompson_moves_omegaOrbit d.hypothesis.qtke T hH hB hZ
    intro j hj u hu
    obtain ⟨a,ha,he⟩ := hcore hj
    have huH : u ∈ H := (conjugateSpanBy_le
      (fun z hz => hH.1.1.2 ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1)
      H.le_normalizer) hu
    have hc : a ∈ centralizer ((omegaOrbit T H).subgroupOf H : Set H) := hker.symm ▸ ha
    rw [←he]
    exact congrArg H.subtype (hc ⟨u,huH⟩ hu)
  exact original_pair_baumann_alternatives d e hjoin hH hJd hJe

/-- Apply the pair reduction after every original guarded rechoice. -/
theorem universal_original_nonsolvable_baumann_pair
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ D : GlaubermanNiles.CharacteristicPair (baumann (S : Subgroup G)),
      D.Universal.{u,u} ∧
      ¬ (I ⊔ (S : Subgroup G) ≤ normalizer
        (D.first.map (baumann (S : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.first.map (baumann (S : Subgroup G)).subtype : Set G)) ∧
      ¬ (I ⊔ (S : Subgroup G) ≤ normalizer
        (D.second.map (baumann (S : Subgroup G)).subtype : Set G) ∧
        H ≤ normalizer (D.second.map (baumann (S : Subgroup G)).subtype : Set G)) ∧
      (IsAlternatingBlock I 5 ∨ IsAlternatingBlock ((pResidual 2 H).map H.subtype) 5 ∨
        (D.first ≠ D.second ∧
          ((I ⊔ (S : Subgroup G) ≤ normalizer
              (D.first.map (baumann (S : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.second.map (baumann (S : Subgroup G)).subtype : Set G)) ∨
          (I ⊔ (S : Subgroup G) ≤ normalizer
              (D.second.map (baumann (S : Subgroup G)).subtype : Set G) ∧
            H ≤ normalizer (D.first.map (baumann (S : Subgroup G)).subtype : Set G))))) := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact original_nonsolvable_baumann_pair d hc hmanyS h1332 hcontexts hH hZ hs
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
