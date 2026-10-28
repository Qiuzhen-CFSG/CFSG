module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.FirstBaumann
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableOneBlock

/-!
# A small common-core seed in the remaining original nonsolvable branch

Both original Contexts and one universal Baumann pair are retained on the
same Sylow subgroup. Block exclusion leaves opposite normalization.
The first member is elementary of order two or four in both actual cores;
its central seed generates the opposite natural module and its conjugates
in the whole Baumann centralizer remain in that member.

The application constructs the Context of the literal embedded O²(H),
uses the full omega-action kernel to prove its Thompson movement, and
preserves the multiple-overgroup guard under every original S,I rechoice.
This supplies structural restrictions for the remaining opposite-normalizer
case; it does not discharge hparameter or the earlier-source premises.
Source: Aschbacher--Smith 13.2.4(2b),13.2.8(1), pp. 879--880;
C.1.18,C.1.24(a), pp. 126,130--131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside
open Section02.A5Outside.OriginalCentralization ChapterB ChapterC
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The first member and its opposite natural-module span in the actual
original nonsolvable pair. Both normalization orientations are retained. -/
theorem original_nonsolvable_first_baumann
    {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
    (d : Context T L V V₁ V₂ V₃) (hc : IsA5Counterexample G)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ (W W₁ W₂ W₃ : Subgroup G)
      (_ : Context T ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G))),
      let A := D.first.map (baumann (T : Subgroup G)).subtype
      D.Universal.{u,u} ∧ D.first ≠ D.second ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 4 ∧
      ((L ⊔ (T : Subgroup G) ≤ normalizer (A : Set G) ∧
          H ≤ normalizer (D.second.map (baumann (T : Subgroup G)).subtype : Set G)) ∨
        (L ⊔ (T : Subgroup G) ≤ normalizer
            (D.second.map (baumann (T : Subgroup G)).subtype : Set G) ∧
          H ≤ normalizer (A : Set G))) ∧
      A ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ H.pCoreIn 2 ∧
      IsElementaryAbelian 2 A ∧ (Nat.card A = 2 ∨ Nat.card A = 4) ∧
      ((A ≤ centralizer (L : Set G) ∧ W ≤ conjugateSpanBy
          (A ⊓ omegaOneCenterAmbient (T : Subgroup G)) ((pResidual 2 H).map H.subtype)) ∨
        (A ≤ centralizer ((pResidual 2 H).map H.subtype : Set G) ∧
          V ≤ conjugateSpanBy (A ⊓ omegaOneCenterAmbient (T : Subgroup G)) L)) ∧
      ∀ x ∈ A, ∀ y ∈ centralizer (baumann (T : Subgroup G) : Set G),
        IsConj x y → y ∈ A := by
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
  obtain ⟨D,hfour,hD,hne,hcases⟩ :=
    original_nonsolvable_opposite_baumann d hc hno hmany h1332 hcontexts h523 hH hZ hs
  have hnA : L ⊔ (T : Subgroup G) ≤ normalizer
      (D.first.map (baumann (T : Subgroup G)).subtype : Set G) ∨
      H ≤ normalizer (D.first.map (baumann (T : Subgroup G)).subtype : Set G) :=
    hcases.elim (fun h => Or.inl h.1) (fun h => Or.inr h.2)
  exact ⟨W,W₁,W₂,W₃,e,D,hD,hne,hfour,hcases,
    original_first_baumann_structure d e hjoin hH hJd hJe D hnA⟩

/-- Apply the same first-member restrictions after every original guarded
rechoice, transporting the multiple-overgroup hypothesis. -/
theorem universal_original_nonsolvable_first_baumann
    (T : Sylow 2 G)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hc : IsA5Counterexample G) (hno : ¬ ClassificationModels.IsQTKEModel G)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (hcontexts : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      ∃ W W₁ W₂ W₃ : Subgroup G, Nonempty (Context S I W W₁ W₂ W₃))
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (S : Sylow 2 G) (I : Subgroup G) (standing : SourceHypothesis S I)
    (H : Subgroup G)
    (hH : H ∈ Chapter3.HStar (S : Subgroup G) (normalizer (I : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (S : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) :
    ∃ (V V₁ V₂ V₃ : Subgroup G)
      (_ : Context S I V V₁ V₂ V₃)
      (W W₁ W₂ W₃ : Subgroup G)
      (_ : Context S ((pResidual 2 H).map H.subtype) W W₁ W₂ W₃)
      (D : GlaubermanNiles.CharacteristicPair (baumann (S : Subgroup G))),
      let A := D.first.map (baumann (S : Subgroup G)).subtype
      D.Universal.{u,u} ∧ D.first ≠ D.second ∧
      Nat.card (omegaOneCenterAmbient (S : Subgroup G)) = 4 ∧
      ((I ⊔ (S : Subgroup G) ≤ normalizer (A : Set G) ∧
          H ≤ normalizer (D.second.map (baumann (S : Subgroup G)).subtype : Set G)) ∨
        (I ⊔ (S : Subgroup G) ≤ normalizer
            (D.second.map (baumann (S : Subgroup G)).subtype : Set G) ∧
          H ≤ normalizer (A : Set G))) ∧
      A ≤ (I ⊔ (S : Subgroup G)).pCoreIn 2 ⊓ H.pCoreIn 2 ∧
      IsElementaryAbelian 2 A ∧ (Nat.card A = 2 ∨ Nat.card A = 4) ∧
      ((A ≤ centralizer (I : Set G) ∧ W ≤ conjugateSpanBy
          (A ⊓ omegaOneCenterAmbient (S : Subgroup G)) ((pResidual 2 H).map H.subtype)) ∨
        (A ≤ centralizer ((pResidual 2 H).map H.subtype : Set G) ∧
          V ≤ conjugateSpanBy (A ⊓ omegaOneCenterAmbient (S : Subgroup G)) I)) ∧
      ∀ x ∈ A, ∀ y ∈ centralizer (baumann (S : Subgroup G) : Set G),
        IsConj x y → y ∈ A := by
  obtain ⟨V,V₁,V₂,V₃,⟨d⟩⟩ := hcontexts S I standing
  have hmanyS : 1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard := by
    rwa [maximalTwoLocalOvergroups_ncard_sylow S T]
  exact ⟨V,V₁,V₂,V₃,d,original_nonsolvable_first_baumann d hc hno hmanyS
    h1332 hcontexts h523 hH hZ hs⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
