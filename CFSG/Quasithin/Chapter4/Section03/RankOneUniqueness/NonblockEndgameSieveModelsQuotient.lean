module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameSieveModelsInputs
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuasisimpleContaining

/-!
# The full nonblock component quotient and its central covers

Apply the proved A.3.6 classification to the top component of K_Z/O₂(K_Z).
Its two-core is trivial and it inherits SQTK from the actual root normalizer.
Quasisimplicity excludes both solvable-Fitting rows. The remaining alternatives
are a centerless simple quotient or an actual three-cover, with its marked
center and source parameter restrictions retained. In particular the center
has order one or three and is prime to every noncubic source prime.

This classification feeds the nonblock prime-rank sieve; it does not replace
the full quotient by its central quotient. The remaining source-model
inspection is owned by qt-d-1222-nonblock-endgame-sieve.
Source: Aschbacher–Smith, A.3.6, pp.43–45, and original 4.3.12–16, pp.617–618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {c : SourceConfiguration T L} {n : ℕ}

private theorem three_cover_transport {A B : Type*} {M : Type} [Group A] [Group B] [Group M]
    (e : A ≃* B) (h : IsThreeCover A M) : IsThreeCover B M := by
  obtain ⟨hq, ⟨ez⟩, ⟨em⟩⟩ := h
  let := hq
  refine ⟨IsQuasisimple.of_mulEquiv e, ⟨(centerCongr e.symm).trans ez⟩, ?_⟩
  have he : (center B).map e.symm.toMonoidHom = center A := by
    apply le_antisymm
    · rintro _ ⟨b, hb, rfl⟩
      exact (centerCongr e.symm ⟨b, hb⟩).property
    · intro a ha
      exact mem_map.mpr ⟨e a, (centerCongr e ⟨a, ha⟩).property, e.symm_apply_apply a⟩
  let q : (B ⧸ center B) ≃* (A ⧸ center A) :=
    QuotientGroup.congr _ _ e.symm he
  exact ⟨q.trans em⟩

private theorem three_cover_model_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : ThreeCoverModel A) : ThreeCoverModel B := by
  cases h with
  | classical unitary q hq hm =>
    refine .classical unitary q hq ?_
    cases unitary
    · obtain ⟨F, hF, hfin, hc, ⟨a⟩⟩ := hm
      exact ⟨F, hF, hfin, hc, ⟨e.symm.trans a⟩⟩
    · obtain ⟨F, hF, hfin, J, hc, hj, ⟨a⟩⟩ := hm
      exact ⟨F, hF, hfin, J, hc, hj, ⟨e.symm.trans a⟩⟩
  | alternating_six hm => exact .alternating_six (three_cover_transport e hm)
  | alternating_seven hm => exact .alternating_seven (three_cover_transport e hm)
  | mathieu hm => exact .mathieu (three_cover_transport e hm)

/-- A.3.6 on the full two-core quotient: its center is trivial, or it is
one of the actual central three-covers. -/
theorem SecondaryData.componentQuotient_simple_or_threeCover (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    (IsSimpleGroup (s.component ⧸ pCore 2 s.component) ∧
      center (s.component ⧸ pCore 2 s.component) = ⊥) ∨
      (Nonempty (center (s.component ⧸ pCore 2 s.component) ≃* Multiplicative (ZMod 3)) ∧
        ThreeCoverModel (s.component ⧸ pCore 2 s.component)) := by
  let J := s.component ⧸ pCore 2 s.component
  let := s.quasisimple
  let : IsQuasisimple (⊤ : Subgroup J) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have htop : (⊤ : Subgroup J).IsCComponent :=
    (show IsComponent J ⊤ from ⟨.top, inferInstance⟩).isCComponent
  have hm := ChapterA.Section03.SourceEmbeddings.quasisimple_containing_component_models_knownSimple
    (SecondaryData.componentQuotient_sqtk s D h) (pCore_quotient_pCore_eq_bot 2) htop
  rcases hm with ⟨hs, _⟩ | ⟨⟨ez⟩, hm⟩
  · let := hs
    let : IsSimpleGroup J := (topEquiv (G := J)).symm.isSimpleGroup
    refine Or.inl ⟨inferInstance, ?_⟩
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp hz)).elim
  · exact Or.inr ⟨⟨(centerCongr (topEquiv (G := J)).symm).trans ez⟩,
      three_cover_model_transport topEquiv hm⟩

/-- In particular the full quotient center has order one or three. -/
theorem SecondaryData.componentQuotient_center_card (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    Nat.card (center (s.component ⧸ pCore 2 s.component)) = 1 ∨
      Nat.card (center (s.component ⧸ pCore 2 s.component)) = 3 := by
  rcases SecondaryData.componentQuotient_simple_or_threeCover s D h with ⟨_, hz⟩ | ⟨⟨e⟩, _⟩
  · exact Or.inl (by rw [hz]; simp)
  · exact Or.inr ((Nat.card_congr e.toEquiv).trans (by simp))

/-- The source center is prime to every noncubic torus prime. -/
theorem SecondaryData.componentQuotient_center_coprime (s : SecondaryData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    Nat.Coprime p (Nat.card (center (s.component ⧸ pCore 2 s.component))) := by
  rcases SecondaryData.componentQuotient_center_card s D h with hz | hz
  · rw [hz]
    exact Nat.coprime_one_right p
  · rw [hz]
    exact hp.coprime_iff_not_dvd.mpr (fun hd =>
      hp3 (((Nat.dvd_prime Nat.prime_three).mp hd).resolve_left hp.ne_one))
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
