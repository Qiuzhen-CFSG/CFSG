module

public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.KnownSimple

/-!
# The original binary alternatives needed for full Hall escape

The proved original component selection and marked geometric cases give
precisely the exchanged, single Bender, and single diagram rows. Their
proved generation upper bounds exclude all other rows when n(X)>1.
Only the adequate inequality n(X)≤f is used; no numerical equality across
the maximal core is assumed. The component and both source quotient maps
are those of the original minimal parabolic.

Source: Aschbacher–Smith E.2.2 and 4.4.13(1), pp.215–216,623–624.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
open MarkedModels ChapterB
universe u
variable {X : Type u} [Group X] [Finite X]

private theorem normal_binary_cases
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hs : ¬ Group.IsSolvable X)
    (hn : 1 < generationParameter X) (K : Subgroup X) (hK : K.IsCComponent)
    [K.Normal] (hqs : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (S : Subgroup X) = ⊤) :
    ∃ f : ℕ, 1 < f ∧ ReducedCases (minimalParabolicMax S hP) K S f := by
  have hA := ChapterA.Section02.theoremA_knownSimple (G := X)
  have hC := fun (G : Type u) [Group G] [Finite G] =>
    ChapterA.Section02.theoremC_knownSimple (G := G)
  have hc := source_single_clauses S hP hs K hK hqs hgen
  rcases source_normal_geometric_cases hA hC hX S hP hs K hK hgen with h2|h3|hb|hl|hsp|hbi
  · exact (single_odd_linear_false_of_parameter_gt_one hA hX S hP hs K hK hgen h2 hn).elim
  · obtain ⟨p,hp,ho,_,huni|hlin⟩ := h3
    · exact (normal_odd_three_false_of_parameter_gt_one hA hX S hP hs K hK hgen hp ho
        (Or.inr huni.2) hn).elim
    · obtain ⟨_,F,hF,hfin,hcard,e,_⟩ := hlin
      exact (normal_odd_three_false_of_parameter_gt_one hA hX S hP hs K hK hgen hp ho
        (Or.inl ⟨F,hF,hfin,hcard,⟨e⟩⟩) hn).elim
  · cases hb with
    | linear f hf hm =>
      exact ⟨f,by omega,.bender hc
        (.inl (source_linear_borel_model S hP hs K hK hgen hf hm))⟩
    | unitary f hf hm =>
      exact ⟨f,by omega,.bender hc
        (.inr (source_unitary_borel_model S hP hs K hK hgen hf hm))⟩
    | suzuki m hm he =>
      exact ⟨2*m+1,by omega,.bender hc
        (.inl (source_suzuki_borel_model S hP hs K hK hgen hm he))⟩
  · obtain ⟨f,hf,hm⟩ := hl
    have hu := normal_classical_parameter_le hA hX S hP hs K hK hgen (.inr (.inr ⟨hf,hm⟩))
    exact ⟨f,hn.trans_le hu,.diagram hc (source_binary_linear_three_model S hP hs K hK hgen hf hm)⟩
  · obtain ⟨f,hf,hm⟩ := hsp
    exact ⟨f,hf,.diagram hc (source_binary_symplectic_model S hP hs K hK hgen hf hm)⟩
  · exact ((Nat.not_le_of_gt hn) (normal_binary_six_parameter_le S hP hs K hK hgen hbi)).elim

/-- The original known-simple SQTK source supplies the three genuine
binary rows, including the full diagram and source kernel clauses. -/
theorem source_binary_cases_generating_knownSimple
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hn : 1 < generationParameter X) :
    ∃ (K : Subgroup X) (f : ℕ), K.IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (S : Subgroup X) = ⊤ ∧ 1 < f ∧
      ReducedCases (minimalParabolicMax S hP) K S f := by
  have hs : ¬ Group.IsSolvable X := by
    intro hh
    let := hh
    exact (Nat.not_le_of_gt hn) generationParameter_le_one_of_solvable
  obtain ⟨K,hK,hqs,hgen,_⟩ := Structure.source_original_component hX S hP hs
  by_cases hnorm : K.Normal
  · let := hnorm
    obtain ⟨f,hf,hcases⟩ := normal_binary_cases hX S hP hs hn K hK hqs hgen
    exact ⟨K,f,hK,hqs,hgen,hf,hcases⟩
  · rcases source_exchanged_marked_cases ChapterA.Section02.theoremA_knownSimple
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hX S hP hs K hK hgen hnorm with
      ⟨f,hf,hm⟩ | ho
    · have hc := source_exchanged_clauses (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
        hX S hP hs hK hqs hgen hnorm
      exact ⟨K,f,hK,hqs,hgen,by omega,.exchanged hc hm⟩
    · obtain ⟨p,hp,_,h7,hm⟩ := ho
      let : Fact p.Prime := ⟨hp⟩
      have hb := paired_prime_parameter_le_one ChapterA.Section02.theoremA_knownSimple
        hX S hP hs K hK hgen hnorm (p := p) (by omega) hm
      exact (Nat.not_le_of_gt hn hb).elim

/-- The same genuine binary alternatives when generation is not needed
by the consumer. -/
theorem source_binary_cases_knownSimple
    (hX : IsSQTK KnownSimple.IsKnownSimple X) (S : Sylow 2 X)
    (hP : IsMinimalParabolicOver S ⊤) (hn : 1 < generationParameter X) :
    ∃ (K : Subgroup X) (f : ℕ), K.IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ 1 < f ∧
      ReducedCases (minimalParabolicMax S hP) K S f := by
  obtain ⟨K,f,hK,hqs,_,hf,hcases⟩ := source_binary_cases_generating_knownSimple hX S hP hn
  exact ⟨K,f,hK,hqs,hf,hcases⟩

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.NormalizerEscape
