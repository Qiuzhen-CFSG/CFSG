module

public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Reduction of index-three Sylow overgroups in S₆

The exhaustive overgroup theorem for the flag stabilizer and the index
formula force each index-three overgroup to be a standard parabolic.
Sylow conjugacy applies this simultaneously to a pair. If the pair
generates S₆, its two members must be the distinct parabolics.

Source: Aschbacher–Smith, the paragraph following 15.4.23, printed p.1165;
the six-letter parabolic geometry is developed in I.5.
-/

@[expose] public section

open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition

theorem index_three_over_borel (H : Subgroup S6) (hB : borel ≤ H)
    (hi : borel.relIndex H = 3) :
    H = duadStabilizer ∨ H = synthemeStabilizer := by
  have hidx : H.index = 15 := by
    have h := relIndex_mul_index hB
    rw [hi, borel_index] at h
    omega
  have hn : H ≠ ⊤ := by
    intro h
    simp [h] at hidx
  rcases overgroup_borel H hB hn with hd | hs
  · left
    apply le_antisymm hd
    apply relIndex_eq_one.mp
    have h := relIndex_mul_index hd
    rw [duadStabilizer_index, hidx] at h
    omega
  · right
    apply le_antisymm hs
    apply relIndex_eq_one.mp
    have h := relIndex_mul_index hs
    rw [synthemeStabilizer_index, hidx] at h
    omega

theorem pair_conjugate (T : Sylow 2 S6) (H₁ H₂ : Subgroup S6)
    (h₁ : (T : Subgroup S6) ≤ H₁) (h₂ : (T : Subgroup S6) ≤ H₂)
    (hi₁ : (T : Subgroup S6).relIndex H₁ = 3)
    (hi₂ : (T : Subgroup S6).relIndex H₂ = 3) (hgen : H₁ ⊔ H₂ = ⊤) :
    ∃ g : S6,
      (H₁ = (MulAut.conj g).mapSubgroup duadStabilizer ∧
       H₂ = (MulAut.conj g).mapSubgroup synthemeStabilizer) ∨
      (H₁ = (MulAut.conj g).mapSubgroup synthemeStabilizer ∧
       H₂ = (MulAut.conj g).mapSubgroup duadStabilizer) := by
  obtain ⟨g, hg, _⟩ := coatoms_over_sylow T
  let e := (MulAut.conj g).mapSubgroup
  have classify (H : Subgroup S6) (h : (T : Subgroup S6) ≤ H)
      (hi : (T : Subgroup S6).relIndex H = 3) :
      H = e duadStabilizer ∨ H = e synthemeStabilizer := by
    have hb : borel ≤ e.symm H := by
      have hh := e.symm.monotone h
      rwa [← hg, e.symm_apply_apply] at hh
    have hidx : borel.relIndex (e.symm H) = 3 := by
      have hh := relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) borel (e.symm H) (MulAut.conj g).injective
      change (e borel).relIndex (e (e.symm H)) = _ at hh
      rw [hg, e.apply_symm_apply] at hh
      exact hh.symm.trans hi
    rcases index_three_over_borel (e.symm H) hb hidx with hh | hh
    · exact Or.inl ((e.apply_symm_apply H).symm.trans (congrArg e hh))
    · exact Or.inr ((e.apply_symm_apply H).symm.trans (congrArg e hh))
  have hne : H₁ ≠ H₂ := by
    intro hh
    have ht : H₁ = ⊤ := by simpa [← hh] using hgen
    rcases classify H₁ h₁ hi₁ with hd | hs
    · exact duadStabilizer_ne_top (e.injective (by simpa using hd.symm.trans ht))
    · exact synthemeStabilizer_ne_top (e.injective (by simpa using hs.symm.trans ht))
  refine ⟨g, ?_⟩
  rcases classify H₁ h₁ hi₁ with hd₁ | hs₁ <;>
    rcases classify H₂ h₂ hi₂ with hd₂ | hs₂
  · exact (hne (hd₁.trans hd₂.symm)).elim
  · exact Or.inl ⟨hd₁, hs₂⟩
  · exact Or.inr ⟨hs₁, hd₂⟩
  · exact (hne (hs₁.trans hs₂.symm)).elim

end Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
