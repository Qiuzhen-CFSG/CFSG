module
public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Simultaneous markings of the alternating-six parabolics

An index-fifteen subgroup containing the standard Sylow subgroup is a
standard duad or syntheme stabilizer. Conjugate a common Sylow only once;
two distinct such subgroups must then have opposite types. The resulting
single isomorphism marks both vertices and their common Sylow together.

The original A₆ component in Chapter13's two-parabolic join consumes this
result, preserving its quotient map and full two-core kernel.
Source: Aschbacher--Smith 13.4.7(1iv), pp.900--901; the six-letter geometry
of I.5, pp.420--422.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.AlternatingPair

/-- The only index-fifteen overgroups of the standard Sylow are its two parabolics. -/
theorem index_fifteen_over_borel (H : Subgroup A6) (hB : a6Borel ≤ H)
    (hi : H.index = 15) : H = a6DuadStabilizer ∨ H = a6SynthemeStabilizer := by
  have hn : H ≠ ⊤ := by
    intro hh
    simp [hh] at hi
  rcases a6_overgroup_borel H hB hn with hd | hs
  · left
    apply le_antisymm hd
    apply relIndex_eq_one.mp
    have hh := relIndex_mul_index hd
    rw [a6DuadStabilizer_index,hi] at hh
    omega
  · right
    apply le_antisymm hs
    apply relIndex_eq_one.mp
    have hh := relIndex_mul_index hs
    rw [a6SynthemeStabilizer_index,hi] at hh
    omega

/-- One isomorphism marks both distinct parabolics and their common Sylow. -/
theorem pair_marking (S : Sylow 2 A6) (P Q : Subgroup A6)
    (hSP : (S : Subgroup A6) ≤ P) (hSQ : (S : Subgroup A6) ≤ Q)
    (hP : P.index = 15) (hQ : Q.index = 15) (hne : P ≠ Q) :
    ∃ e : A6 ≃* A6,
      (S : Subgroup A6).map e.toMonoidHom = a6Borel ∧
      ((P.map e.toMonoidHom = a6DuadStabilizer ∧
        Q.map e.toMonoidHom = a6SynthemeStabilizer) ∨
       (P.map e.toMonoidHom = a6SynthemeStabilizer ∧
        Q.map e.toMonoidHom = a6DuadStabilizer)) := by
  obtain ⟨g,hg,_⟩ := a6_coatoms_over_sylow S
  let a := (MulAut.conj g).mapSubgroup
  have classify (H : Subgroup A6) (hS : (S : Subgroup A6) ≤ H)
      (hi : H.index = 15) :
      a.symm H = a6DuadStabilizer ∨ a.symm H = a6SynthemeStabilizer := by
    apply index_fifteen_over_borel
    · have hh := a.symm.monotone hS
      rwa [←hg,a.symm_apply_apply] at hh
    · change (H.map (MulAut.conj g).symm.toMonoidHom).index = 15
      rw [index_map_of_bijective (MulAut.conj g).symm.bijective]
      exact hi
  have hne' : a.symm P ≠ a.symm Q := fun hh => hne (a.symm.injective hh)
  refine ⟨(MulAut.conj g).symm,?_,?_⟩
  · change a.symm (S : Subgroup A6) = a6Borel
    rw [←hg,a.symm_apply_apply]
  · rcases classify P hSP hP with hp | hp <;>
      rcases classify Q hSQ hQ with hq | hq
    · exact (hne' (hp.trans hq.symm)).elim
    · exact Or.inl ⟨hp,hq⟩
    · exact Or.inr ⟨hp,hq⟩
    · exact (hne' (hp.trans hq.symm)).elim

end Theory.SpecificGroups.SymmetricSix.AlternatingPair
