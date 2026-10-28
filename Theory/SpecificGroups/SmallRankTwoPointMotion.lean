module
public import Theory.SpecificGroups.PSL3Two.Parabolics.TwoKernel
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoKernel

/-!
# Moving points in the three smallest rank-two parabolic geometries

For SL₃(2), A₆ and S₆, the interval above a Sylow two-subgroup consists
of the Sylow subgroup, two maximal parabolics, and the whole group. Two
proper Sylow overgroups generating the group must be those parabolics.
Any further Sylow overgroup containing neither generator is therefore the
Sylow subgroup itself. Applied to a point stabilizer, this says that moving
the same Sylow-fixed point by both generators precludes any extra fixer.

The proofs transport the established matrix and permutation subgroup
lattices along actual group isomorphisms. The consumer is the point-motion
step of Aschbacher--Smith 13.2.12, printed p.882.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.SpecificGroups.SmallRankTwoPointMotion
/-- For any of the three actual model groups, a Sylow overgroup avoiding
both proper generators equals the Sylow subgroup itself. -/
theorem sylow_overgroup_eq_of_avoids_generators {D : Type*} [Group D] [Finite D]
    (hmodel : Nonempty (D ≃* SL(3,ZMod 2)) ∨
      Nonempty (D ≃* alternatingGroup (Fin 6)) ∨ Nonempty (D ≃* Equiv.Perm (Fin 6)))
    (S : Sylow 2 D) (A B C : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hSB : (S : Subgroup D) ≤ B)
    (hgen : A ⊔ B = ⊤) (hA : A ≠ ⊤) (hB : B ≠ ⊤)
    (hSC : (S : Subgroup D) ≤ C) (hAC : ¬ A ≤ C) (hBC : ¬ B ≤ C) :
    C = (S : Subgroup D) := by
  have hk {X : Type} [Group X] (e : D ≃* X) : IsPGroup 2 e.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr e.injective]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hi : ∃ P Q : Subgroup D, IsCoatom P ∧ IsCoatom Q ∧
      ∀ U : Subgroup D, (S : Subgroup D) ≤ U →
        U = (S : Subgroup D) ∨ U = P ∨ U = Q ∨ U = ⊤ := by
    rcases hmodel with he | he | he <;> obtain ⟨e⟩ := he
    · let f := e.trans Matrix.PSL3Two.equiv
      obtain ⟨P,Q,hP,hQ,_,_,_,_,_,_,hi⟩ :=
        Matrix.PSL3Two.two_kernel_parabolics S f.toMonoidHom f.surjective (hk f)
      exact ⟨P,Q,hP,hQ,hi⟩
    · obtain ⟨P,Q,hP,hQ,_,_,_,_,_,_,hi⟩ :=
        SymmetricSix.alternating_two_kernel_parabolics S e.toMonoidHom e.surjective (hk e)
      exact ⟨P,Q,hP,hQ,hi⟩
    · obtain ⟨P,Q,hP,hQ,_,_,_,_,_,_,hi⟩ :=
        SymmetricSix.symmetric_two_kernel_parabolics S e.toMonoidHom e.surjective (hk e)
      exact ⟨P,Q,hP,hQ,hi⟩
  obtain ⟨P,Q,hP,hQ,hi⟩ := hi
  have ha : A = P ∨ A = Q := by
    rcases hi A hSA with h | h | h | h
    · exact (hAC (h ▸ hSC)).elim
    · exact Or.inl h
    · exact Or.inr h
    · exact (hA h).elim
  have hb : B = P ∨ B = Q := by
    rcases hi B hSB with h | h | h | h
    · exact (hBC (h ▸ hSC)).elim
    · exact Or.inl h
    · exact Or.inr h
    · exact (hB h).elim
  rcases hi C hSC with h | h | h | h
  · exact h
  · rcases ha with ha | ha
    · exact (hAC (ha ▸ h.ge)).elim
    · rcases hb with hb | hb
      · exact (hBC (hb ▸ h.ge)).elim
      · rw [ha,hb,sup_idem] at hgen
        exact (hQ.ne_top hgen).elim
  · rcases ha with ha | ha
    · rcases hb with hb | hb
      · rw [ha,hb,sup_idem] at hgen
        exact (hP.ne_top hgen).elim
      · exact (hBC (hb ▸ h.ge)).elim
    · exact (hAC (ha ▸ h.ge)).elim
  · exact (hAC (h ▸ le_top)).elim
/-- These three actual carriers are smaller than a cubic A₆ cover. -/
theorem card_lt_1080 {D : Type*} [Group D]
    (hmodel : Nonempty (D ≃* SL(3,ZMod 2)) ∨
      Nonempty (D ≃* alternatingGroup (Fin 6)) ∨ Nonempty (D ≃* Equiv.Perm (Fin 6))) :
    Nat.card D < 1080 := by
  rcases hmodel with he | he | he <;> obtain ⟨e⟩ := he
  · rw [Nat.card_congr (e.trans Matrix.PSL3Two.equiv).toEquiv,Matrix.PSL3Two.card_PSL]
    decide
  · rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    decide
  · rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
end Theory.SpecificGroups.SmallRankTwoPointMotion
