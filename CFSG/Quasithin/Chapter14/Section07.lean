module
public import Theory.GroupTheory.Commutator.ConjugateGeneration

/-!
# Section 14.7: the abelian-generated L₃(2) case

The local analysis uses `S = ⟨U_H^L⟩`, `E = [U_H,Q]`, and `R = ⟨E^L⟩`.
This module establishes the algebraic steps in Lemma 14.7.13(1),(3).
The first commutes conjugate generation with taking commutators with `Q`.
For the second, the two-orbit description in Lemma 14.7.12 makes `E`
centralize every generator of `S`; invariance under `L` then gives the
same statement for `R`.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
combined manuscript dated 1 March 2004, §14.7, printed pp. 1042–1078,
especially Lemmas 14.7.3, 14.7.12–13 on pp. 1043 and 1046.
The subgroup hypotheses below are explicit so these algebraic steps do
not depend on the representation-theoretic construction of the local groups.
-/

namespace CFSG.Quasithin.Chapter14.Section07

open Subgroup

variable {G : Type*} [Group G]

/-- The containment used in Lemma 14.7.3(2). -/
public theorem generated_le_Q (U L Q : Subgroup G)
    (hUQ : U ≤ Q) (hLQ : L ≤ normalizer Q) :
    (⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom) ≤ Q :=
  iSup_conjugates_le_of_le_normalizer U L Q hUQ hLQ

/-- Lemma 14.7.13(1): `[S,Q] = R`, with `S` and `R` expanded. -/
public theorem generated_commutator_eq (U L Q : Subgroup G)
    (hUQ : U ≤ Q) (hLQ : L ≤ normalizer Q) :
    ⁅⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom, Q⁆ =
      ⨆ l : L, (⁅U, Q⁆).map (MulAut.conj (l : G)).toMonoidHom :=
  commutator_iSup_conjugates U L Q hUQ hLQ

/-- Lemma 14.7.13(3), using the orbit decomposition of Lemma 14.7.12(2).
Here `A = U_α` and `P = L₁T`; the intersection on the right represents
`Z(S)` as a subgroup of the ambient group. -/
public theorem generated_commutator_le_center (U A L P Q : Subgroup G)
    [IsMulCommutative U] (hQU : Q ≤ normalizer U)
    (hPU : P ≤ normalizer U) (hPQ : P ≤ normalizer Q)
    (hEA : ⁅⁅U, Q⁆, A⁆ = ⊥)
    (hcover : ∀ l : L, U.map (MulAut.conj (l : G)).toMonoidHom = U ∨
      ∃ p : P, U.map (MulAut.conj (l : G)).toMonoidHom =
        A.map (MulAut.conj (p : G)).toMonoidHom) :
    (⨆ l : L, (⁅U, Q⁆).map (MulAut.conj (l : G)).toMonoidHom) ≤
      (⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom) ⊓
      centralizer ((⨆ l : L, U.map (MulAut.conj (l : G)).toMonoidHom) : Subgroup G) := by
  have hEU : ⁅U, Q⁆ ≤ U := le_normalizer_iff_commutator_le_left.mp hQU
  apply iSup_conjugates_le_center_of_two_orbits U ⁅U, Q⁆ A L P hEU
  · intro p hp
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hU : U.map (MulAut.conj p).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (hPU hp)
    have hQ : Q.map (MulAut.conj p).toMonoidHom = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hPQ hp)
    change (⁅U, Q⁆).map (MulAut.conj p).toMonoidHom = ⁅U, Q⁆
    rw [map_commutator, hU, hQ]
  · exact eq_bot_iff.mpr ((commutator_mono hEU le_rfl).trans
      (commutator_self_eq_bot_iff.mpr inferInstance).le)
  · exact hEA
  · exact hcover

end CFSG.Quasithin.Chapter14.Section07
