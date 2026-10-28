module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BinaryQuotients
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.QuinticSolvableParabolics.BinaryRows

/-!
# Every binary reduced quotient row at the original quintic pair

The left local quotient has order ten or twenty. Its inclusion-induced
embedding rules out the previously unhandled full left binary quotient.
On the right, the binary quotient gives solvability. The original quintic
hypotheses imply S₀ = S, so these conclusions concern both full original
parabolics and the actual opposite factor R.

All three quotient conventions of the reduced catalogue are handled in
both orientations. The source binary row remains an explicit input;
regular and exceptional row selection retain their source producers.
No marked-model conclusion is inferred from TYPE data.

Source: Aschbacher--Smith F.1.12, pp.263--264; DGS, Groups and Graphs
(1985), (12.9)--(13.1), pp.186--191, and (15.1)--(15.3), pp.226--231.
-/

public noncomputable section
open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BinaryQuotients
open SuzukiContainment
variable {G : Type*} [Group G] {K R S : Subgroup G}

/-- The missing left full-parabolic binary clause is impossible in the
original quintic pair. The full quotient need not equal K/O₂(K): its order
must be divisible by 10 or 20 through the inclusion-induced embedding. -/
theorem quintic_no_binary_full_left (h : HypothesisF11 ![K,R] S)
    (hSK : S ≤ K) (hi : S.relIndex K = 5) :
    ¬ ClassicalGroup.IsPSL
      (parabolic ![K,R] S 0 ⧸ pCore 2 (parabolic ![K,R] S 0)) 2 2 := by
  apply no_binary_full_of_local_quotient_card h 0
  rcases h.quintic_quotient_card hSK hi with hc | hc <;>
    change ¬ Nat.card (K ⧸ pCore 2 K) ∣ 6 <;> rw [hc] <;> decide

/-- A binary quotient on either full reduced endpoint makes the ORIGINAL
opposite endpoint solvable. The quintic source fixes S₀ = S internally. -/
theorem quintic_opposite_solvable_of_binary_reduced_parabolic
    (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K) (hi : S.relIndex K = 5)
    (i : Fin 2)
    (he : ClassicalGroup.IsPSL
      (parabolic ![K,R] (reducedSylow ![K,R] S) i ⧸
        pCore 2 (parabolic ![K,R] (reducedSylow ![K,R] S) i)) 2 2) :
    Group.IsSolvable (parabolic ![K,R] S 1) := by
  rw [h.quintic_reducedSylow_eq hSK] at he
  fin_cases i
  · exact (quintic_no_binary_full_left h hSK hi he).elim
  · exact h.quintic_solvable_of_binary_parabolic_right he

/-- All three literal binary quotient conventions in the reduced catalogue
give both original solvable parabolics in the quintic F.1.12 consumer.
No TYPE-to-model identification or ambient Sylow hypothesis is used. -/
theorem quintic_parabolics_solvable_of_binary_rows
    (h : HypothesisF11 ![K,R] S) (hSK : S ≤ K) (hi : S.relIndex K = 5)
    (he : (∃ i : Fin 2, ClassicalGroup.IsPSL
        (![K,R] i ⧸ pCore 2 (![K,R] i)) 2 2) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL
        ((![K,R] i ⊔ reducedSylow ![K,R] S : Subgroup G) ⧸
          pCore 2 (![K,R] i ⊔ reducedSylow ![K,R] S : Subgroup G)) 2 2) ∨
      (∃ i : Fin 2, ClassicalGroup.IsPSL
        (parabolic ![K,R] (reducedSylow ![K,R] S) i ⧸
          pCore 2 (parabolic ![K,R] (reducedSylow ![K,R] S) i)) 2 2)) :
    Group.IsSolvable (parabolic ![K,R] S 0) ∧
      Group.IsSolvable (parabolic ![K,R] S 1) ∧ Group.IsSolvable R := by
  have hs : Group.IsSolvable (parabolic ![K,R] S 1) := by
    rcases he with ⟨i,he⟩ | ⟨i,he⟩ | ⟨i,he⟩
    · fin_cases i
      · exact (h.quintic_no_binary_local_left hSK hi he).elim
      · exact h.quintic_solvable_of_binary_local_right he
    · fin_cases i
      · exact (h.quintic_no_binary_join_left hSK hi he).elim
      · exact h.quintic_solvable_of_binary_join_right hSK hi he
    · exact quintic_opposite_solvable_of_binary_reduced_parabolic h hSK hi i he
  let := hs
  exact ⟨h.quintic_first_solvable hSK hi, hs,
    Group.isSolvable_of_isSolvable_injective
      (f := inclusion (show R ≤ parabolic ![K,R] S 1 from le_sup_left.trans le_sup_left))
      (inclusion_injective _)⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BinaryQuotients
