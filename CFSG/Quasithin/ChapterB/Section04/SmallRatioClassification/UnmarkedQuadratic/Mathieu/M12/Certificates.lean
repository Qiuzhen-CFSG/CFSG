module
public import CFSG.Quasithin.ChapterB.Section04.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12.Contracts

public section
namespace CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12
open Data
private theorem prefix_check_00 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 0 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_01 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 1 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_02 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 2 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_03 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 3 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_04 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 4 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_05 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 5 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_06 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 6 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_07 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 7 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_08 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 8 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_09 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 9 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_10 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 10 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_11 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 11 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_12 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 12 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_13 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 13 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_14 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 14 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_15 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 15 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_16 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 16 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

private theorem prefix_check_17 : ∀ a : Fin 5,
    (prefixCheck) ⟨5 * 17 + a.val, by omega⟩ := by
  unfold prefixCheck
  decide +kernel

theorem prefix_check (i : Fin 90) : (prefixCheck) i := by
  have blocks : ∀ (b : Fin 18) (a : Fin 5), (prefixCheck) ⟨5 * b.val + a.val, by omega⟩ := by
    intro b a
    fin_cases b
    · exact prefix_check_00 a
    · exact prefix_check_01 a
    · exact prefix_check_02 a
    · exact prefix_check_03 a
    · exact prefix_check_04 a
    · exact prefix_check_05 a
    · exact prefix_check_06 a
    · exact prefix_check_07 a
    · exact prefix_check_08 a
    · exact prefix_check_09 a
    · exact prefix_check_10 a
    · exact prefix_check_11 a
    · exact prefix_check_12 a
    · exact prefix_check_13 a
    · exact prefix_check_14 a
    · exact prefix_check_15 a
    · exact prefix_check_16 a
    · exact prefix_check_17 a
  have h := blocks ⟨i.val / 5, by omega⟩ ⟨i.val % 5, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨5 * (i.val / 5) + i.val % 5, by omega⟩ : Fin 90) = i := by
    apply Fin.ext
    change 5 * (i.val / 5) + i.val % 5 = i.val
    omega
  exact hi ▸ h

private theorem matrix_check_00 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 0 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_01 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 1 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_02 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 2 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_03 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 3 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_04 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 4 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_05 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 5 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_06 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 6 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_07 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 7 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_08 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 8 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_09 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 9 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_10 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 10 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_11 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 11 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_12 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 12 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_13 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 13 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_14 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 14 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_15 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 15 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_16 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 16 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_17 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 17 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_18 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 18 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_19 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 19 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_20 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 20 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_21 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 21 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_22 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 22 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_23 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 23 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_24 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 24 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_25 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 25 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_26 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 26 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_27 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 27 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_28 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 28 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_29 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 29 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_30 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 30 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

private theorem matrix_check_31 : ∀ a : Fin 4,
    (matrixCheck) ⟨4 * 31 + a.val, by omega⟩ := by
  unfold matrixCheck
  decide +kernel

theorem matrix_check (i : Fin 128) : (matrixCheck) i := by
  have blocks : ∀ (b : Fin 32) (a : Fin 4), (matrixCheck) ⟨4 * b.val + a.val, by omega⟩ := by
    intro b a
    fin_cases b
    · exact matrix_check_00 a
    · exact matrix_check_01 a
    · exact matrix_check_02 a
    · exact matrix_check_03 a
    · exact matrix_check_04 a
    · exact matrix_check_05 a
    · exact matrix_check_06 a
    · exact matrix_check_07 a
    · exact matrix_check_08 a
    · exact matrix_check_09 a
    · exact matrix_check_10 a
    · exact matrix_check_11 a
    · exact matrix_check_12 a
    · exact matrix_check_13 a
    · exact matrix_check_14 a
    · exact matrix_check_15 a
    · exact matrix_check_16 a
    · exact matrix_check_17 a
    · exact matrix_check_18 a
    · exact matrix_check_19 a
    · exact matrix_check_20 a
    · exact matrix_check_21 a
    · exact matrix_check_22 a
    · exact matrix_check_23 a
    · exact matrix_check_24 a
    · exact matrix_check_25 a
    · exact matrix_check_26 a
    · exact matrix_check_27 a
    · exact matrix_check_28 a
    · exact matrix_check_29 a
    · exact matrix_check_30 a
    · exact matrix_check_31 a
  have h := blocks ⟨i.val / 4, by omega⟩ ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨4 * (i.val / 4) + i.val % 4, by omega⟩ : Fin 128) = i := by
    apply Fin.ext
    change 4 * (i.val / 4) + i.val % 4 = i.val
    omega
  exact hi ▸ h

private theorem square_check_00 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 0 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

private theorem square_check_01 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 1 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

private theorem square_check_02 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 2 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

private theorem square_check_03 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 3 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

private theorem square_check_04 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 4 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

private theorem square_check_05 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 5 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

private theorem square_check_06 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 6 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

private theorem square_check_07 : ∀ a : Fin 16,
    (squareCheck) ⟨16 * 7 + a.val, by omega⟩ := by
  unfold squareCheck
  decide +kernel

theorem square_check (i : Fin 128) : (squareCheck) i := by
  have blocks : ∀ (b : Fin 8) (a : Fin 16), (squareCheck) ⟨16 * b.val + a.val, by omega⟩ := by
    intro b a
    fin_cases b
    · exact square_check_00 a
    · exact square_check_01 a
    · exact square_check_02 a
    · exact square_check_03 a
    · exact square_check_04 a
    · exact square_check_05 a
    · exact square_check_06 a
    · exact square_check_07 a
  have h := blocks ⟨i.val / 16, by omega⟩ ⟨i.val % 16, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨16 * (i.val / 16) + i.val % 16, by omega⟩ : Fin 128) = i := by
    apply Fin.ext
    change 16 * (i.val / 16) + i.val % 16 = i.val
    omega
  exact hi ▸ h

private theorem reject_check_00 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 0 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_01 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 1 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_02 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 2 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_03 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 3 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_04 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 4 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_05 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 5 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_06 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 6 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_07 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 7 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

private theorem reject_check_08 : ∀ a : Fin 4,
    (fun v => ∀ w, rejectionCheck v w) ⟨4 * 8 + a.val, by omega⟩ := by
  unfold rejectionCheck
  decide +kernel

theorem reject_check (i : Fin 36) : (fun v => ∀ w, rejectionCheck v w) i := by
  have blocks : ∀ (b : Fin 9) (a : Fin 4), (fun v => ∀ w, rejectionCheck v w) ⟨4 * b.val + a.val, by omega⟩ := by
    intro b a
    fin_cases b
    · exact reject_check_00 a
    · exact reject_check_01 a
    · exact reject_check_02 a
    · exact reject_check_03 a
    · exact reject_check_04 a
    · exact reject_check_05 a
    · exact reject_check_06 a
    · exact reject_check_07 a
    · exact reject_check_08 a
  have h := blocks ⟨i.val / 4, by omega⟩ ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨4 * (i.val / 4) + i.val % 4, by omega⟩ : Fin 36) = i := by
    apply Fin.ext
    change 4 * (i.val / 4) + i.val % 4 = i.val
    omega
  exact hi ▸ h

private theorem neighbors_check_00 : ∀ a : Fin 6,
    (neighborsCheck) ⟨6 * 0 + a.val, by omega⟩ := by
  unfold neighborsCheck
  decide +kernel

private theorem neighbors_check_01 : ∀ a : Fin 6,
    (neighborsCheck) ⟨6 * 1 + a.val, by omega⟩ := by
  unfold neighborsCheck
  decide +kernel

private theorem neighbors_check_02 : ∀ a : Fin 6,
    (neighborsCheck) ⟨6 * 2 + a.val, by omega⟩ := by
  unfold neighborsCheck
  decide +kernel

private theorem neighbors_check_03 : ∀ a : Fin 6,
    (neighborsCheck) ⟨6 * 3 + a.val, by omega⟩ := by
  unfold neighborsCheck
  decide +kernel

private theorem neighbors_check_04 : ∀ a : Fin 6,
    (neighborsCheck) ⟨6 * 4 + a.val, by omega⟩ := by
  unfold neighborsCheck
  decide +kernel

private theorem neighbors_check_05 : ∀ a : Fin 6,
    (neighborsCheck) ⟨6 * 5 + a.val, by omega⟩ := by
  unfold neighborsCheck
  decide +kernel

theorem neighbors_check (i : Fin 36) : (neighborsCheck) i := by
  have blocks : ∀ (b : Fin 6) (a : Fin 6), (neighborsCheck) ⟨6 * b.val + a.val, by omega⟩ := by
    intro b a
    fin_cases b
    · exact neighbors_check_00 a
    · exact neighbors_check_01 a
    · exact neighbors_check_02 a
    · exact neighbors_check_03 a
    · exact neighbors_check_04 a
    · exact neighbors_check_05 a
  have h := blocks ⟨i.val / 6, by omega⟩ ⟨i.val % 6, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨6 * (i.val / 6) + i.val % 6, by omega⟩ : Fin 36) = i := by
    apply Fin.ext
    change 6 * (i.val / 6) + i.val % 6 = i.val
    omega
  exact hi ▸ h

private theorem rank_check_00 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 0 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_01 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 1 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_02 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 2 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_03 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 3 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_04 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 4 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_05 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 5 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_06 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 6 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_07 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 7 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

private theorem rank_check_08 : ∀ a : Fin 4,
    (rankCheck) ⟨4 * 8 + a.val, by omega⟩ := by
  unfold rankCheck
  decide +kernel

theorem rank_check (i : Fin 36) : (rankCheck) i := by
  have blocks : ∀ (b : Fin 9) (a : Fin 4), (rankCheck) ⟨4 * b.val + a.val, by omega⟩ := by
    intro b a
    fin_cases b
    · exact rank_check_00 a
    · exact rank_check_01 a
    · exact rank_check_02 a
    · exact rank_check_03 a
    · exact rank_check_04 a
    · exact rank_check_05 a
    · exact rank_check_06 a
    · exact rank_check_07 a
    · exact rank_check_08 a
  have h := blocks ⟨i.val / 4, by omega⟩ ⟨i.val % 4, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨4 * (i.val / 4) + i.val % 4, by omega⟩ : Fin 36) = i := by
    apply Fin.ext
    change 4 * (i.val / 4) + i.val % 4 = i.val
    omega
  exact hi ▸ h

end CFSG.Quasithin.ChapterB.SmallRatioClassification.UnmarkedQuadratic.Mathieu.M12
