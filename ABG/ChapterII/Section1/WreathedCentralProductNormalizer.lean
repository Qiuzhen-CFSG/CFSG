module
public import ABG.ChapterII.Section1.WreathedCentralProductCoordinates
public import ABG.ChapterII.Section1.WreathedBaseFour

/-!
# Normalizer index of the canonical quaternion central product

The canonical exceptional subgroup `V` in ABG Chapter II §1 Lemma 3(ii)
(article p.10) has index two in its normalizer, for every wreathed height
`n ≥ 2`.

The coordinate description gives `V = <x₂,z>Z(S)`. Conjugation preserves
the center and sends `x₂` into the normal four-group `T`, already contained
in `V`; thus an element normalizes `V` exactly when its conjugate of `z`
lies in `V`. Conjugation by `s^i*t^j*z^k` sends `z` to
`s^(i-j)*t^(j-i)*z`. The membership criterion for `V` therefore says that
`2^(n-2)` divides `i-j`. In contrast, membership in `V` requires divisibility
by `2^(n-1)`. The relative index-two criterion now uses the two cosets
represented by `1` and `s^(2^(n-2))`. This includes height two without an
exception and retains the actual subgroup of the chosen presentation.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem normal_form_conj_z (i j k : ℤ) :
    (P.s ^ i * P.t ^ j * P.z ^ k) * P.z * (P.s ^ i * P.t ^ j * P.z ^ k)⁻¹ =
      P.s ^ (i-j) * P.t ^ (j-i) * P.z := by
  have hs : SemiconjBy P.z P.s P.t := P.z_mul_s
  have ht : SemiconjBy P.z P.t P.s := P.z_mul_t
  have hc : Commute P.s P.t := P.commute
  calc
    _ = P.s ^ i * P.t ^ j * (P.z * P.t ^ (-j)) * P.s ^ (-i) := by
      simp only [zpow_neg]; group
    _ = P.s ^ i * P.t ^ j * (P.s ^ (-j) * P.z) * P.s ^ (-i) := by rw [(ht.zpow_right (-j)).eq]
    _ = P.s ^ i * (P.t ^ j * P.s ^ (-j)) * (P.z * P.s ^ (-i)) := by group
    _ = P.s ^ i * (P.s ^ (-j) * P.t ^ j) * (P.t ^ (-i) * P.z) := by
      rw [← (hc.zpow_zpow (-j) j).eq, (hs.zpow_right (-i)).eq]
    _ = P.s ^ (i-j) * P.t ^ (j-i) * P.z := by simp only [sub_eq_add_neg,zpow_add]; group

private theorem normalizer_iff_conj_z (V : Subgroup S)
    (hV : V = Subgroup.closure ({P.x₂,P.z} : Set S) ⊔ Subgroup.center S) (g : S) :
    g ∈ Subgroup.normalizer (V : Set S) ↔ g * P.z * g⁻¹ ∈ V := by
  have hZ : Subgroup.center S ≤ V := by rw [hV]; exact le_sup_right
  have hx₂ : P.x₂ ∈ V := by
    rw [hV]
    exact (show Subgroup.closure ({P.x₂,P.z} : Set S) ≤ _ from le_sup_left)
      (Subgroup.subset_closure (by simp))
  have hz : P.z ∈ V := by
    rw [hV]
    exact (show Subgroup.closure ({P.x₂,P.z} : Set S) ≤ _ from le_sup_left)
      (Subgroup.subset_closure (by simp))
  have hx : P.x ∈ V := hZ P.x_mem_center
  have hx₃ : P.x₃ ∈ V := by
    have h := V.mul_mem (V.inv_mem hx₂) hx
    simpa only [P.x_eq_x₂_mul_x₃, inv_mul_cancel_left] using h
  have hT : P.T ≤ V := by
    rw [T]
    apply (Subgroup.closure_le _).mpr
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact hx
    · exact hx₂
    · exact hx₃
  constructor
  · intro h
    exact ((Subgroup.mem_normalizer_iff.mp h) P.z).mp hz
  · intro h
    let : Finite S := Nat.finite_of_card_ne_zero (by rw [P.card]; positivity)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge
    · conv_lhs => rw [hV]
      rw [Subgroup.map_sup]
      apply sup_le
      · rw [MonoidHom.map_closure]
        apply (Subgroup.closure_le _).mpr
        rintro _ ⟨a,ha,rfl⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl
        · exact hT (P.T_normal.conj_mem _ (Subgroup.subset_closure (by simp)) g)
        · exact h
      · rintro _ ⟨a,ha,rfl⟩
        exact hZ ((inferInstance : (Subgroup.center S).Normal).conj_mem a ha g)
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

private theorem normal_form_mem_normalizer_iff (V : Subgroup S)
    (hV : V = Subgroup.closure ({P.x₂,P.z} : Set S) ⊔ Subgroup.center S)
    (hmem : ∀ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k ∈ V ↔
      ((2^(n-1) : ℕ) : ℤ) ∣ i-j) (i j k : ℤ) :
    P.s ^ i * P.t ^ j * P.z ^ k ∈ Subgroup.normalizer (V : Set S) ↔
      ((2^(n-2) : ℕ) : ℤ) ∣ i-j := by
  rw [P.normalizer_iff_conj_z V hV, P.normal_form_conj_z]
  rw [← zpow_one P.z, hmem]
  have hhalf : ((2^(n-1) : ℕ) : ℤ) = 2 * ((2^(n-2) : ℕ) : ℤ) := by
    have hn : n-1 = (n-2)+1 := by have := P.height; omega
    rw [hn, pow_succ]
    push_cast
    ring
  rw [hhalf, show i-j-(j-i) = 2*(i-j) by ring]
  exact mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)

private theorem normalizer_index_of_coordinates (V : Subgroup S)
    (hV : V = Subgroup.closure ({P.x₂,P.z} : Set S) ⊔ Subgroup.center S)
    (hmem : ∀ i j k : ℤ, P.s ^ i * P.t ^ j * P.z ^ k ∈ V ↔
      ((2^(n-1) : ℕ) : ℤ) ∣ i-j) :
    V.relIndex (Subgroup.normalizer (V : Set S)) = 2 := by
  let q : ℤ := ((2^(n-2) : ℕ) : ℤ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hhalf : ((2^(n-1) : ℕ) : ℤ) = q * 2 := by
    have hn : n-1 = (n-2)+1 := by have := P.height; omega
    rw [hn, pow_succ]
    push_cast
    rfl
  have hwN : P.s ^ q ∈ Subgroup.normalizer (V : Set S) := by
    have h := (P.normal_form_mem_normalizer_iff V hV hmem q 0 0).mpr (by simp [q])
    simpa only [zpow_zero, mul_one] using h
  have hwV : P.s ^ q ∉ V := by
    intro h
    have hdiv := (hmem q 0 0).mp (by simpa only [zpow_zero, mul_one] using h)
    rw [sub_zero, hhalf] at hdiv
    have he : (2 : ℤ) ∣ 1 := (mul_dvd_mul_iff_left hq.ne').mp (by simpa using hdiv)
    norm_num at he
  apply Subgroup.relIndex_eq_two_iff_exists_notMem_and'.mpr
  refine ⟨P.s ^ q, hwN, hwV, ?_⟩
  intro g hg
  obtain ⟨i,j,b,rfl⟩ := P.exists_normal_form g
  let I : ℤ := i.val
  let J : ℤ := j.val
  let B : ℤ := b.val
  have hg' : P.s ^ I * P.t ^ J * P.z ^ B ∈ Subgroup.normalizer (V : Set S) := by
    simpa only [I,J,B,zpow_natCast] using hg
  obtain ⟨l,hl⟩ := (P.normal_form_mem_normalizer_iff V hV hmem I J B).mp hg'
  have hpar : (2 : ℤ) ∣ l ∨ (2 : ℤ) ∣ l+1 := by omega
  rcases hpar with he | ho
  · right
    have hh : ((2^(n-1) : ℕ) : ℤ) ∣ I-J := by
      rw [hhalf, hl]
      exact mul_dvd_mul_left q he
    have h := (hmem I J B).mpr hh
    simpa only [I,J,B,zpow_natCast] using h
  · left
    have hh : ((2^(n-1) : ℕ) : ℤ) ∣ (q+I)-J := by
      rw [hhalf]
      have heq : (q+I)-J = q*(l+1) := by dsimp [q] at *; linear_combination hl
      rw [heq]
      exact mul_dvd_mul_left q ho
    have h := (hmem (q+I) J B).mpr hh
    simpa only [zpow_add, mul_assoc, I,J,B,zpow_natCast] using h

public theorem V_normalizer_index :
    P.V.relIndex (Subgroup.normalizer (P.V : Set S)) = 2 :=
  P.normalizer_index_of_coordinates P.V P.V_eq_generators_center P.normal_form_zpow_mem_V_iff

end ABG.Wreathed.Presentation
