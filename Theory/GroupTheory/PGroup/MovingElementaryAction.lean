module

public import Theory.GroupTheory.PGroup.NormalFourNormalizerGrowth

/-!
# Fixed-point-free action of a moving elementary subgroup

Let `V` normalize the elementary join `A ⊔ B` and centralize `A`. Assume
distinct `V`-conjugates of `B` are disjoint, normalization of `B` by all of
`V` forces centralization, and an element of `V` fixing a nonidentity
element of `B` normalizes `B`. Local omega control then upgrades a
nontrivial action to a fixed-point-free cross action.

The key invariant is `⁅A ⊔ B, zpowers v⁆`. If `v` normalizes `B`, this
subgroup lies in `B` and is preserved by `V`. Intersection rigidity either
makes it trivial or forces all of `V` to normalize `B`.

This isolates the elementary action argument used in Janko–Thompson,
Math. Z. 113 (1970), Lemma 5.1 and its application on printed p.395.
-/

namespace Subgroup

open scoped commutatorElement

/-- Intersection rigidity and local normalization turn a moving elementary
subgroup into a fixed-point-free actor. -/
public theorem cross_action_of_moving_elementary
    {P : Type*} [Group P] (A B V : Subgroup P) [A.Normal]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 2 B] [IsElementaryAbelian 2 V]
    (hBA : B ≤ centralizer (A : Set P))
    (hVN : V ≤ normalizer ((A ⊔ B : Subgroup P) : Set P))
    (hVA : V ≤ centralizer (A : Set P)) (hd : Disjoint A V)
    (hnot : ¬ V ≤ centralizer ((A ⊔ B : Subgroup P) : Set P))
    (hOmega : (omega₁ (centralizer ((A ⊔ B : Subgroup P) : Set P)) (p := 2)).map
      (centralizer ((A ⊔ B : Subgroup P) : Set P)).subtype = A ⊔ B)
    (hcontrol : ∀ v ∈ V, ∀ b ∈ B, b ≠ 1 → Commute v b →
      v ∈ normalizer (B : Set P))
    (hnormcomm : V ≤ normalizer (B : Set P) → V ≤ centralizer (B : Set P))
    (hrigid : ∀ u ∈ V, B.map (MulAut.conj u).toMonoidHom ≠ B →
      Disjoint B (B.map (MulAut.conj u).toMonoidHom)) :
    ∀ v ∈ V, v ≠ 1 → ∀ b ∈ B, b ≠ 1 → ¬ Commute v b := by
  let E := A ⊔ B
  let Y := centralizer (E : Set P)
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.sup_of_le_centralizer hBA
  have hcomm (hn : V ≤ normalizer (B : Set P)) : False := by
    apply hnot
    intro v hv e he
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_left.mp he
    have hva := hVA hv a ha
    have hvb := hnormcomm hn hv b hb
    calc
      a * b * v = a * (b * v) := mul_assoc _ _ _
      _ = a * (v * b) := by rw [hvb]
      _ = v * (a * b) := by rw [← mul_assoc, hva, mul_assoc]
  have hkernel : ∀ v ∈ V, v ∈ Y → v = 1 := by
    intro v hv hvY
    by_contra hv1
    have hvE : v ∈ E := by
      change v ∈ A ⊔ B
      rw [← hOmega]
      refine ⟨⟨v, hvY⟩, subset_closure ?_, rfl⟩
      apply Subtype.ext
      change v ^ (2 ^ 1) = 1
      simpa using elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp hvE
    have hb1 : b ≠ 1 := by
      intro he
      have hav : a = v := by simpa [he] using hab
      exact hv1 (disjoint_def.mp hd (hav ▸ ha) hv)
    apply hcomm
    intro u hu
    apply hcontrol u hu b hb hb1
    have huv := V.le_centralizer hu v hv
    have hua := hVA hu a ha
    change u * b = b * u
    apply mul_left_cancel (a := a)
    calc
      a * (u * b) = u * (a * b) := by rw [← mul_assoc, hua, mul_assoc]
      _ = (a * b) * u := by rw [hab, huv]
      _ = a * (b * u) := mul_assoc _ _ _
  intro v hv hv1 b hb hb1 hcommvb
  have hvN := hcontrol v hv b hb hb1 hcommvb
  let K := zpowers v
  let D := ⁅E, K⁆
  have hKB : K ≤ normalizer (B : Set P) := zpowers_le.mpr hvN
  have hKA : K ≤ centralizer (A : Set P) := zpowers_le.mpr (hVA hv)
  have hDB : D ≤ B := by
    apply commutator_le.mpr
    intro e he k hk
    obtain ⟨a, ha, c, hc, rfl⟩ := mem_sup_of_normal_left.mp he
    have hac := hBA hc a ha
    have hak := hKA hk a ha
    have hid : ⁅a * c, k⁆ = ⁅c, k⁆ := by
      simp only [commutatorElement_def, mul_inv_rev]
      calc
        a * c * k * (c⁻¹ * a⁻¹) * k⁻¹ =
            c * k * c⁻¹ * (a * a⁻¹) * k⁻¹ := by
          rw [hac, mul_assoc c a k, hak]
          have hai : a * c⁻¹ = c⁻¹ * a := (show Commute a c from hac).inv_right.eq
          simp only [mul_assoc]
          rw [← mul_assoc a c⁻¹, hai]
          group
        _ = c * k * c⁻¹ * k⁻¹ := by simp
    rw [hid]
    exact le_normalizer_iff_commutator_le_left.mp hKB
      (commutator_mem_commutator hc hk)
  have hVD : V ≤ normalizer (D : Set P) := by
    intro u hu
    apply mem_normalizer_iff_map_conj_eq.mpr
    change D.map (MulAut.conj u).toMonoidHom = D
    dsimp [D]
    rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hVN hu)]
    have hKu : K.map (MulAut.conj u).toMonoidHom = K := by
      apply mem_normalizer_iff_map_conj_eq.mp
      apply centralizer_le_normalizer
      intro k hk
      exact (le_centralizer_iff.mp (zpowers_le.mpr (V.le_centralizer hv)))
        hu k hk
    change ⁅E, K.map (MulAut.conj u).toMonoidHom⁆ = ⁅E, K⁆
    rw [hKu]
  have hDbot : D = ⊥ := by
    by_contra hD
    apply hcomm
    intro u hu
    apply mem_normalizer_iff_map_conj_eq.mpr
    by_contra heq
    have hDD : D ≤ B.map (MulAut.conj u).toMonoidHom := by
      rw [← mem_normalizer_iff_map_conj_eq.mp (hVD hu)]
      exact map_mono hDB
    exact hD (le_bot_iff.mp ((disjoint_iff.mp (hrigid u hu heq)) ▸ le_inf hDB hDD))
  have hvY : v ∈ Y := by
    have hEK : E ≤ centralizer (K : Set P) :=
      commutator_eq_bot_iff_le_centralizer.mp hDbot
    exact le_centralizer_iff.mp hEK (mem_zpowers v)
  exact hv1 (hkernel v hv hvY)

end Subgroup
