module

public import Theory.AlgebraicGroup.RootSystems.Classical

/-!
# Simultaneous positivity for D4 root pairs

A word in the four simple reflections acts on the actual standard root pairing.
Maximize the sum of the two heights in its finite orbit. The resulting sum is
nonnegative on every simple coroot. Symmetry of the D4 pairing and the bound
on pairings of distinct nonopposite roots then force both roots to be positive.
This gives a structural proof, without an enumeration certificate.

Sources: GLS3, §1.12; Steinberg (1963), §2, reduction to a positive root system.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
public noncomputable section

@[expose] def d4Word : List (Fin 4) → Equiv.Perm (TypeDRootIndex 4)
  | [] => Equiv.refl _
  | i :: w => (d4Word w).trans ((typeDRootPairing 2).reflectionPerm (typeDSimpleRootIndex 2 i))

theorem d4Word_append (w v : List (Fin 4)) (a : TypeDRootIndex 4) :
    d4Word (w ++ v) a = d4Word w (d4Word v a) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simpa only [List.cons_append, d4Word, Equiv.trans_apply] using
      congrArg ((typeDRootPairing 2).reflectionPerm (typeDSimpleRootIndex 2 i)) ih

theorem d4Word_neg (w : List (Fin 4)) (a : TypeDRootIndex 4) :
    let P := typeDRootPairing 2
    d4Word w (P.reflectionPerm a a) = P.reflectionPerm (d4Word w a) (d4Word w a) := by
  let P := typeDRootPairing 2
  induction w with
  | nil => rfl
  | cons i w ih =>
    change P.reflectionPerm _ (d4Word w (P.reflectionPerm a a)) = _
    rw [ih]
    apply P.root.injective
    change P.root (P.reflectionPerm _ (P.reflectionPerm (d4Word w a) (d4Word w a))) =
      P.root (P.reflectionPerm (P.reflectionPerm _ (d4Word w a))
        (P.reflectionPerm _ (d4Word w a)))
    rw [P.root_reflectionPerm, P.root_reflectionPerm, P.reflection_apply_self,
      map_neg, P.root_reflectionPerm, P.reflection_apply_self, P.root_reflectionPerm]

theorem d4Word_sum_iff (w : List (Fin 4)) (a b c : TypeDRootIndex 4) :
    let P := typeDRootPairing 2
    P.root (d4Word w c) = P.root (d4Word w a) + P.root (d4Word w b) ↔
      P.root c = P.root a + P.root b := by
  let P := typeDRootPairing 2
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [d4Word, Equiv.trans_apply, (typeDRootPairing 2).root_reflectionPerm, ← map_add,
      ((typeDRootPairing 2).reflection _).injective.eq_iff]
    exact ih

theorem d4Word_to_simple (a : TypeDRootIndex 4) :
    ∃ (w : List (Fin 4)) (i : Fin 4), d4Word w a = typeDSimpleRootIndex 2 i := by
  let P := typeDRootPairing 2
  apply (typeDRootPairing_base 2).induction_reflect a
  · intro a ha
    obtain ⟨w, i, hi⟩ := ha
    refine ⟨i :: w, i, ?_⟩
    change P.reflectionPerm _ (d4Word w (P.reflectionPerm a a)) = _
    rw [d4Word_neg, hi, P.reflectionPerm_involutive]
  · intro a ha
    obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨a, ha⟩
    exact ⟨[], i, (congrArg Subtype.val hi).symm⟩
  · intro a b ha hb
    obtain ⟨w, i, hi⟩ := ha
    obtain ⟨j, hj⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨b, hb⟩
    have hj' : typeDSimpleRootIndex 2 j = b := congrArg Subtype.val hj
    refine ⟨w ++ [j], i, ?_⟩
    rw [d4Word_append]
    change d4Word w (P.reflectionPerm _ (P.reflectionPerm b a)) = _
    rw [hj', P.reflectionPerm_involutive, hi]

theorem d4_pairing_symm (a b : TypeDRootIndex 4) :
    (typeDRootPairing 2).pairing a b = (typeDRootPairing 2).pairing b a := by
  rw [typeDRootPairing_pairing, typeDRootPairing_pairing, dot_comm]

theorem d4_pairingIn_symm (a b : TypeDRootIndex 4) :
    (typeDRootPairing 2).pairingIn ℤ a b = (typeDRootPairing 2).pairingIn ℤ b a := by
  have h := d4_pairing_symm a b
  rw [← (typeDRootPairing 2).algebraMap_pairingIn ℤ,
    ← (typeDRootPairing 2).algebraMap_pairingIn ℤ] at h
  exact_mod_cast h

theorem d4_sum_pairing (a b c : TypeDRootIndex 4)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root a + (typeDRootPairing 2).root b) :
    (typeDRootPairing 2).pairing a b = -1 := by
  let P := typeDRootPairing 2
  have h₁ := RootPairing.pairing_eq_add_of_root_eq_add (l := a) hs
  have h₂ := RootPairing.pairing_eq_add_of_root_eq_add (l := b) hs
  have h₃ := RootPairing.pairing_eq_add_of_root_eq_add (l := c) hs
  rw [(typeDRootPairing 2).pairing_same] at h₁ h₂ h₃
  rw [d4_pairing_symm b a] at h₁
  rw [d4_pairing_symm a c, d4_pairing_symm b c] at h₃
  linarith

theorem d4_pairing_lower (a b : TypeDRootIndex 4) (hab : a ≠ b)
    (hop : b ≠ (typeDRootPairing 2).reflectionPerm a a) :
    -1 ≤ (typeDRootPairing 2).pairingIn ℤ a b := by
  let P := typeDRootPairing 2
  have hn : P.root a ≠ -P.root b := by
    intro h
    apply hop
    apply P.root.injective
    rw [P.root_reflectionPerm, P.reflection_apply_self, h, neg_neg]
  have h := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' a b
    (P.root.injective.ne hab) hn
  dsimp only [P] at h
  rw [d4_pairingIn_symm b a] at h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  dsimp only [P] at *
  omega

theorem d4_height_reflection (i : Fin 4) (a : TypeDRootIndex 4) :
    (typeDRootPairing_base 2).height
        ((typeDRootPairing 2).reflectionPerm (typeDSimpleRootIndex 2 i) a) =
      (typeDRootPairing_base 2).height a -
        (typeDRootPairing 2).pairingIn ℤ a (typeDSimpleRootIndex 2 i) := by
  have hs := (typeDRootPairing 2).reflection_apply_root' ℤ
    (i := typeDSimpleRootIndex 2 i) (j := a)
  rw [← (typeDRootPairing 2).root_reflectionPerm, sub_eq_add_neg, ← neg_smul] at hs
  have hi : typeDSimpleRootIndex 2 i ∈ (typeDRootPairing_base 2).support := by
    exact (typeDRootPairing_baseEquiv 2 i).property
  rw [(typeDRootPairing_base 2).height_add_zsmul hs,
    RootPairing.Base.height_one_of_mem_support hi]
  simp [sub_eq_add_neg]

theorem d4_positive_of_dominant_pair (a b : TypeDRootIndex 4) (hab : a ≠ b)
    (hop : b ≠ (typeDRootPairing 2).reflectionPerm a a)
    (hd : ∀ i : Fin 4,
      0 ≤ (typeDRootPairing 2).pairingIn ℤ a (typeDSimpleRootIndex 2 i) +
        (typeDRootPairing 2).pairingIn ℤ b (typeDSimpleRootIndex 2 i)) :
    (typeDRootPairing_base 2).IsPos a := by
  let P := typeDRootPairing 2
  let B := typeDRootPairing_base 2
  obtain ⟨f, _, hf, he⟩ := B.exists_root_eq_sum_int a
  rcases hf with hf | hf
  · change 0 < B.height a
    rw [B.height_eq_sum he]
    have hne := B.height_ne_zero a
    rw [B.height_eq_sum he] at hne
    exact lt_of_le_of_ne (Finset.sum_nonneg fun j _ => hf.le j) (Ne.symm hne)
  · let l := P.coroot' a + P.coroot' b
    have hval : l (P.root a) = 2 + P.pairing a b := by
      simp only [l, LinearMap.add_apply, P.root_coroot'_eq_pairing, P.pairing_same]
    have hnonneg (j) (hj : j ∈ B.support) : 0 ≤ l (P.root j) := by
      obtain ⟨i, hi⟩ := (typeDRootPairing_baseEquiv 2).surjective ⟨j, hj⟩
      have hi' : typeDSimpleRootIndex 2 i = j := congrArg Subtype.val hi
      have h := hd i
      rw [hi', d4_pairingIn_symm a j, d4_pairingIn_symm b j] at h
      change 0 ≤ P.pairing j a + P.pairing j b
      rw [← P.algebraMap_pairingIn ℤ, ← P.algebraMap_pairingIn ℤ]
      change (0 : ℝ) ≤ (P.pairingIn ℤ j a : ℝ) + (P.pairingIn ℤ j b : ℝ)
      rw [← Int.cast_add]
      exact Int.cast_nonneg h
    have hn : l (P.root a) ≤ 0 := by
      rw [he, map_sum]
      apply Finset.sum_nonpos
      intro j hj
      rw [map_zsmul, zsmul_eq_mul]
      exact mul_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hf.le j) (hnonneg j hj)
    have hp := d4_pairing_lower a b hab hop
    have hp' : (-1 : ℝ) ≤ P.pairing a b := by
      rw [← P.algebraMap_pairingIn ℤ]
      dsimp only [P]
      change (-1 : ℝ) ≤ ((typeDRootPairing 2).pairingIn ℤ a b : ℝ)
      simpa only [Int.cast_neg, Int.cast_one] using
        (Int.cast_le (R := ℝ)).mpr hp
    rw [hval] at hn
    linarith

theorem d4_pair_positive_word (a b : TypeDRootIndex 4) (hab : a ≠ b)
    (hop : b ≠ (typeDRootPairing 2).reflectionPerm a a) :
    ∃ w : List (Fin 4), (typeDRootPairing_base 2).IsPos (d4Word w a) ∧
      (typeDRootPairing_base 2).IsPos (d4Word w b) := by
  classical
  let P := typeDRootPairing 2
  let B := typeDRootPairing_base 2
  let orbit : Set (TypeDRootIndex 4 × TypeDRootIndex 4) :=
    Set.range fun w : List (Fin 4) => (d4Word w a, d4Word w b)
  obtain ⟨p, ⟨w, rfl⟩, hm⟩ := Set.exists_max_image orbit
    (fun p => B.height p.1 + B.height p.2) (Set.toFinite _) ⟨(a, b), [], rfl⟩
  have hd (i : Fin 4) :
      0 ≤ P.pairingIn ℤ (d4Word w a) (typeDSimpleRootIndex 2 i) +
        P.pairingIn ℤ (d4Word w b) (typeDSimpleRootIndex 2 i) := by
    have h := hm _ ⟨i :: w, rfl⟩
    change B.height (P.reflectionPerm _ (d4Word w a)) +
      B.height (P.reflectionPerm _ (d4Word w b)) ≤ B.height (d4Word w a) +
        B.height (d4Word w b) at h
    rw [d4_height_reflection, d4_height_reflection] at h
    dsimp only [P, B] at *
    omega
  have hne := (d4Word w).injective.ne hab
  have hnot : d4Word w b ≠ P.reflectionPerm (d4Word w a) (d4Word w a) := by
    rw [← d4Word_neg]
    exact (d4Word w).injective.ne hop
  refine ⟨w, d4_positive_of_dominant_pair _ _ hne hnot hd, ?_⟩
  apply d4_positive_of_dominant_pair _ _ hne.symm
  · intro h
    apply hnot
    have he : P.root (d4Word w a) = -P.root (d4Word w b) :=
      P.root_eq_neg_iff.mpr h
    apply P.root.injective
    rw [P.root_reflectionPerm, P.reflection_apply_self, he, neg_neg]
  · intro i
    rw [add_comm]
    exact hd i

theorem d4_sum_ne (a b c : TypeDRootIndex 4)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root a + (typeDRootPairing 2).root b) : a ≠ b := by
  intro h
  have hp := d4_sum_pairing a b c hs
  rw [h, (typeDRootPairing 2).pairing_same] at hp
  norm_num at hp

theorem d4_sum_nonopposite (a b c : TypeDRootIndex 4)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root a + (typeDRootPairing 2).root b) :
    b ≠ (typeDRootPairing 2).reflectionPerm a a := by
  intro h
  rw [h, (typeDRootPairing 2).root_reflectionPerm,
    (typeDRootPairing 2).reflection_apply_self, add_neg_cancel] at hs
  exact (typeDRootPairing 2).ne_zero c hs

theorem d4_sum_reflection (a b c : TypeDRootIndex 4)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root a + (typeDRootPairing 2).root b) :
    (typeDRootPairing 2).reflectionPerm a b = c := by
  apply (typeDRootPairing 2).root.injective
  rw [(typeDRootPairing 2).root_reflectionPerm, (typeDRootPairing 2).reflection_apply_root,
    d4_pairing_symm b a, d4_sum_pairing a b c hs, neg_one_smul, sub_neg_eq_add,
    add_comm ((typeDRootPairing 2).root b), ← hs]

theorem d4_sum_no_difference (a b c : TypeDRootIndex 4)
    (hs : (typeDRootPairing 2).root c =
      (typeDRootPairing 2).root a + (typeDRootPairing 2).root b) :
    ¬ ∃ d, (typeDRootPairing 2).root d =
      (typeDRootPairing 2).root ((typeDRootPairing 2).reflectionPerm a a) +
        (typeDRootPairing 2).root b := by
  rintro ⟨d, hd⟩
  have hp := d4_sum_pairing _ _ _ hd
  rw [(typeDRootPairing 2).pairing_reflectionPerm_self_left,
    d4_sum_pairing a b c hs] at hp
  norm_num at hp


end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension.RootPairGeometry
