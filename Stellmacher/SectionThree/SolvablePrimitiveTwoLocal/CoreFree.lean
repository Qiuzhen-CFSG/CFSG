module

public import Stellmacher.SectionsOneToFourDefs

/-!
# The core-free primitive step

This module proves the core-free part of the solvable primitive-group argument
used in Stellmacher (3.3), Journal of Algebra 190 (1997), pp. 21--22.  In a
finite solvable group with a unique maximal subgroup `B` above a Sylow
2-subgroup `T`, core-freeness of `B` supplies a minimal normal elementary
abelian subgroup `K`.  It cannot lie in `B`; maximality then gives `K ⋁ T = Q`,
and the trivial core gives `K ∩ B = 1`.  Minimal normality also gives the
required irreducibility under conjugation by `T`.
-/

namespace Stellmacher.SectionThree

open scoped Pointwise IsMulCommutative

universe u

public theorem coreFree_uniqueSylowMaximal
    {Q : Type u} [Group Q] [Finite Q]
    (T B : Subgroup Q) (Tₛ : Sylow 2 Q)
    (hT : (Tₛ : Subgroup Q) = T)
    (hB : IsCoatom B) (hTB : T ≤ B)
    (huniq : ∀ M : Subgroup Q, IsCoatom M → T ≤ M → M = B)
    (hcore : B.normalCore = ⊥) (hsolv : Group.IsSolvable Q) :
    ∃ (p : ℕ) (K : Subgroup Q),
      p.Prime ∧ Odd p ∧ K.Normal ∧ IsElementaryAbelian p K ∧
      K ⊓ B = ⊥ ∧ K ⊔ T = ⊤ ∧
      (∀ A : Subgroup Q, A ≤ K →
        (∀ t : T, ∀ a : Q, a ∈ A →
          (t : Q) * a * (t : Q)⁻¹ ∈ A) →
        A = ⊥ ∨ A = K) := by
  classical
  let _ : Group.IsSolvable Q := hsolv
  have hQ_ne_bot : (⊤ : Subgroup Q) ≠ ⊥ := by
    intro htopbot
    apply hB.ne_top
    apply le_antisymm le_top
    simp [htopbot]
  obtain ⟨K, hKnormal, _hKtop, hKne, hKmin⟩ :=
    exists_minimal_normal_le (G := Q) ⊤ inferInstance hQ_ne_bot
  let _ : K.Normal := hKnormal
  let _ : IsMinimalNormal K :=
    { minimal := by
        intro A hAnormal hAK
        by_cases hAbot : A = ⊥
        · exact Or.inl hAbot
        · exact Or.inr (hKmin A hAnormal hAK hAbot) }
  obtain ⟨p, hp, hKelem⟩ :=
    minimalNormal_solvable_exists_isElementaryAbelian K
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : IsElementaryAbelian p K := hKelem
  have hKnotB : ¬ K ≤ B := by
    intro hKB
    have hKcore : K ≤ B.normalCore :=
      Subgroup.normal_le_normalCore.mpr hKB
    have hKbot : K ≤ (⊥ : Subgroup Q) := by simpa [hcore] using hKcore
    exact hKne (le_bot_iff.mp hKbot)
  have hp_ne_two : p ≠ 2 := by
    intro hp2
    have hKtwo : IsPGroup 2 K := by simpa [hp2] using IsElementaryAbelian.isPGroup p K
    have hKT : K ≤ T := by
      rw [← hT]
      exact IsPGroup.le_sylow_of_normal hKtwo Tₛ
    exact hKnotB (hKT.trans hTB)
  have hKBtop : K ⊔ B = ⊤ := by
    rcases (hB.le_iff).mp le_sup_right with htop | hEq
    · exact htop
    · exact False.elim (hKnotB (by rw [← hEq]; exact le_sup_left))
  have hKinfBnormal : (K ⊓ B).Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hKBtop]
    apply sup_le
    · rw [Subgroup.le_normalizer_iff]
      intro k hk x hx
      have hcomm : k * x = x * k := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := K)).comm
            (⟨k, hk⟩ : K) ⟨x, hx.1⟩)
      simpa [hcomm] using hx
    · rw [Subgroup.le_normalizer_iff]
      intro b hb x hx
      exact ⟨hKnormal.conj_mem x hx.1 b,
        B.mul_mem (B.mul_mem hb hx.2) (B.inv_mem hb)⟩
  have hKinfB : K ⊓ B = ⊥ := by
    have hlecore : K ⊓ B ≤ B.normalCore :=
      @Subgroup.normal_le_normalCore Q _ B (K ⊓ B) hKinfBnormal |>.mpr inf_le_right
    apply le_antisymm
    · simpa [hcore] using hlecore
    · exact bot_le
  have hKTtop : K ⊔ T = ⊤ := by
    rcases eq_top_or_exists_le_coatom (K ⊔ T) with htop | ⟨M, hM, hleM⟩
    · exact htop
    · have hMT : T ≤ M := le_sup_right.trans hleM
      have hMB : M = B := huniq M hM hMT
      exact False.elim (hKnotB (le_sup_left.trans (hMB ▸ hleM)))
  refine ⟨p, K, hp, hp.odd_of_ne_two hp_ne_two, hKnormal, hKelem,
    hKinfB, hKTtop, ?_⟩
  intro A hAK hAinv
  have hAnormal : A.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hKTtop]
    apply sup_le
    · rw [Subgroup.le_normalizer_iff]
      intro k hk a ha
      have hcomm : k * a = a * k := by
        exact congrArg Subtype.val
          ((IsMulCommutative.is_comm (M := K)).comm
            (⟨k, hk⟩ : K) ⟨a, hAK ha⟩)
      simpa [hcomm] using ha
    · rw [Subgroup.le_normalizer_iff]
      intro t ht a ha
      exact hAinv ⟨t, ht⟩ a ha
  by_cases hAbot : A = ⊥
  · exact Or.inl hAbot
  · exact Or.inr (hKmin A hAnormal hAK hAbot)

end Stellmacher.SectionThree
