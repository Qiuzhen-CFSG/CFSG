module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Theory.Comparator.Defs
public import Stellmacher.Recognition.FinalTheorem
public import Stellmacher.Recognition.MinimalSimpleFinalTheorem
public import Stellmacher.Recognition.PSL3ThreeModel
public import Stellmacher.Recognition.PSU3ThreeModel

open Matrix
open scoped MatrixGroups

universe u

namespace CFSG

set_option warningAsError false in
/-- **Feit--Thompson odd-order theorem.** -/
public theorem odd_order_theorem (G : Type u) [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    : Group.IsSolvable G := by
  sorry

set_option warningAsError false in
/-- **The Bender-Suzuki theorem.** -/
public theorem bender_suzuki {X : Type u} [Group X] [Finite X] [IsSimpleGroup X]
    (M : Subgroup X) (hM : IsStronglyEmbedded M)
    : IsSimpleBenderGroup X := by
  sorry

set_option warningAsError false in
/-- **Gorenstein--Walter theorem.** -/
public theorem gorenstein_walter (G : Type) [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (P : Sylow 2 G)
    (_hdih : ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n))
    : Nonempty (G ≃* alternatingGroup (Fin 7))
      ∨ ∃ p k : ℕ,
        ∃ _hp : Fact p.Prime,
          Odd p ∧ 5 ≤ p ^ k ∧ Nonempty (G ≃* PSL(2, GaloisField p k)) := by
  sorry

/-- `PSU₃(3)`, independently specified as the projective image of determinant-one
isometries over `GF(9)`, with identity Gram matrix and conjugation `x ↦ x³`. -/
@[expose] public noncomputable def PSU3ThreeModel :
    Subgroup (ProjGenLinGroup (Fin 3) (GaloisField 3 2)) :=
  (Subgroup.closure
    {A : GL (Fin 3) (GaloisField 3 2) |
      (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) j i ^ 3)
          * (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) = 1
        ∧ GeneralLinearGroup.det A = 1}).map ProjGenLinGroup.mk

private theorem psu3ThreeModel_eq : PSU3ThreeModel = ABG.PSU3 3 1 (by decide) := by
  have hset :
      {A : GL (Fin 3) (GaloisField 3 2) |
        (Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) j i ^ 3)
            * (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) = 1
          ∧ GeneralLinearGroup.det A = 1} =
      ((ABG.unitaryForm 3 3 1 (by decide)).specialSubgroup : Set _) := by
    ext A
    change (_ ∧ _) ↔
      ((Matrix.of fun i j => (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) j i ^ 3)
          * 1 * (A : Matrix (Fin 3) (Fin 3) (GaloisField 3 2)) = 1 ∧ _)
    rw [mul_one]
    rfl
  unfold PSU3ThreeModel
  rw [hset, Subgroup.closure_eq]

/-- **Thompson's classification of minimal finite simple groups**, in both
directions. The hypotheses and all five model families are explicit.

Source: Thompson, *Nonsolvable finite groups all of whose local subgroups are
solvable*, I (1968), Corollary 1, p. 388. -/
public theorem minimal_simple_classification (G : Type u) [Group G] [Finite G] :
    (IsSimpleGroup G ∧ ¬ Group.IsSolvable G ∧
      ∀ H : Subgroup G, H < ⊤ → Group.IsSolvable H) ↔
    (∃ p : ℕ, p.Prime ∧ Nonempty (G ≃* PSL(2, GaloisField 2 p))) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ Nonempty (G ≃* PSL(2, GaloisField 3 p))) ∨
    (∃ p : ℕ, ∃ _hp : Fact p.Prime, 3 < p ∧ (p % 5 = 2 ∨ p % 5 = 3) ∧
      Nonempty (G ≃* PSL(2, ZMod p))) ∨
    (∃ n : ℕ, (2 * n + 1).Prime ∧ Nonempty (G ≃* SzModel n)) ∨
    Nonempty (G ≃* PSL(3, ZMod 3)) := by
  constructor
  · rintro ⟨hs, hns, hproper⟩
    rcases Stellmacher.Recognition.isMinimalSimple_iff_thompsonModel.mp
        ⟨hs, hns, hproper⟩ with
      ⟨p, hp, e⟩ | ⟨p, hp, hodd, e⟩ | ⟨p, hp, hgt, hmod, e⟩ |
      ⟨n, hp, e⟩ | ⟨e⟩
    · exact .inl ⟨p, hp, ⟨e⟩⟩
    · exact .inr (.inl ⟨p, hp, hodd, ⟨e⟩⟩)
    · exact .inr (.inr (.inl ⟨p, ⟨hp⟩, hgt, hmod, ⟨e⟩⟩))
    · exact .inr (.inr (.inr (.inl ⟨n, hp, ⟨e⟩⟩)))
    · exact .inr (.inr (.inr (.inr ⟨e⟩)))
  · intro h
    suffices hG : IsMinimalSimple G from
      ⟨hG.isSimpleGroup, hG.not_isSolvable, hG.solvable_of_lt⟩
    apply Stellmacher.Recognition.isMinimalSimple_iff_thompsonModel.mpr
    rcases h with ⟨p, hp, ⟨e⟩⟩ | ⟨p, hp, hodd, ⟨e⟩⟩ |
      ⟨p, hp, hgt, hmod, ⟨e⟩⟩ | ⟨n, hp, ⟨e⟩⟩ | ⟨e⟩
    · exact .psl2Binary p hp e
    · exact .psl2ThreePower p hp hodd e
    · exact .psl2Prime p hp.out hgt hmod e
    · exact .suzuki n hp e
    · exact .psl3Three e.some

/-- **The classification of finite nonsolvable simple N₂ groups.** The N₂
hypothesis says explicitly that normalizers of nontrivial 2-subgroups are
solvable. Each alternative supplies an isomorphism with an actual group.

Sources: Kurzweil–Stellmacher, Appendix p. 370; Thompson VI (1974), p. 573
for the Tits correction. `Tits.ParrottGroup` is the ten-generator,
37-relator presentation from Parrott (1972), p. 683; `Sporadic.Mathieu.M11`
is the automorphism group of the explicit Witt `S(4,5,11)` design. -/
public theorem nTwo_classification (G : Type u) [Group G] [Finite G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G)
    (hlocal : ∀ Q : Subgroup G, Q ≠ ⊥ → IsPGroup 2 Q →
      Group.IsSolvable (Subgroup.normalizer (Q : Set G))) :
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSL(2, GaloisField 2 n))) ∨
    (∃ (K : Type u) (_ : Field K) (_ : Finite K),
      Odd (Nat.card K) ∧ 3 < Nat.card K ∧ Nonempty (G ≃* PSL(2, K))) ∨
    (∃ n : ℕ, 1 ≤ n ∧ Nonempty (G ≃* SzModel n)) ∨
    Nonempty (G ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (G ≃* Sporadic.Mathieu.M11) ∨
    Nonempty (G ≃* PSL(3, ZMod 3)) ∨
    Nonempty (G ≃* PSU3ThreeModel) ∨
    Nonempty (G ≃* Tits.ParrottGroup) ∨
    (∃ n : ℕ, 2 ≤ n ∧ Nonempty (G ≃* PSU3Model n)) := by
  have hN : Stellmacher.IsNTwoGroup G := by
    rintro U ⟨Q, hQ, htwo, rfl⟩
    exact hlocal Q hQ htwo
  rcases Stellmacher.nTwo_classification hns hN with hmodel | hunitary
  · cases hmodel with
    | psl2Even n hn e => exact .inl ⟨n, hn, ⟨e⟩⟩
    | psl2Odd K hodd hcard e =>
      exact .inr (.inl ⟨K, inferInstance, inferInstance, hodd, hcard, ⟨e⟩⟩)
    | suzuki n hn e => exact .inr (.inr (.inl ⟨n, hn, ⟨e⟩⟩))
    | alternatingSeven e => exact .inr (.inr (.inr (.inl ⟨e⟩)))
    | mathieuEleven e => exact .inr (.inr (.inr (.inr (.inl ⟨e⟩))))
    | linearThree h =>
      exact .inr (.inr (.inr (.inr (.inr (.inl
        (ABG.isPSL3_three_iff_nonempty_mulEquiv.mp h))))))
    | unitaryThree h =>
      have he : Nonempty (G ≃* PSU3ThreeModel) := by
        rw [psu3ThreeModel_eq]
        exact ABG.isPSU3_three_iff_nonempty_mulEquiv.mp h
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inl he))))))
    | tits e => exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e⟩)))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr hunitary)))))))

end CFSG
