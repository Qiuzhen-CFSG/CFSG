module

public import CFSG.Quasithin.ChapterG.Section08.Basic
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The complementary actions in Thompson's dihedral induction

The G.8.2 complement theorem and the proved nilpotent A × B lemma first give
the relative fixed-group complement of G.8.5. Applying this twice splits a
faithful actor of rank n+1 into actors of ranks n and one, each faithful on
an odd subgroup, with the two generated overgroups centralizing each other.

The G.8.2 input remains explicit. This is the induction geometry in
Aschbacher–Smith G.8.6 and the relative complement step of G.8.7, printed p.350.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section08
variable {G : Type*} [Group G]

theorem dihedral_elementary_le {A E : Subgroup G} [IsElementaryAbelian 2 A]
    (hEA : E ≤ A) : IsElementaryAbelian 2 E := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact le_centralizer_iff_isMulCommutative.mp
      (hEA.trans (A.le_centralizer.trans (centralizer_le hEA)))
  · exact (Monoid.exponent_dvd_of_monoidHom (inclusion hEA)
      (inclusion_injective hEA)).trans (IsElementaryAbelian.exponent_dvd_p 2 A)

theorem dihedral_nilpotent_le {X Y : Subgroup G} (hX : Group.IsNilpotent X)
    (hYX : Y ≤ X) : Group.IsNilpotent Y := by
  let _ := hX
  exact Subgroup.isNilpotent_of_ker_le_center (inclusion hYX) (by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr (inclusion_injective hYX)]
    exact bot_le)

theorem dihedral_normalizes_subgroup {A B : Subgroup G} [IsElementaryAbelian 2 A]
    (hBA : B ≤ A) : A ≤ normalizer (B : Set G) :=
  (A.le_centralizer.trans (centralizer_le hBA)).trans (centralizer_le_normalizer _)

theorem dihedral_fixed_normalizer (A X Y : Subgroup G)
    (hAX : A ≤ normalizer (X : Set G)) (hAY : A ≤ normalizer (Y : Set G)) :
    A ≤ normalizer (X ⊓ centralizer (Y : Set G) : Set G) :=
  (le_inf hAX (hAY.trans (normalizer_le_normalizer_centralizer Y))).trans
    inf_normalizer_le_normalizer_inf

variable [Finite G]

/-- The relative complement step of G.8.5, with its G.8.2 input explicit. -/
theorem relative_faithful_complement (hComplement : FaithfulComplementTheorem G)
    (A B X Y : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G)) (hBA : B ≤ A) (hYX : Y ≤ X)
    (hAY : A ≤ normalizer (Y : Set G)) (hBY : B ≤ centralizer (Y : Set G))
    (hfaith : B ⊓ centralizer (X : Set G) = ⊥) :
    ∃ D : Subgroup G, B ⊓ D = ⊥ ∧ B ⊔ D = A ∧
      B ⊓ centralizer (X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G) : Set G) = ⊥ := by
  let _ := hA
  let _ : IsElementaryAbelian 2 B := dihedral_elementary_le hBA
  let X' := X ⊓ centralizer (Y : Set G)
  have hfaith' : B ⊓ centralizer (X' : Set G) = ⊥ :=
    lemma_G_8_4 B X Y (IsElementaryAbelian.isPGroup 2 B) hX hodd hYX
      (hBA.trans hnorm) hBY hfaith
  obtain ⟨D, hD⟩ := hComplement A B X' hA (dihedral_nilpotent_le hX inf_le_left)
    (hodd.of_dvd_nat (card_dvd_of_le inf_le_left))
    (dihedral_fixed_normalizer A X Y hnorm hAY) hBA hfaith'
  refine ⟨D, hD.1, hD.2.1, ?_⟩
  have heq : X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G) = X' ⊓ centralizer (D : Set G) := by
    apply le_antisymm
    · exact le_inf
        (le_inf inf_le_left (inf_le_right.trans (centralizer_le (show Y ≤ D ⊔ Y from le_sup_right))))
        (inf_le_right.trans (centralizer_le (show D ≤ D ⊔ Y from le_sup_left)))
    · intro x hx
      refine ⟨hx.1.1, ?_⟩
      have hc : D ⊔ Y ≤ centralizer ({x} : Set G) := by
        apply sup_le
        · intro d hd
          exact mem_centralizer_singleton_iff.mpr (hx.2 d hd)
        · intro y hy
          exact mem_centralizer_singleton_iff.mpr (hx.1.2 y hy)
      intro z hz
      exact mem_centralizer_singleton_iff.mp (hc hz)
  change B ⊓ centralizer ((X ⊓ centralizer ((D ⊔ Y : Subgroup G) : Set G) : Subgroup G) : Set G) = ⊥
  rw [heq]
  exact hD.2.2.1

/-- The subgroup geometry for the dihedral induction. A rank-one actor C
and its complement B act faithfully on commuting odd subgroups. -/
theorem dihedral_induction_split (hComplement : FaithfulComplementTheorem G)
    (A X : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hX : Group.IsNilpotent X) (hodd : Odd (Nat.card X))
    (hnorm : A ≤ normalizer (X : Set G))
    (hfaith : A ⊓ centralizer (X : Set G) = ⊥)
    (n : ℕ) (hcard : Nat.card A = 2 ^ (n + 1)) :
    ∃ B C Y Z : Subgroup G,
      B ≤ A ∧ C ≤ A ∧ B ⊔ C = A ∧
      Nat.card B = 2 ^ n ∧ Nat.card C = 2 ∧
      Y ≤ X ∧ Z ≤ X ∧
      B ≤ normalizer (Y : Set G) ∧ C ≤ normalizer (Z : Set G) ∧
      B ⊓ centralizer (Y : Set G) = ⊥ ∧ C ⊓ centralizer (Z : Set G) = ⊥ ∧
      Y ⊔ B ≤ centralizer ((Z ⊔ C : Subgroup G) : Set G) := by
  let _ := hA
  obtain ⟨B₀, hB₀card⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2
    (show 2 ^ n ∣ Nat.card A by rw [hcard, pow_succ]; exact dvd_mul_right _ _)
  let B' := B₀.map A.subtype
  have hB'A : B' ≤ A := map_subtype_le _
  have hB'card : Nat.card B' = 2 ^ n := (card_map_of_injective A.subtype_injective).trans hB₀card
  have hB'faith : B' ⊓ centralizer (X : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hB'A).trans hfaith.le)
  obtain ⟨C, hCdis, hCsup, hCYfaith, hCker⟩ :=
    hComplement A B' X hA hX hodd hnorm hB'A hB'faith
  have hCA : C ≤ A := hCsup ▸ le_sup_right
  have hCcard : Nat.card C = 2 := by
    have hc := card_sup_eq_mul_of_normalizes_of_disjoint B' C
      (hCA.trans (dihedral_normalizes_subgroup hB'A)) (disjoint_iff.mpr hCdis)
    rw [hCsup, hcard, hB'card, pow_succ] at hc
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hc.symm
  let Y := X ⊓ centralizer (C : Set G)
  have hYX : Y ≤ X := inf_le_left
  have hAY : A ≤ normalizer (Y : Set G) :=
    dihedral_fixed_normalizer A X C hnorm (dihedral_normalizes_subgroup hCA)
  have hCfaith : C ⊓ centralizer (X : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hCA).trans hfaith.le)
  obtain ⟨B, hdis, hsup, hCZfaith⟩ :=
    relative_faithful_complement hComplement A C X Y hA hX hodd hnorm hCA hYX hAY
      (le_centralizer_iff.mpr inf_le_right) hCfaith
  have hBA : B ≤ A := hsup ▸ le_sup_right
  have hBcard : Nat.card B = 2 ^ n := by
    have hc := card_sup_eq_mul_of_normalizes_of_disjoint C B
      (hBA.trans (dihedral_normalizes_subgroup hCA)) (disjoint_iff.mpr hdis)
    rw [hsup, hcard, hCcard, pow_succ, mul_comm (2 ^ n)] at hc
    exact Nat.eq_of_mul_eq_mul_left (by decide) hc.symm
  let Z := X ⊓ centralizer ((B ⊔ Y : Subgroup G) : Set G)
  have hBYfaith : B ⊓ centralizer (Y : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    have hxC : x ∈ C := hCker.le ⟨hBA hx.1, hx.2⟩
    exact hdis.le ⟨hxC, hx.1⟩
  refine ⟨B, C, Y, Z, hBA, hCA, sup_comm C B ▸ hsup, hBcard, hCcard,
    hYX, inf_le_left, hBA.trans hAY, ?_, hBYfaith, hCZfaith, ?_⟩
  · exact hCA.trans (dihedral_fixed_normalizer A X (B ⊔ Y) hnorm
      ((le_inf (dihedral_normalizes_subgroup hBA) hAY).trans
        (normalizer_inf_normalizer_le_normalizer_sup B Y)))
  · apply le_centralizer_iff.mpr
    apply sup_le
    · exact (inf_le_right : Z ≤ centralizer ((B ⊔ Y : Subgroup G) : Set G)).trans (by rw [sup_comm B Y])
    · apply le_centralizer_iff.mpr
      apply sup_le
      · exact inf_le_right
      · exact hBA.trans (A.le_centralizer.trans (centralizer_le hCA))

end CFSG.Quasithin.ChapterG.Section08
