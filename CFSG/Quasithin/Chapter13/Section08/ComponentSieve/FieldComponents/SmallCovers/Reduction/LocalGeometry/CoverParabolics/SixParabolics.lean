module

public import Theory.SpecificGroups.SymmetricSix.Parabolics

/-!
# Marked parabolics from the genuine six-letter subgroup lattice

The checked A₆ and S₆ subgroup tables identify the two maximal overgroups
of each Sylow two-subgroup. Their orders are respectively three times the
Sylow order. Consequently a proper Sylow overgroup containing a subgroup
of three-divisible order must be one of these ordinary maximal parabolics.
It equals the join of that subgroup and the Sylow subgroup.

The final two lemmas lift maximality and this equality through a genuine
surjective quotient map. The kernel must lie in the marked join; this is a
separate source obligation, as is the three-divisibility of the image.
These lemmas do not choose a quotient coordinate map or infer a diagram
action from an abstract group-family label.

Source: Aschbacher--Smith, 13.8.21(2), printed p.956 (PDF p.973),
using the six-letter parabolic geometry of Appendix I.5.
-/

public section

open Subgroup
open Theory.SpecificGroups.SymmetricSix

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics

private theorem isCoatom_of_order (X : Type*) [Group X] [Finite X]
    (S J : Subgroup X) (n : ℕ) (hS : Nat.card S = n) (hc : Nat.Coprime 3 n)
    (hSJ : S ≤ J) (hJ : J ≠ ⊤) (hthree : 3 ∣ Nat.card J)
    (hmax : ∀ P : Subgroup X, IsCoatom P → S ≤ P → Nat.card P = 3 * n) :
    IsCoatom J := by
  obtain ⟨P, hP, hJP⟩ := (eq_top_or_exists_le_coatom J).resolve_left hJ
  have hd : n ∣ Nat.card J := hS ▸ card_dvd_of_le hSJ
  have hcardP := hmax P hP (hSJ.trans hJP)
  have he : J = P := eq_of_le_of_card_ge hJP (by
    rw [hcardP]
    exact Nat.le_of_dvd Nat.card_pos (hc.mul_dvd_of_dvd_of_dvd hthree hd))
  exact he.symm ▸ hP

/-- A proper A₆ Sylow overgroup with three-divisible order is an ordinary maximal subgroup. -/
theorem six_isCoatom_of_sylow_three (S : Sylow 2 A6) (J : Subgroup A6)
    (hSJ : (S : Subgroup A6) ≤ J) (hJ : J ≠ ⊤) (hthree : 3 ∣ Nat.card J) :
    IsCoatom J := by
  obtain ⟨g, hg, hall⟩ := a6_coatoms_over_sylow S
  have hS : Nat.card S = 8 := by
    rw [← hg]
    exact (card_map_of_injective (MulAut.conj g).injective).trans a6Borel_order
  apply isCoatom_of_order A6 S J 8 hS (by decide) hSJ hJ hthree
  intro P hP hSP
  rcases (hall P).mp ⟨hP, hSP⟩ with rfl | rfl
  · exact (card_map_of_injective (MulAut.conj g).injective).trans a6DuadStabilizer_order
  · exact (card_map_of_injective (MulAut.conj g).injective).trans a6SynthemeStabilizer_order

/-- The corresponding ordinary maximality assertion in the actual S₆. -/
theorem symmetricSix_isCoatom_of_sylow_three (S : Sylow 2 S6) (J : Subgroup S6)
    (hSJ : (S : Subgroup S6) ≤ J) (hJ : J ≠ ⊤) (hthree : 3 ∣ Nat.card J) :
    IsCoatom J := by
  obtain ⟨g, hg, hall⟩ := coatoms_over_sylow S
  have hS : Nat.card S = 16 := by
    rw [← hg]
    exact (card_map_of_injective (MulAut.conj g).injective).trans borel_order
  apply isCoatom_of_order S6 S J 16 hS (by decide) hSJ hJ hthree
  intro P hP hSP
  rcases (hall P).mp ⟨hP, hSP⟩ with rfl | rfl
  · exact (card_map_of_injective (MulAut.conj g).injective).trans duadStabilizer_order
  · exact (card_map_of_injective (MulAut.conj g).injective).trans synthemeStabilizer_order

/-- Identify the actual conjugate duad or syntheme parabolic and its marked generating join. -/
theorem six_marked_parabolic (S : Sylow 2 A6) (J A : Subgroup A6)
    (hSJ : (S : Subgroup A6) ≤ J) (hAJ : A ≤ J) (hJ : J ≠ ⊤)
    (hthree : 3 ∣ Nat.card A) :
    IsCoatom J ∧ J = A ⊔ S ∧ ∃ g : A6,
      (MulAut.conj g).mapSubgroup a6Borel = (S : Subgroup A6) ∧
      (J = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∨
        J = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer) := by
  have hmax := six_isCoatom_of_sylow_three S J hSJ hJ (hthree.trans (card_dvd_of_le hAJ))
  have hle : A ⊔ (S : Subgroup A6) ≤ J := sup_le hAJ hSJ
  have hjoin := six_isCoatom_of_sylow_three S (A ⊔ S) le_sup_right
    (fun he => hJ (top_unique (he ▸ hle)))
    (hthree.trans (card_dvd_of_le le_sup_left))
  have he : J = A ⊔ S := by
    rcases eq_or_lt_of_le hle with he | hl
    · exact he.symm
    · exact (hJ (hjoin.2 J hl)).elim
  obtain ⟨g, hg, hall⟩ := a6_coatoms_over_sylow S
  exact ⟨hmax, he, g, hg, (hall J).mp ⟨hmax, hSJ⟩⟩

/-- Identify the genuine S₆ parabolic, with a conjugator also marking the Sylow subgroup. -/
theorem symmetricSix_marked_parabolic (S : Sylow 2 S6) (J A : Subgroup S6)
    (hSJ : (S : Subgroup S6) ≤ J) (hAJ : A ≤ J) (hJ : J ≠ ⊤)
    (hthree : 3 ∣ Nat.card A) :
    IsCoatom J ∧ J = A ⊔ S ∧ ∃ g : S6,
      (MulAut.conj g).mapSubgroup borel = (S : Subgroup S6) ∧
      (J = (MulAut.conj g).mapSubgroup duadStabilizer ∨
        J = (MulAut.conj g).mapSubgroup synthemeStabilizer) := by
  have hmax := symmetricSix_isCoatom_of_sylow_three S J hSJ hJ
    (hthree.trans (card_dvd_of_le hAJ))
  have hle : A ⊔ (S : Subgroup S6) ≤ J := sup_le hAJ hSJ
  have hjoin := symmetricSix_isCoatom_of_sylow_three S (A ⊔ S) le_sup_right
    (fun he => hJ (top_unique (he ▸ hle)))
    (hthree.trans (card_dvd_of_le le_sup_left))
  have he : J = A ⊔ S := by
    rcases eq_or_lt_of_le hle with he | hl
    · exact he.symm
    · exact (hJ (hjoin.2 J hl)).elim
  obtain ⟨g, hg, hall⟩ := coatoms_over_sylow S
  exact ⟨hmax, he, g, hg, (hall J).mp ⟨hmax, hSJ⟩⟩

private theorem lift_marked_maximal {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Surjective f) (J P : Subgroup X)
    (hPJ : P ≤ J) (hk : f.ker ≤ P)
    (hmax : IsCoatom (J.map f)) (he : J.map f = P.map f) :
    IsCoatom J ∧ J = P := by
  have hJ := comap_map_eq_self (hk.trans hPJ)
  have hP := comap_map_eq_self hk
  refine ⟨hJ ▸ isCoatom_comap_of_surjective hf hmax, ?_⟩
  have h := congrArg (comap f) he
  rwa [hJ, hP] at h

/-- Pull back A₆ parabolic maximality and the marked join through the actual quotient map. -/
theorem six_lifted_marked_maximal {X : Type*} [Group X] [Finite X]
    (f : X →* A6) (hf : Function.Surjective f) (S : Sylow 2 X) (J A : Subgroup X)
    (hSJ : (S : Subgroup X) ≤ J) (hAJ : A ≤ J) (hJ : J ≠ ⊤)
    (hk : f.ker ≤ A ⊔ S) (hthree : 3 ∣ Nat.card (A.map f)) :
    IsCoatom J ∧ J = A ⊔ S := by
  have hbase : A ⊔ (S : Subgroup X) ≤ J := sup_le hAJ hSJ
  have hproper : J.map f ≠ ⊤ := by
    intro he
    have h := congrArg (comap f) he
    rw [comap_map_eq_self (hk.trans hbase), comap_top] at h
    exact hJ h
  obtain ⟨hm, he, _⟩ := six_marked_parabolic (S.mapSurjective hf) (J.map f) (A.map f)
    (map_mono hSJ) (map_mono hAJ) hproper hthree
  apply lift_marked_maximal f hf J (A ⊔ S) hbase hk hm
  simpa only [Subgroup.map_sup, Sylow.coe_mapSurjective] using he

/-- Pull back S₆ parabolic maximality and the marked join, retaining the kernel containment. -/
theorem symmetricSix_lifted_marked_maximal {X : Type*} [Group X] [Finite X]
    (f : X →* S6) (hf : Function.Surjective f) (S : Sylow 2 X) (J A : Subgroup X)
    (hSJ : (S : Subgroup X) ≤ J) (hAJ : A ≤ J) (hJ : J ≠ ⊤)
    (hk : f.ker ≤ A ⊔ S) (hthree : 3 ∣ Nat.card (A.map f)) :
    IsCoatom J ∧ J = A ⊔ S := by
  have hbase : A ⊔ (S : Subgroup X) ≤ J := sup_le hAJ hSJ
  have hproper : J.map f ≠ ⊤ := by
    intro he
    have h := congrArg (comap f) he
    rw [comap_map_eq_self (hk.trans hbase), comap_top] at h
    exact hJ h
  obtain ⟨hm, he, _⟩ := symmetricSix_marked_parabolic (S.mapSurjective hf) (J.map f)
    (A.map f) (map_mono hSJ) (map_mono hAJ) hproper hthree
  apply lift_marked_maximal f hf J (A ⊔ S) hbase hk hm
  simpa only [Subgroup.map_sup, Sylow.coe_mapSurjective] using he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
