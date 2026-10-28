module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted.Source
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.Reflections.RankOne
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.Reflections.LinearThree
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.Reflections.SymplecticFour
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Tori.Reflections.UnitaryThree
/-!
# Original cyclic escape in every marked binary model

The five concrete reflections apply to the same torus embeddings used for
orders and Borel placement. The original two-stage lift gives order 2^f−1
and escaping normalizers of all odd-primary subgroups. The unitary torus is
only the fixed-field torus; the symplectic case retains the derived carrier
and its genuine field-size bound.
Source: Aschbacher–Smith E.2.2 and E.6.27, pp.215–216,257.
-/

public section
open Subgroup

namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
open ChapterB
variable {X : Type*} [Group X] [Finite X]
private theorem odd_mersenne {f : ℕ} (hf : 0 < f) : Odd (2^f-1) :=
  Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega)) odd_one

theorem rank_one_cyclic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X)
    (hc : SingleClauses (minimalParabolicMax S hP) K S ∨
      ExchangedClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : ExchangedModel (minimalParabolicMax S hP) K f) :
    ∃ D : Subgroup X, D ≤ minimalParabolicMax S hP ∧ IsCyclic D ∧ Nat.card D=2^f-1 ∧
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ D → IsPGroup p A →
        ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  rcases hm with ⟨F,hfield,hfin,hchar,hf,hF,hB⟩|⟨m,hm,hf,hB⟩
  · let := hfield
    let := hfin
    let := hchar
    obtain ⟨w,hw,hinv⟩ := Tori.exists_psl2Torus_reflection (F := F)
    have hu : Nat.card Fˣ = 2^f-1 := by rw [Nat.card_units,hF]
    obtain ⟨D,hDM,hDc,hcard,hN⟩ := source_cyclic_normalizer_escape_of_torus S hP K hc _ hB
      (Tori.psl2Torus (F := F)) Tori.psl2Torus_injective (hu.symm ▸ odd_mersenne (by omega)) w hw hinv
    exact ⟨D,hDM,hDc,hcard.trans hu,hN⟩
  · obtain ⟨w,hw,hinv⟩ := Tori.exists_suzukiTorus_reflection m (by omega)
    have hu : Nat.card (GaloisField 2 (2*m+1))ˣ = 2^f-1 := by
      rw [Nat.card_units,GaloisField.card 2 (2*m+1) (by omega),hf]
    obtain ⟨D,hDM,hDc,hcard,hN⟩ := source_cyclic_normalizer_escape_of_torus S hP K hc _ hB
      (Tori.suzukiTorus m (by omega)) (Tori.suzukiTorus_injective m (by omega))
      (hu.symm ▸ odd_mersenne (by omega)) w hw hinv
    exact ⟨D,hDM,hDc,hcard.trans hu,hN⟩

theorem unitary_cyclic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : UnitaryModel (minimalParabolicMax S hP) K f) :
    ∃ D : Subgroup X, D ≤ minimalParabolicMax S hP ∧ IsCyclic D ∧ Nat.card D=2^f-1 ∧
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ D → IsPGroup p A →
        ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  obtain ⟨F,hfield,hfin,hchar,J,hJ,hf,hF,hconj,hfixed,hB⟩ := hm
  let := hfield
  let := hfin
  let := hchar
  obtain ⟨w,hw,hinv⟩ := Tori.exists_psu3Torus_reflection J hJ
  have hu : Nat.card (Tori.unitaryFixedField J)ˣ = 2^f-1 := by
    rw [Nat.card_units]
    exact congrArg (fun n : ℕ => n-1) hfixed
  obtain ⟨D,hDM,hDc,hcard,hN⟩ := source_cyclic_normalizer_escape_of_torus S hP K (.inl hc) _ hB
    (Tori.psu3Torus J hJ) (Tori.psu3Torus_injective J hJ)
    (hu.symm ▸ odd_mersenne (by omega)) w hw hinv
  exact ⟨D,hDM,hDc,hcard.trans hu,hN⟩

theorem bender_cyclic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hm : BenderModel (minimalParabolicMax S hP) K f) :
    ∃ D : Subgroup X, D ≤ minimalParabolicMax S hP ∧ IsCyclic D ∧ Nat.card D=2^f-1 ∧
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ D → IsPGroup p A →
        ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP :=
  hm.elim (rank_one_cyclic_escape S hP K (.inl hc)) (unitary_cyclic_escape S hP K hc)

theorem diagram_cyclic_escape (S : Sylow 2 X) (hP : IsMinimalParabolicOver S ⊤)
    (K : Subgroup X) (hc : SingleClauses (minimalParabolicMax S hP) K S) {f : ℕ}
    (hf : 1 < f) (hm : DiagramModel (minimalParabolicMax S hP) K S f) :
    ∃ D : Subgroup X, D ≤ minimalParabolicMax S hP ∧ IsCyclic D ∧ Nat.card D=2^f-1 ∧
      ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup X), Odd p → A ≤ D → IsPGroup p A →
        ¬ normalizer (A : Set X) ≤ minimalParabolicMax S hP := by
  rcases hm with ⟨F,hfield,hfin,hchar,_,hF,e,hB,_⟩|⟨F,hfield,hfin,hchar,_,hF,e,hB,_⟩
  · let := hfield
    let := hfin
    let := hchar
    obtain ⟨w,hw,hinv⟩ := Tori.exists_psl3Torus_reflection F
    have hu : Nat.card Fˣ = 2^f-1 := by rw [Nat.card_units,hF]
    obtain ⟨D,hDM,hDc,hcard,hN⟩ := source_cyclic_normalizer_escape_of_torus S hP K (.inl hc) _ ⟨e,hB⟩
      (Tori.psl3Torus F) (Tori.psl3Torus_injective F) (hu.symm ▸ odd_mersenne (by omega)) w hw hinv
    exact ⟨D,hDM,hDc,hcard.trans hu,hN⟩
  · let := hfield
    let := hfin
    let := hchar
    have hlarge : 2 < Nat.card F := by
      rw [hF]
      simpa only [pow_one] using Nat.pow_lt_pow_right (by decide : 1<2) hf
    obtain ⟨w,hw,hinv⟩ := Tori.exists_sp4DerivedTorus_reflection hlarge
    have hu : Nat.card Fˣ = 2^f-1 := by rw [Nat.card_units,hF]
    obtain ⟨D,hDM,hDc,hcard,hN⟩ := source_cyclic_normalizer_escape_of_torus S hP K (.inl hc) _ ⟨e,hB⟩
      (Tori.sp4DerivedTorus (F := F)) Tori.sp4DerivedTorus_injective
      (hu.symm ▸ odd_mersenne (by omega)) w hw hinv
    exact ⟨D,hDM,hDc,hcard.trans hu,hN⟩
end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Inverted
