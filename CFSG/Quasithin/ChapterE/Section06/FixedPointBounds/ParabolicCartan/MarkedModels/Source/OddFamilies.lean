module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddTwo
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.Source.OddThreeDiagram
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels.Original
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import GorensteinWalter.A5
public import GorensteinWalter.LinearRingEquiv
public import Theory.GroupTheory.SmallIndexSolvable
public import GorensteinWalter.PSL2Cardinality
import all CFSG.Quasithin.ChapterB.Section06To07.Structure
/-!
# Complete odd-family dispatch for the original normal component

The actual Theorem C odd list has linear degree two, linear degree three,
or unitary degree three. The genuine model-source proofs construct every
odd geometric row. The field-three degree-two case is solvable and cannot
be the component; the five-, seven- and nine-element coincidences are
transported to their actual characteristic-two matrix models. No family
is discarded by a numerical label.

The final export applies the complete original component catalogue and
returns the proved odd marked rows or the remaining literal binary models.
It is independent of the disputed generation-parameter equality and does
not assert the still-separate binary Borel and diagram marking.
Source: Aschbacher–Smith E.2.2, printed pp.215–216.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
universe u
variable {H : Type u} [Group H] [Finite H]
private theorem component_not_three
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3)
    {K : Subgroup H} (hK : IsComponent H K) (e : K ≃* PSL(2,F)) : False := by
  let := hK.2
  have hc : Nat.card K = 12 := by
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨3,1,by decide,by decide,by decide,by simpa using hF⟩,hF]
    norm_num
  let P : Sylow 2 K := Classical.choice inferInstance
  have hcop : Nat.Coprime (P : Subgroup K).index (2 ^ 2) :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr P.not_dvd_index).symm.pow_right 2
  have hi : (P : Subgroup K).index ∣ 3 := hcop.dvd_of_dvd_mul_left
    (by simpa [hc] using (P : Subgroup K).index_dvd_card)
  let : Nontrivial K := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  exact Group.IsPerfect.not_isSolvable K ((P : Subgroup K).isSolvable_of_index_le_four
    ((Nat.le_of_dvd (by decide : 0 < 3) hi).trans (by decide)))

private theorem five_binary_model {D : Type*} [Group D]
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 5) (e : D ≃* PSL(2,F)) :
    ClassicalGroup.IsPSL D 2 4 := by
  let : Fintype F := Fintype.ofFinite F
  let eF : ZMod 5 ≃+* F := ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let eA := (e.trans (GorensteinWalter.psl2RingEquiv eF).symm).trans
    GorensteinWalter.alternatingGroupFive_equiv_PSL2.some.symm
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,hfour,
    ⟨eA.trans Atlas.Comparisons.Exceptional.psl2FourEquivAlt5.symm⟩⟩

/-- Dispatch every actual odd-family model, retaining the three binary coincidences. -/
theorem source_odd_families (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (hm : ChapterA.Section02.IsTheoremCOddModel
      (sourceImage (ChapterB.minimalParabolicMax T hP) K)) :
    SingleOddLinearModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) ∨
    SingleOddRankThreeModel (ChapterB.minimalParabolicMax T hP) K (T : Subgroup H) ∨
    ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 2 4 ∨
    ClassicalGroup.IsPSL (sourceImage (ChapterB.minimalParabolicMax T hP) K) 3 2 ∨
    Nonempty (sourceImage (ChapterB.minimalParabolicMax T hP) K ≃*
      commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  cases hm with
  | linear_three p hp ho he =>
    exact Or.inr (Or.inl (source_odd_linear_model T hP hs K hK hgen hp ho he))
  | unitary_three p hp ho he =>
    exact Or.inr (Or.inl (source_odd_unitary_model T hP hs K hK hgen hp ho he))
  | linear_two p d hp ho hd he =>
    obtain ⟨F,hF,hfin,hcard,⟨e⟩⟩ := he
    have hd0 : d ≠ 0 := by
      intro heq
      have hc : Nat.card F = 1 := by simpa [heq] using hcard
      exact zero_ne_one ((Nat.card_eq_one_iff_unique.mp hc).1.elim (0 : F) 1)
    have hp2 : p ≠ 2 := by intro h; subst p; norm_num at ho
    have hd12 : d=1 ∨ d=2 := by omega
    rcases hd12 with rfl|rfl
    · have hcard' : Nat.card F = p := by simpa using hcard
      by_cases h3 : p = 3
      · have hi := Structure.source_component_simple_image T hP hs K hK hgen
        exact (component_not_three (hcard'.trans h3) hi.2.1 e).elim
      by_cases h5 : p = 5
      · exact Or.inr (Or.inr (Or.inl (five_binary_model (hcard'.trans h5) e)))
      by_cases h7 : p = 7
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ZMod 2,inferInstance,inferInstance,by simp,
          ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two (hcard'.trans h7))⟩⟩)))
      have hlarge : 9 < p := by
        by_contra! hh
        interval_cases p <;> norm_num at *
      exact Or.inl (source_odd_prime_linear_model T hP hs K hK hgen hp ho hlarge
        ⟨F,hF,hfin,hcard',⟨e⟩⟩)
    · by_cases h3 : p = 3
      · have hc : Nat.card F = 9 := by simpa [h3] using hcard
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(e.trans
          (Atlas.Comparisons.Exceptional.psl2Card9EquivAlt6 hc)).trans
          Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm⟩)))
      have hlarge : 3 < p := by have hh := hp.two_le; omega
      exact Or.inl (source_odd_quadratic_linear_model T hP hs K hK hgen hp ho hlarge
        ⟨F,hF,hfin,hcard,⟨e⟩⟩)

/-- The normal component has a binary model or one of the completely marked odd rows. -/
theorem source_normal_geometric_cases {κ : GroupClass.{u}}
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H)
    (hP : ChapterB.IsMinimalParabolicOver T ⊤) (hs : ¬ Group.IsSolvable H)
    (K : Subgroup H) (hK : K.IsCComponent) [K.Normal]
    (hgen : K ⊔ (T : Subgroup H) = ⊤) :
    let M := ChapterB.minimalParabolicMax T hP
    let D := sourceImage M K
    SingleOddLinearModel M K (T : Subgroup H) ∨
    SingleOddRankThreeModel M K (T : Subgroup H) ∨
    ClassificationModels.IsBenderModel D ∨
    (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL D 3 (2^f)) ∨
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp D 2 (2^f)) ∨
    Nonempty (D ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) := by
  rcases Structure.source_component_classical_star_models hA hC hH T hP hs K hK hgen with
    ho | hb | hl | hsp | hbi
  · rcases source_odd_families T hP hs K hK hgen ho with ho2 | ho3 | h4 | h32 | h6
    · exact Or.inl ho2
    · exact Or.inr (Or.inl ho3)
    · exact Or.inr (Or.inr (Or.inl (.linear 2 (by decide) (by simpa using h4))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨1,by decide,by simpa using h32⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h6))))
  · exact Or.inr (Or.inr (Or.inl hb))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hsp))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hbi))))

end CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
