module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticHall
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticSixParameters
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryGeneration

/-!
# Generation and Hall obstructions on both original symplectic rows

The proved strict weak-closure lower bound and r >= m >= 3n combine
with the original E.3.35 containment theorem to force n(H) > n for
every H-star member. For A₆ = Sp₄(2)′ the same argument gives n(H) > 1.

The whole-orbit Hall reduction therefore applies without an extra
large-generation premise. Either the literal quotient-conjugation image
on L/O₂(L) has Cartan parameter above the table value, or an actual
H-star subgroup contains an elementary odd section kernel fixing the
whole orbit and having a normalizer escaping N_G(L). These are the
remaining alternatives in 7.3.4, not a proof of either upper bound.
NonFFSourceDoubledSymplecticOddAction supplies the same-actor local
configurations needed to finish the second alternative.

Source: Aschbacher--Smith E.3.35, 4.4.14 and 7.3.2--7.3.5,
printed pp.238--239,624--625,698--699, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource ChapterE ChapterE.Section06.FixedPointBounds
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- E.3.35 and the strict H.7 inequality force n(H) above the field degree. -/
theorem sourceOrbit_symplectic_degree_lt_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2))))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) : F.degree < generationParameter H := by
  obtain ⟨hr,hm,_⟩ := D.sourceOrbit_symplectic_initial_parameters h hd F hn hmodel
  have hmr : (F.degree : ℕ∞) < globalR D.sourceOrbit :=
    (ENat.natCast_lt_natCast.mpr (show F.degree < localM D.sourceOrbit by omega)).trans_le hr
  have hw := D.sourceOrbit_symplectic_globalW_gt_degree h hd F hn hmodel
  exact ENat.natCast_lt_natCast.mp ((lt_min hw hmr).trans_le
    (D.sourceOrbit_doubled_min_parameters_le_generation h hd hH))

/-- The genuine binary derived row forces n(H) > 1 on every original H-star member. -/
theorem sourceOrbit_six_one_lt_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6)))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G)
      (normalizer (L : Set G))) : 1 < generationParameter H := by
  obtain ⟨hr,hm,_⟩ := D.sourceOrbit_six_initial_parameters h hd hmodel
  have hmr : (1 : ℕ∞) < globalR D.sourceOrbit :=
    (ENat.natCast_lt_natCast.mpr (show 1 < localM D.sourceOrbit by omega)).trans_le hr
  have hw := D.sourceOrbit_six_globalW_gt_one h hd hmodel
  exact ENat.natCast_lt_natCast.mp ((lt_min hw hmr).trans_le
    (D.sourceOrbit_doubled_min_parameters_le_generation h hd hH))

/-- The nonbinary row supplies an oversized original Cartan parameter or an actual escaping Hall-kernel actor. -/
theorem sourceOrbit_symplectic_cartan_or_odd_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2)))) :
    F.degree < nPrime (normalizerPCoreQuotientAction L).range ∨
      ∃ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      F.degree < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨H,hH⟩ := D.doubledOrbit_outside_of_many h hmany
  have hgen := D.sourceOrbit_symplectic_degree_lt_generation h hd F hn hmodel hH
  rcases D.sourceOrbit_whole_generation_or_odd_escape h hmany hnon hH
      (hn.trans hgen) with hc | ho
  · exact Or.inl (hgen.trans_le hc)
  · exact Or.inr ⟨H,hH,hgen,ho⟩

/-- The A₆ row supplies the same original Hall obstruction at table value one. -/
theorem sourceOrbit_six_cartan_or_odd_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (alternatingNatural 6))) :
    1 < nPrime (normalizerPCoreQuotientAction L).range ∨
      ∃ (H : Subgroup G), H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      1 < generationParameter H ∧
      ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ Odd p ∧ A ≠ ⊥ ∧
        IsElementaryAbelian p A ∧ A ≤ H ∧ A ≤ Chapter4.sectionCentralizer L ∧
        A ≤ centralizer (D.sourceOrbit : Set G) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        ¬ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨H,hH⟩ := D.doubledOrbit_outside_of_many h hmany
  have hgen := D.sourceOrbit_six_one_lt_generation h hd hmodel hH
  rcases D.sourceOrbit_whole_generation_or_odd_escape h hmany hnon hH hgen with hc | ho
  · exact Or.inl (hgen.trans_le hc)
  · exact Or.inr ⟨H,hH,hgen,ho⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
