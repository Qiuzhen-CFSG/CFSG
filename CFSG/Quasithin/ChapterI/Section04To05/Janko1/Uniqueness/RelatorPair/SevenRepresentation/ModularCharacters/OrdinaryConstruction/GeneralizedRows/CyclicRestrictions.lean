module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.CyclicRestrictions.Roots
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows.CyclicRestrictions.Fourier
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.OrdinaryConstruction.GeneralizedRows

/-!
# Ordinary J₁ rows on arbitrary cyclic subgroups

An actual generator determines one of the fifteen conjugacy-class labels.
Conjugacy transports the supplied representative power map to every power of
that generator. The exact Fourier certificates then express the restriction
as an integer polynomial in a genuine linear representation of the subgroup.
This covers precisely the orders 1, 2, 3, 5, 6, 7, 10, 11, 15 and 19 supplied
by the class enumeration, preserving the mixed-order and nineteenth-period
label conventions.

`row_cyclic_restriction` discharges the literal cyclic premise of
`ordinaryGeneralizedRows_of_local_restrictions`. The final theorem applies it
to that consumer. Construction of `OrdinaryPowerLabels` and the classification
of the nilpotent subgroups remain separate group-theoretic obligations owned
by the parent source-group assembly.

The numerical certificates retain the GPL-3.0-or-later attribution documented
in `CyclicRestrictions/FourierData.lean`. Source: Janko (1966), ordinary-character
calculation, summarized by Gorenstein, §16.6, printed p.482.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
open CyclicCharacterPolynomial CyclicRestrictions

private theorem row_generator_power {G : Type*} [Group G] [Finite G]
    {c : OrdinaryClassData G} (p : OrdinaryPowerLabels c) (z5 z19 : ℂ)
    (i : Fin 15) (g : G) (n : ℕ) :
    p.row z5 z19 i (g ^ n) = ordinaryValue z5 z19 i (ordinaryPowerClass (p.classIndex g) n) := by
  have hc : IsConj (c.representatives (p.labels (p.classIndex g))) g := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mp
    rw [← c.classes_eq]
    simp [OrdinaryPowerLabels.classIndex]
  have he := ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.pow n)
  simp only [OrdinaryPowerLabels.row, OrdinaryPowerLabels.classIndex] at ⊢
  rw [← he, p.powers]
  simp [OrdinaryPowerLabels.classIndex]

/-- Every literal row is a generalized character on every actual cyclic subgroup,
conditional only on the actual compatible power labels and primitive roots. -/
theorem OrdinaryPowerLabels.row_cyclic_restriction
    {G : Type*} [Group G] [Finite G] {c : OrdinaryClassData G}
    (p : OrdinaryPowerLabels c) (z5 z19 : ℂ)
    (hz5 : IsPrimitiveRoot z5 5) (hz19 : IsPrimitiveRoot z19 19)
    (i : Fin 15) (H : Subgroup G) (hH : IsCyclic H) :
    IsGeneralizedCharacter (fun x : H => p.row z5 z19 i (x : G)) := by
  let : IsCyclic H := hH
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := H)
  let j := p.classIndex (g : G)
  have ho : orderOf g = classOrder j :=
    (Subgroup.orderOf_coe g).symm.trans (p.classIndex_order (g : G)).symm
  obtain ⟨w, hw, h5, h19⟩ := compatible_root z5 z19 hz5 hz19 j
  apply cyclic_realization g hg w (by rw [ho]; exact hw.pow_eq_one) (coefficients j i)
  intro n
  change p.row z5 z19 i ((g : G) ^ n) = _
  rw [row_generator_power]
  have hv : ordinaryValue z5 z19 i (ordinaryPowerClass j n) =
      ordinaryValue (w ^ (classOrder j / 5)) w i (ordinaryPowerClass j n) := by
    apply value_congr
    · intro h
      exact (h5 (h.trans (power_class_dvd j n))).symm
    · intro h
      exact (h19 (h.trans (power_class_dvd j n))).symm
  change ordinaryValue z5 z19 i (ordinaryPowerClass j n) = _
  rw [hv, pow_eq_pow_mod n hw.pow_eq_one]
  have hp : 0 < classOrder j :=
    (by decide +kernel : ∀ l : Fin 15, 0 < classOrder l) j
  have hm : ordinaryPowerClass j n = ordinaryPowerClass j (n % classOrder j) := by
    simp [ordinaryPowerClass]
  rw [hm]
  exact fourier_identity j i w hw ⟨n % classOrder j, Nat.mod_lt n hp⟩

/-- Discharge the cyclic premise of the parent Brauer restriction assembly.
The group-theoretic power labels and nilpotent subgroup classification remain
with the source-group assembly owner. -/
theorem ordinaryGeneralizedRows_of_powerLabels_and_nilpotent_types
    {G : Type*} [Group G] [Finite G] {c : OrdinaryClassData G}
    (p : OrdinaryPowerLabels c)
    (htypes : ∀ H : Subgroup G, Group.IsNilpotent H →
      IsCyclic H ∨ ((∀ x : H, x ^ 2 = 1) ∧ Nat.card H ∣ 8)) :
    Nonempty (OrdinaryGeneralizedRows c) := by
  exact ordinaryGeneralizedRows_of_local_restrictions p htypes p.row_cyclic_restriction

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters
