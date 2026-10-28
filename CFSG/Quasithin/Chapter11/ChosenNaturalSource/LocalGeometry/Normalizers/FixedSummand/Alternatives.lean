module

public import CFSG.Quasithin.GoldschmidtONan
public import Mathlib.Data.Set.Card

/-!
# The odd-index part of the point-radical GO argument

A Sylow two-subgroup preserving the fixed space makes its orbit odd.
Consequently the swapped and complement alternatives of Goldschmidt--O'Nan
are impossible: their orbit sizes are two and a nontrivial power of two.
Only invariance and the genuine exceptional order-21 action remain.

Source: Aschbacher--Smith, 11.1.5, printed p.766, the exclusion of
conclusions (ii) and (iii) of GLS C.14.2.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.GoldschmidtONan Representation.RegularCyclicNormalClosure

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand

variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) A W} {X : Subgroup A}

@[instance_reducible] private def orbitAction : MulAction A (fixedOrbit ρ X) where
  smul a U := ⟨U.val.map (ρ a), map_mem_fixedOrbit U.property a⟩
  one_smul U := Subtype.ext (orbit_map_one U.val)
  mul_smul a b U := Subtype.ext (orbit_map_mul U.val a b)

/-- Orbit--stabilizer for this exact fixed-space orbit. -/
theorem fixedOrbit_card :
    Nat.card (fixedOrbit ρ X) = (subspaceStabilizer ρ (fixedSpace ρ X)).index := by
  let := orbitAction (ρ := ρ) (X := X)
  let : MulAction.IsPretransitive A (fixedOrbit ρ X) := ⟨fun U U' => by
    obtain ⟨a, ha⟩ := exists_map_eq_of_mem_fixedOrbit U.property U'.property
    exact ⟨a, Subtype.ext ha⟩⟩
  have he : subspaceStabilizer ρ (fixedSpace ρ X) =
      MulAction.stabilizer A (⟨fixedSpace ρ X, fixed_mem_fixedOrbit⟩ : fixedOrbit ρ X) := by
    ext a
    rw [mem_subspaceStabilizer_iff_map]
    change _ ↔ (⟨(fixedSpace ρ X).map (ρ a), _⟩ : fixedOrbit ρ X) = ⟨fixedSpace ρ X, _⟩
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  rw [he]
  exact (MulAction.index_stabilizer_of_transitive A _).symm

/-- Odd stabilizer index removes both even-orbit alternatives. -/
theorem invariant_or_exceptional_of_odd_index [Finite A] [Finite W]
    (h : GoldschmidtONan.Input ρ X) (hodd : Odd (subspaceStabilizer ρ (fixedSpace ρ X)).index) :
    Invariant ρ (fixedSpace ρ X) ∨ ExceptionalCase ρ X := by
  have ho : Odd (Nat.card (fixedOrbit ρ X)) := by rwa [fixedOrbit_card]
  rcases CFSG.Quasithin.GoldschmidtONan.alternatives h with hs | hs | hc | he
  · exact Or.inl hs.2
  · have hcard : Nat.card (fixedOrbit ρ X) = 2 := by
      rw [hs.1, Nat.card_coe_set_eq, Set.ncard_pair h.fixed_ne_moved]
    rw [hcard] at ho
    norm_num at ho
  · rw [hc.1, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at ho
    have hd := h.moved_dimension_gt_one
    have heven : Even (2 ^ Module.finrank (ZMod 2) (displacementSpan ρ X ⊤)) :=
      even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    exact ((Nat.not_even_iff_odd.mpr ho) heven).elim
  · exact Or.inr he

/-- The source Sylow preservation suffices; no index premise is added. -/
theorem invariant_or_exceptional_of_sylow [Finite A] [Finite W]
    (h : GoldschmidtONan.Input ρ X) (P : Sylow 2 A)
    (hP : (P : Subgroup A) ≤ subspaceStabilizer ρ (fixedSpace ρ X)) :
    Invariant ρ (fixedSpace ρ X) ∨ ExceptionalCase ρ X := by
  apply invariant_or_exceptional_of_odd_index h
  apply Nat.not_even_iff_odd.mp
  intro he
  exact P.not_dvd_index ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hP))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
