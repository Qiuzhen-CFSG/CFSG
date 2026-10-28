module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary.Realization
public import Theory.SpecificGroups.SymplecticFour.BorelActionGeometry.Normalizers

/-!
# Transporting the nonbinary displacement normalizer

The equality L ∩ M = N_L([V,L ∩ M]) transports through the actual
symplectic model. An image equal to the matrix Borel gives the literal
Sylow-normalizer preimage in L/Z(L). A maximal image gives a maximal
parabolic of L, with its Sylow normalizer supplied by the original Borel.

Source: Aschbacher–Smith E.6.8(2), printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
/-- The actual local intersection maps onto the full displacement normalizer. -/
theorem intersection_image_eq_normalizer
    (hclass : DiagramSemilinearCoverage)
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B) (e : L ≃* Sp F) :
    ((L ⊓ M).subgroupOf L).map e.toMonoidHom =
      normalizer (((⁅V, L ⊓ M⁆).subgroupOf L).map e.toMonoidHom : Set (Sp F)) := by
  rw [← map_normalizer_eq_of_bijective _ e.bijective]
  apply congrArg (Subgroup.map e.toMonoidHom)
  rw [← subgroupOf_normalizer_eq (displacement_le_component h hU hL)]
  have he := congrArg (fun J : Subgroup G => J.subgroupOf L)
    (intersection_eq_displacement_normalizer hclass h hU hL hn hm hB)
  simpa only [inf_subgroupOf_left] using he

omit [CharP F 2] in
/-- A matrix Borel image realizes the central-quotient Borel preimage. -/
theorem borelPreimage_of_intersection_image
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (hF : Nat.card F = 2 ^ n) (e : L ≃* Sp F)
    (he : ((L ⊓ M).subgroupOf L).map e.toMonoidHom = Theory.SpecificGroups.SymplecticFour.borel) :
    BorelPreimage L (L ⊓ M) := by
  let S := (unipotentSylow hF (by omega)).mapSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hS : normalizer (S : Set L) = (L ⊓ M).subgroupOf L := by
    change normalizer ((unipotent.map e.symm.toMonoidHom) : Set L) = _
    rw [← map_normalizer_eq_of_bijective _ e.symm.bijective,
      ← borel_eq_normalizer_unipotent, ← he, map_map]
    simp
  have hz : IsPGroup 2 (center L) := by
    rw [model_center_eq_bot hn hm]
    exact IsPGroup.of_subsingleton 2 _
  have hb := LinearThree.borelPreimage_sylow_normalizer S hz
  rwa [hS, map_subgroupOf_eq_of_le inf_le_left] at hb

omit [Finite F] [CharP F 2] in
/-- Maximality transports with the supplied Sylow-normalizer containment. -/
theorem maximalParabolic_of_intersection_image
    (hB : ∃ B : Subgroup G, B ≤ L ⊓ M ∧ BorelPreimage L B)
    (hn : 1 < n) (hm : SymplecticDerivedModel L n)
    (e : L ≃* Sp F)
    (he : IsCoatom (((L ⊓ M).subgroupOf L).map e.toMonoidHom)) :
    MaximalParabolic L (L ⊓ M) := by
  obtain ⟨B, hBJ, hBB⟩ := hB
  obtain ⟨S, hS⟩ := exists_sylow_normalizer_of_borel (model_center_eq_bot hn hm) hBB
  refine ⟨inf_le_left, ?_, S, ?_⟩
  · exact (OrderIso.isCoatom_iff e.mapSubgroup _).mp he
  · rw [← hS]
    exact subgroupOf_mono L hBJ

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.Nonbinary
