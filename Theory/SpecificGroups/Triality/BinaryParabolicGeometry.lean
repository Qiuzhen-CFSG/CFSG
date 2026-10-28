module
public import Theory.SpecificGroups.Triality.SylowCenterMaximal
public import Theory.SpecificGroups.Triality.SylowParabolicExtensions
/-!
# Proper escaping Borel overgroups in genuine binary triality

The Borel normalizes the full Sylow center of order two, hence centralizes
it. A proper Borel overgroup escaping that centralizer strictly contains
the Borel. The genuine D₄ graph-field Tits geometry identifies every such
strict overgroup with one of the two maximal root parabolics.

Both assertions transport along the original model equivalence and an
aligned Sylow marking. The original M ∩ L application is in ordinary
15.1.22(4), Aschbacher--Smith, printed pp.1098--1099. The root geometry
uses GLS3 §§2.3--2.6 as cited in the imported construction.
-/

public section
open Subgroup Theory.GroupTheory
namespace Triality.Standard.BinaryParabolicGeometry
open Parabolics ConcreteBruhat OuterOdd.Coverage.RootGeometry.SimpleRecognition

private theorem standard_borel_centralizes :
    borel (binaryParameters 1 Nat.zero_lt_one) ≤ centralizer
      ((center (unipotent (binaryParameters 1 Nat.zero_lt_one))).map
        (unipotent (binaryParameters 1 Nat.zero_lt_one)).subtype :
          Set (BinaryCarrier 1 Nat.zero_lt_one)) := by
  let P := binaryParameters 1 Nat.zero_lt_one
  let Z := (center (unipotent P)).map (unipotent P).subtype
  have hz : Nat.card Z = 2 := by
    rw [card_map_of_injective (unipotent P).subtype_injective]
    simpa [P,Parameters.q,binaryParameters] using
      RadicalCoordinates.Centers.card_center_unipotent P rfl
  exact ((borel_le_normalizer_unipotent P rfl).trans
    (normalizer_le_normalizer_characteristic_image (unipotent P) (center (unipotent P)))).trans
      (normalizer_le_centralizer_of_card_two Z hz)

private theorem centralizer_map_equiv {K H : Type*} [Group K] [Group H]
    (e : K ≃* H) (Z : Subgroup K) :
    (centralizer (Z : Set K)).map e.toMonoidHom = centralizer (Z.map e.toMonoidHom : Set H) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro z hz
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using hx (e z) (mem_map_of_mem _ hz)

/-- Proper escaping Borel overgroups are maximal parabolics, on the original Sylow marking. -/
theorem borel_geometry {K : Type*} [Group K]
    (e : K ≃* BinaryCarrier 1 Nat.zero_lt_one) (S : Sylow 2 K) :
    normalizer (S : Set K) ≤ centralizer ((center S).map (S : Subgroup K).subtype : Set K) ∧
      ∀ H : Subgroup K, H ≠ ⊤ → normalizer (S : Set K) ≤ H →
        ¬ H ≤ centralizer ((center S).map (S : Subgroup K).subtype : Set K) → IsCoatom H := by
  let : Finite K := Finite.of_injective e e.injective
  let P := binaryParameters 1 Nat.zero_lt_one
  obtain ⟨_,f,_,hf⟩ := Theory.GroupTheory.SolvableSylowControl.exists_aligned_equiv
    e S (unipotentSylow P rfl)
  change (S : Subgroup K).map f.toMonoidHom = unipotent P at hf
  have hB : (normalizer (S : Set K)).map f.toMonoidHom = borel P := by
    calc
      _ = normalizer (((S : Subgroup K).map f.toMonoidHom) : Set (Carrier P)) :=
        map_equiv_normalizer_eq (S : Subgroup K) f
      _ = _ := by rw [hf]; exact normalizer_unipotent_eq_borel P rfl
  have hZ : ((center S).map (S : Subgroup K).subtype).map f.toMonoidHom =
      (center (unipotent P)).map (unipotent P).subtype := by
    rw [map_map, ← map_center_image_of_injective (S : Subgroup K) f.toMonoidHom f.injective,hf]
  have hC : (centralizer ((center S).map (S : Subgroup K).subtype : Set K)).map
      f.toMonoidHom = centralizer ((center (unipotent P)).map (unipotent P).subtype : Set (Carrier P)) := by
    rw [centralizer_map_equiv,hZ]
  have hBC : normalizer (S : Set K) ≤ centralizer
      ((center S).map (S : Subgroup K).subtype : Set K) := by
    apply (f.mapSubgroup.le_iff_le).mp
    change (normalizer (S : Set K)).map f.toMonoidHom ≤
      (centralizer ((center S).map (S : Subgroup K).subtype : Set K)).map f.toMonoidHom
    rw [hB,hC]
    exact standard_borel_centralizes
  refine ⟨hBC,?_⟩
  intro H hH hBH hout
  have hBlt : borel P < H.map f.toMonoidHom := by
    rw [← hB]
    apply (f.mapSubgroup.lt_iff_lt).mpr
    exact lt_of_le_of_ne hBH (fun he => hout (he ▸ hBC))
  have hproper : H.map f.toMonoidHom ≠ ⊤ := by
    intro he
    apply hH
    apply map_injective (f := f.toMonoidHom) f.injective
    exact he.trans (map_top_of_surjective f.toMonoidHom f.surjective).symm
  obtain ⟨a,ha⟩ := eq_parabolic_of_borel_lt 1 Nat.zero_lt_one _ hBlt hproper
  apply (f.mapSubgroup.isCoatom_iff H).mp
  change IsCoatom (H.map f.toMonoidHom)
  rw [ha]
  exact OddSupplement.parabolic_isCoatom 1 Nat.zero_lt_one a
end Triality.Standard.BinaryParabolicGeometry
