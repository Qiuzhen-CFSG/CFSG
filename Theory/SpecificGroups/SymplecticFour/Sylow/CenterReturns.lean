module
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.ParabolicCores
public import Theory.SpecificGroups.SymplecticFour.Sylow.Parabolics

/-!
# Returning conjugates of a central symplectic Sylow subgroup

Both parabolic radicals contain the Sylow center and lie in the same Sylow.
Their parabolics therefore return each central subgroup to that Sylow.
Since the parabolics generate Sp4, any subgroup containing every such
conjugator is the whole group. The field-two case uses the determinant
kernels directly and is included.

Source: Aschbacher–Smith E.2.13(6), printed p.225 (refs/quasithin.pdf).
The Hermitian source selection applies this to the normalizer of B,
retaining the original quotient and Sylow.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem point_parabolic_normalizes_radical {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n) :
    pointParabolic (F := F) ≤ normalizer (pointRadicalAmbient (F := F) : Set (Sp F)) := by
  by_cases he : n = 1
  · have hc : Nat.card F = 2 := by simpa [he] using hF
    rw [←pointLocal_eq_of_card_two hc]
    intro x hx
    exact le_normalizer_map pointLocal.subtype
      ⟨⟨x,hx⟩,le_normalizer_of_normal (mem_top _),rfl⟩
  · rw [pointRadicalAmbient_normalizer hF (by omega)]

private theorem plane_parabolic_normalizes_radical {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n) :
    planeParabolic (F := F) ≤ normalizer (planeRadicalAmbient (F := F) : Set (Sp F)) := by
  by_cases he : n = 1
  · have hc : Nat.card F = 2 := by simpa [he] using hF
    rw [←planeLocal_eq_of_card_two hc]
    intro x hx
    exact le_normalizer_map planeLocal.subtype
      ⟨⟨x,hx⟩,le_normalizer_of_normal (mem_top _),rfl⟩
  · rw [planeRadicalAmbient_normalizer hF (by omega)]

/-- A subgroup containing every conjugator returning a subgroup of the
Sylow center to the Sylow is the full symplectic group, including field two. -/
theorem eq_top_of_central_sylow_returns {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 0 < n)
    (E N : Subgroup (Sp F))
    (hE : E ≤ (center (unipotent (F := F))).map unipotent.subtype)
    (hN : ∀ x : Sp F, E.map (MulAut.conj x).toMonoidHom ≤ unipotent → x ∈ N) : N = ⊤ := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hER : E ≤ pointRadicalAmbient ⊓ planeRadicalAmbient := by
    change E ≤ SymplecticConjugatePair.pointRadical ⊓ SymplecticConjugatePair.planeRadical
    rw [←SymplecticConjugatePair.sylowCenter_eq_radical_inf]
    exact hE
  have hpU : pointRadicalAmbient (F := F) ≤ unipotent := by
    change SymplecticConjugatePair.pointRadical ≤ unipotent
    rw [SymplecticConjugatePair.pointRadical_eq_wing]
    exact map_subtype_le _
  have hqU : planeRadicalAmbient (F := F) ≤ unipotent := by
    change SymplecticConjugatePair.planeRadical ≤ unipotent
    rw [SymplecticConjugatePair.planeRadical_eq_wing]
    exact map_subtype_le _
  have hp : pointParabolic (F := F) ≤ N := by
    intro x hx
    apply hN
    exact (map_mono (hER.trans inf_le_left)).trans
      ((mem_normalizer_iff_map_conj_eq.mp (point_parabolic_normalizes_radical hF hn hx)).le.trans hpU)
  have hq : planeParabolic (F := F) ≤ N := by
    intro x hx
    apply hN
    exact (map_mono (hER.trans inf_le_right)).trans
      ((mem_normalizer_iff_map_conj_eq.mp (plane_parabolic_normalizes_radical hF hn hx)).le.trans hqU)
  exact top_unique (parabolics_sup_eq_top (F := F) ▸ sup_le hp hq)
end Theory.SpecificGroups.SymplecticFour
