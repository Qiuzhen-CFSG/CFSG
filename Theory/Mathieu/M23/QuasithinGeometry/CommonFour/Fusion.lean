module

public import Theory.Mathieu.M23.QuasithinGeometry.CommonFour.Cores

/-!
# Fusion into the two intrinsic M23 cores

The exhaustive native Sylow calculation identifies its two E16 subgroups.
Transporting the global fusion conjugator through the fixed geometric marking
identifies every native E16 with a conjugate of the intrinsic quintet or heptad
core. Both cores occur in the compatible Sylow group and are distinct.

Source: Aschbacher–Smith, H.14.2(1), printed p.397.
-/

public section
namespace Sporadic.Mathieu.M23Geometry.CommonFour
open ElementarySylow

/-- Global fusion retains the actual geometric marking of the Sylow candidates. -/
theorem card16_conjugate_standardCandidate (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ∃ (g : M23) (b : Fin 2),
      A = (standardCandidate b).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨u, b, hu⟩ := card16_conjugate_candidate A hA hc
  refine ⟨u * transport⁻¹, b, ?_⟩
  rw [standardCandidate, Subgroup.map_map]
  have he : (MulAut.conj (u * transport⁻¹)).toMonoidHom.comp
      (MulAut.conj transport).toMonoidHom = (MulAut.conj u).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rwa [he]

/-- Every native E16 is a conjugate of one of the actual intrinsic local cores. -/
theorem card16_conjugate_core (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 16) :
    ∃ g : M23,
      A = ((pCore 2 quintetStabilizer).map quintetStabilizer.subtype).map
          (MulAut.conj g).toMonoidHom ∨
      A = ((pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype).map
          (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, b, hb⟩ := card16_conjugate_standardCandidate A hA hc
  refine ⟨g, ?_⟩
  rw [quintet_core_eq, heptad_core_eq]
  fin_cases b
  · exact Or.inl hb
  · exact Or.inr hb

/-- The source's uniqueness assertion includes existence of both E16 cores. -/
theorem sylow_card16_iff (A : Subgroup M23) :
    (IsElementaryAbelian 2 A ∧ Nat.card A = 16 ∧ A ≤ standardSylow.toSubgroup) ↔
      A = (pCore 2 quintetStabilizer).map quintetStabilizer.subtype ∨
      A = (pCore 2 markedHeptadStabilizer).map markedHeptadStabilizer.subtype := by
  constructor
  · rintro ⟨hA, hc, hAS⟩
    exact card16_eq_core A hA hc hAS
  · rw [quintet_core_eq, heptad_core_eq]
    rintro (rfl | rfl)
    · exact ⟨standardCandidate_elementary 0, standardCandidate_card 0,
        standardCandidate_le_sylow 0⟩
    · exact ⟨standardCandidate_elementary 1, standardCandidate_card 1,
        standardCandidate_le_sylow 1⟩

end Sporadic.Mathieu.M23Geometry.CommonFour
