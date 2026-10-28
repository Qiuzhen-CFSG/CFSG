module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The conjugate radical and its fixed plane

If gAg⁻¹ lies in the radical of the stabilizer of P, then A lies in the radical
of the stabilizer of g⁻¹P. Both pointwise fixation and displacement into the
plane are transported. The explicit conjugator prevents confusing the source's
γ and α actions. Conjugation here is left conjugation; for a right-conjugation
source element h, take g = h⁻¹.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.960–962.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure

variable {H : Type*} [Group H]

/-- Conjugation transports the entire radical condition, including its
commutator containment, to the inverse image of the marked plane. -/
theorem le_radical_of_conjugate
    (eH : H ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (P : Submodule (ZMod 2) (Fin 4 → ZMod 2)) (A : Subgroup H) (g : H)
    (hA : (A.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
      BinaryLinear.radical P) :
    A.map eH.toMonoidHom ≤ BinaryLinear.radical (P.map (eH g⁻¹).toLinearMap) := by
  rintro _ ⟨a, ha, rfl⟩
  have he := hA (Subgroup.mem_map.mpr ⟨MulAut.conj g a,
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩)
  change eH (g * a * g⁻¹) ∈ BinaryLinear.radical P at he
  have hcancel (v : Fin 4 → ZMod 2) : eH g (eH g⁻¹ v) = v := by
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  refine ⟨?_, ?_⟩
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := hv
    apply (eH g).injective
    change eH g (eH a (eH g⁻¹ p)) = eH g (eH g⁻¹ p)
    rw [hcancel]
    simpa only [map_mul, LinearEquiv.mul_apply] using he.1 p hp
  · intro v
    refine ⟨eH g (eH a v - v), ?_, ?_⟩
    · change eH g (eH a v - v) ∈ P
      have hd := he.2 (eH g v)
      change eH (g * a * g⁻¹) (eH g v) - eH g v ∈ P at hd
      have hi : eH g⁻¹ (eH g v) = v := by
        rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
        rfl
      simpa only [map_mul, LinearEquiv.mul_apply, hi, map_sub] using hd
    · change eH g⁻¹ (eH g (eH a v - v)) = eH a v - v
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl

/-- The fixed plane used by the terminal contradiction is transported by
the specified conjugator, not identified silently with the original plane. -/
theorem exists_fixed_plane_of_conjugate_radical
    (eH : H ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (P : Submodule (ZMod 2) (Fin 4 → ZMod 2))
    (hP : Module.finrank (ZMod 2) P = 2) (A : Subgroup H) (g : H)
    (hA : (A.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
      BinaryLinear.radical P) :
    ∃ Q : Submodule (ZMod 2) (Fin 4 → ZMod 2),
      Module.finrank (ZMod 2) Q = 2 ∧ ∀ a ∈ A, ∀ v ∈ Q, eH a v = v := by
  let Q := P.map (eH g⁻¹).toLinearMap
  refine ⟨Q, ?_, ?_⟩
  · exact (LinearEquiv.finrank_map_eq (eH g⁻¹) P).trans hP
  · intro a ha v hv
    obtain ⟨p, hp, rfl⟩ := hv
    have he := (hA (Subgroup.mem_map.mpr ⟨MulAut.conj g a,
      Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩)).1 p hp
    change eH (g * a * g⁻¹) p = p at he
    apply (eH g).injective
    have hcancel : eH g (eH g⁻¹ p) = p := by
      rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    change eH g (eH a (eH g⁻¹ p)) = eH g (eH g⁻¹ p)
    rw [hcancel]
    simpa only [map_mul, LinearEquiv.mul_apply] using he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
