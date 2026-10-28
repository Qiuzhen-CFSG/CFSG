module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Odd
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Quotient
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.PairIncidence
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.Involutions.Ranks

/-!
# Involution displacement on the literal ten-dimensional M22 modules

The ambient eleven-dimensional cocode has displacement four for involutions
with a fixed point and five for fixed-point-free involutions, by the proved
native M24 conjugacy coverage and representative matrix calculations. The
marked-pair incidence theorem and quotient rank-nullity remove one dimension
exactly when an involution with a fixed point exchanges the pair. Thus native
M22 involutions have rank four, and outer involutions have rank five or three
according as their fixed set is empty or nonempty. Equivariant coordinate
duality gives the same ranks on the actual code hyperplane.

Source: Aschbacher--Smith, H.13.1 and H.14.4(3),(4), printed pp.395,397--398,
combined manuscript of 1 March 2004. These results need no additional group
classification or rank premises. Identification of the pair stabilizer with
`MulAut M22` belongs to the source assembly's separate group-theoretic work.
-/

public section

noncomputable section
open Sporadic.Mathieu Representation.BinaryOffender
open MathieuCode.CocodeOctad.Involutions
namespace MathieuCode

private theorem ambient_rank_of_fixed (g : M24) (hg : orderOf g = 2)
    (hf : ∃ i : Fin 24, g • i = i) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers g) = 4 := by
  rcases M24InvolutionCentralizers.involution_classes g hg with hz | ht
  · obtain ⟨c, hc⟩ := isConj_iff.mp hz
    rw [← hc, fixedCodim_zpowers_conj]
    exact fixedCodim_z
  · obtain ⟨c, hc⟩ := isConj_iff.mp ht
    obtain ⟨i, hi⟩ := hf
    change c * t * c⁻¹ = g at hc
    rw [← hc] at hi
    have h := congrArg (fun j : Fin 24 => c⁻¹ • j) hi
    exact (t_fixedPointFree (c⁻¹ • i)
      (by simpa only [mul_smul, inv_smul_smul] using h)).elim

private theorem ambient_rank_of_fixedPointFree (g : M24) (hg : orderOf g = 2)
    (hf : ∀ i : Fin 24, g • i ≠ i) :
    fixedCodim cocodeRepresentation (Subgroup.zpowers g) = 5 := by
  rcases M24InvolutionCentralizers.involution_classes g hg with hz | ht
  · obtain ⟨c, hc⟩ := isConj_iff.mp hz
    have h0 : z • (0 : Fin 24) = 0 := by decide +kernel
    apply (hf (c • 0)).elim
    change c * z * c⁻¹ = g at hc
    rw [← hc]
    simp only [mul_smul, inv_smul_smul, h0]
  · obtain ⟨c, hc⟩ := isConj_iff.mp ht
    rw [← hc, fixedCodim_zpowers_conj]
    exact fixedCodim_t

private theorem coe_order (g : m22PairStabilizer) (hg : orderOf g = 2) :
    orderOf g.val = 2 :=
  (orderOf_injective m22PairStabilizer.subtype Subtype.val_injective g).trans hg

private theorem pair_image (g : m22PairStabilizer) (i : Fin 24) (hi : i ∈ m22Pair) :
    g.val • i = 0 ∨ g.val • i = 9 := by
  have h := MulAction.mem_stabilizer_finset'.mp g.property hi
  simpa only [m22Pair, Finset.mem_insert, Finset.mem_singleton] using h

/-- Within the setwise pair stabilizer, fixing one marked point characterizes the native M22 image. -/
theorem m22ToPairStabilizer_mem_range_iff_fixed_zero (g : m22PairStabilizer) :
    g ∈ m22ToPairStabilizer.range ↔ g.val • (0 : Fin 24) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    exact m22Embedding_fixed_zero u
  · intro h0
    have h9 : g.val • (9 : Fin 24) = 9 := by
      rcases pair_image g 9 (by simp [m22Pair]) with h9 | h9
      · have he : (9 : Fin 24) = 0 := (MulAction.injective g.val) (h9.trans h0.symm)
        exact ((by decide : (9 : Fin 24) ≠ 0) he).elim
      · exact h9
    have hr : g.val ∈ m22Embedding.range := by
      rw [m22Embedding_range]
      exact ⟨h0, h9⟩
    obtain ⟨u, hu⟩ := hr
    exact ⟨u, Subtype.ext hu⟩

/-- An element outside the native M22 image exchanges the distinguished pair. -/
theorem m22PairStabilizer_swaps_of_not_mem_range (g : m22PairStabilizer)
    (hg : g ∉ m22ToPairStabilizer.range) : g.val • (0 : Fin 24) = 9 := by
  exact (pair_image g 0 (by simp [m22Pair])).resolve_left
    (fun h => hg ((m22ToPairStabilizer_mem_range_iff_fixed_zero g).mpr h))

/-- An involution fixing the marked pair pointwise has cocode displacement four. -/
theorem m22Outer_cocode_involution_displacement_of_fixed_zero (g : m22PairStabilizer)
    (hg : orderOf g = 2) (h0 : g.val • (0 : Fin 24) = 0) :
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 4 := by
  have hn : m22PairClass ∉ LinearMap.range (cocodeRepresentation g.val - LinearMap.id) := by
    intro h
    have hm := ((m22PairClass_mem_displacement_iff g hg).mp h).2
    rw [h0] at hm
    exact (by decide : (0 : Fin 24) ≠ 9) hm
  rw [m22Outer_cocode_displacement_of_pair_not_mem g hn]
  exact ambient_rank_of_fixed g.val (coe_order g hg) ⟨0, h0⟩

/-- A fixed-point-free involution has displacement five on the literal cocode quotient. -/
theorem m22Outer_cocode_involution_displacement_of_fixedPointFree (g : m22PairStabilizer)
    (hg : orderOf g = 2) (hf : ∀ i : Fin 24, g.val • i ≠ i) :
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 5 := by
  have hn : m22PairClass ∉ LinearMap.range (cocodeRepresentation g.val - LinearMap.id) := by
    intro h
    obtain ⟨i, hi⟩ := ((m22PairClass_mem_displacement_iff g hg).mp h).1
    exact hf i hi
  rw [m22Outer_cocode_displacement_of_pair_not_mem g hn]
  exact ambient_rank_of_fixedPointFree g.val (coe_order g hg) hf

/-- An outer involution with a fixed point has displacement three on the literal cocode quotient. -/
theorem m22Outer_cocode_involution_displacement_of_fixed (g : m22PairStabilizer)
    (hg : orderOf g = 2) (houter : g ∉ m22ToPairStabilizer.range)
    (hf : ∃ i : Fin 24, g.val • i = i) :
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 3 := by
  have hm := (m22PairClass_mem_displacement_iff g hg).mpr
    ⟨hf, m22PairStabilizer_swaps_of_not_mem_range g houter⟩
  have hr := m22Outer_cocode_displacement_of_pair_mem g hm
  rw [ambient_rank_of_fixed g.val (coe_order g hg) hf] at hr
  omega

/-- Every native M22 involution has displacement four on the literal cocode quotient. -/
theorem m22_cocode_involution_displacement (g : M22) (hg : orderOf g = 2) :
    fixedCodim m22CocodeRepresentation (Subgroup.zpowers g) = 4 := by
  have hi : Function.Injective m22ToPairStabilizer := by
    intro a b h
    exact m22Embedding_injective (congrArg Subtype.val h)
  have hr := m22Outer_cocode_involution_displacement_of_fixed_zero
    (m22ToPairStabilizer g) ((orderOf_injective _ hi g).trans hg)
    (m22Embedding_fixed_zero g)
  rw [← MonoidHom.map_zpowers, fixedCodim, ← fixedSpace_comp_map] at hr
  exact hr

/-- Every native M22 involution has displacement four on the actual code hyperplane. -/
theorem m22_code_involution_displacement (g : M22) (hg : orderOf g = 2) :
    fixedCodim m22CodeRepresentation (Subgroup.zpowers g) = 4 := by
  rw [m22_code_cocode_fixedCodim_zpowers]
  exact m22_cocode_involution_displacement g hg

/-- A fixed-point-free involution has displacement five on the actual code hyperplane. -/
theorem m22Outer_code_involution_displacement_of_fixedPointFree (g : m22PairStabilizer)
    (hg : orderOf g = 2) (hf : ∀ i : Fin 24, g.val • i ≠ i) :
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) = 5 := by
  rw [m22Outer_code_cocode_fixedCodim_zpowers]
  exact m22Outer_cocode_involution_displacement_of_fixedPointFree g hg hf

/-- An outer involution with a fixed point has displacement three on the actual code hyperplane. -/
theorem m22Outer_code_involution_displacement_of_fixed (g : m22PairStabilizer)
    (hg : orderOf g = 2) (houter : g ∉ m22ToPairStabilizer.range)
    (hf : ∃ i : Fin 24, g.val • i = i) :
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) = 3 := by
  rw [m22Outer_code_cocode_fixedCodim_zpowers]
  exact m22Outer_cocode_involution_displacement_of_fixed g hg houter hf

/-- The involution displacement bound three holds throughout the actual pair stabilizer. -/
theorem m22Outer_involution_displacement_ge_three (g : m22PairStabilizer)
    (hg : orderOf g = 2) :
    3 ≤ fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) ∧
      3 ≤ fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) := by
  rw [m22Outer_code_cocode_fixedCodim_zpowers, and_self]
  by_cases hi : g ∈ m22ToPairStabilizer.range
  · rw [m22Outer_cocode_involution_displacement_of_fixed_zero g hg
      ((m22ToPairStabilizer_mem_range_iff_fixed_zero g).mp hi)]
    decide
  · by_cases hf : ∃ i : Fin 24, g.val • i = i
    · rw [m22Outer_cocode_involution_displacement_of_fixed g hg hi hf]
    · rw [m22Outer_cocode_involution_displacement_of_fixedPointFree g hg
        (fun i h => hf ⟨i, h⟩)]
      decide

end MathieuCode
