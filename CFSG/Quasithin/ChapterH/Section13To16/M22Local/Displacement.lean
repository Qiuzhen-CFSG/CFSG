module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Irreducibility
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement

/-!
# H.13.2 and the displacement spectrum for the native M22 modules

Both literal ten-dimensional modules are absolutely irreducible. Every
odd-prime element has displacement at least six, and an actual cubic element
attains six on both modules. In the native M22 subgroup, equality holds
exactly for order three; the full setwise-pair action retains the literal
six-fixed-point criterion. No unverified Atlas class-name identification is
used. Native involutions have displacement four; fixed-point-free involutions
in the setwise-pair extension have displacement five, and those with a fixed
octad disjoint from the marked pair have displacement three. The calculations
use the actual native group and its setwise-pair extension; transport to
`MulAut M22` and the source's group conjugacy classification are separate.

Source: Aschbacher--Smith, H.13.2, the parameter tables, and H.14.4(3),(4),
printed pp.395--398, combined manuscript of 1 March 2004.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section13To16
open Sporadic.Mathieu MathieuCode Representation.BinaryOffender

/-- The M22 clause of H.13.2 on the actual source carriers and actions. -/
theorem proposition_H_13_2_ten_dimensional :
    m22CodeRepresentation.IsAbsolutelyIrreducible ∧
      m22CocodeRepresentation.IsAbsolutelyIrreducible :=
  ⟨m22Code_isAbsolutelyIrreducible, m22Cocode_isAbsolutelyIrreducible⟩

/-- The odd-prime lower bound for each literal native M22 module. -/
theorem m22_odd_prime_displacement (g : M22) (hp : (orderOf g).Prime)
    (ho : Odd (orderOf g)) :
    6 ≤ fixedCodim m22CodeRepresentation (Subgroup.zpowers g) ∧
      6 ≤ fixedCodim m22CocodeRepresentation (Subgroup.zpowers g) :=
  ⟨m22_code_fixedCodim_ge_six _ hp ho (Nat.card_zpowers g),
    m22_cocode_fixedCodim_ge_six _ hp ho (Nat.card_zpowers g)⟩

/-- The equality case is order three, verified on the native action. -/
theorem m22_odd_prime_displacement_eq_six (g : M22) (hp : (orderOf g).Prime)
    (ho : Odd (orderOf g)) :
    (fixedCodim m22CodeRepresentation (Subgroup.zpowers g) = 6 ↔ orderOf g = 3) ∧
      (fixedCodim m22CocodeRepresentation (Subgroup.zpowers g) = 6 ↔ orderOf g = 3) :=
  ⟨m22_code_fixedCodim_eq_six_iff_cubic _ hp ho (Nat.card_zpowers g),
    m22_cocode_fixedCodim_eq_six_iff_cubic _ hp ho (Nat.card_zpowers g)⟩

/-- The bound is attained by the same genuine native cubic actor on both modules. -/
theorem beta_six_attained_m22 : ∃ g : M22, orderOf g = 3 ∧
    fixedCodim m22CodeRepresentation (Subgroup.zpowers g) = 6 ∧
    fixedCodim m22CocodeRepresentation (Subgroup.zpowers g) = 6 :=
  exists_m22_displacement_six

/-- The odd-prime lower bound also holds on the actual setwise-pair extensions. -/
theorem m22Outer_odd_prime_displacement (g : m22PairStabilizer)
    (hp : (orderOf g).Prime) (ho : Odd (orderOf g)) :
    6 ≤ fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) ∧
      6 ≤ fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) :=
  ⟨m22Outer_code_fixedCodim_ge_six _ hp ho (Nat.card_zpowers g),
    m22Outer_cocode_fixedCodim_ge_six _ hp ho (Nat.card_zpowers g)⟩

/-- The same native cubic witness remains an attaining element in the outer actions. -/
theorem beta_six_attained_m22Outer : ∃ g : m22PairStabilizer, orderOf g = 3 ∧
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) = 6 ∧
    fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 6 :=
  exists_m22Outer_displacement_six

/-- The equality criterion on the actual setwise-pair actions retains the native fixed set. -/
theorem m22Outer_odd_prime_displacement_eq_six (g : m22PairStabilizer)
    (hp : (orderOf g).Prime) (ho : Odd (orderOf g)) :
    (fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) = 6 ↔
      orderOf g = 3 ∧ Nat.card (MulAction.fixedPoints
        ((Subgroup.zpowers g).map m22PairStabilizer.subtype) (Fin 24)) = 6) ∧
    (fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 6 ↔
      orderOf g = 3 ∧ Nat.card (MulAction.fixedPoints
        ((Subgroup.zpowers g).map m22PairStabilizer.subtype) (Fin 24)) = 6) :=
  ⟨m22Outer_code_fixedCodim_eq_six_iff _ hp ho (Nat.card_zpowers g),
    m22Outer_cocode_fixedCodim_eq_six_iff _ hp ho (Nat.card_zpowers g)⟩

/-- The M22 displacement clause of H.14.4(3), on both literal source modules. -/
theorem lemma_H_14_4_3_m22_displacement (g : M22) (hg : orderOf g = 2) :
    fixedCodim m22CodeRepresentation (Subgroup.zpowers g) = 4 ∧
      fixedCodim m22CocodeRepresentation (Subgroup.zpowers g) = 4 :=
  ⟨m22_code_involution_displacement g hg, m22_cocode_involution_displacement g hg⟩

/-- The fixed-point-free rank in H.14.4(4), before transport to Aut(M22). -/
theorem lemma_H_14_4_4_m22_fixedPointFree_displacement (g : m22PairStabilizer)
    (hg : orderOf g = 2) (hf : ∀ i : Fin 24, g.val • i ≠ i) :
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) = 5 ∧
      fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 5 :=
  ⟨m22Outer_code_involution_displacement_of_fixedPointFree g hg hf,
    m22Outer_cocode_involution_displacement_of_fixedPointFree g hg hf⟩

/-- The fixed-octad rank in H.14.4(4). Disjointness makes the actor outer,
and the octad supplies the fixed point required by the incidence calculation. -/
theorem lemma_H_14_4_4_m22_octad_displacement (g : m22PairStabilizer)
    (hg : orderOf g = 2) (O : M24LocalGeometry.Octad)
    (hdisjoint : Disjoint O.val m22Pair)
    (hfixed : ∀ i : Fin 24, g.val • i = i ↔ i ∈ O.val) :
    fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) = 3 ∧
      fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) = 3 := by
  have houter : g ∉ m22ToPairStabilizer.range := by
    intro hi
    have h0 := (m22ToPairStabilizer_mem_range_iff_fixed_zero g).mp hi
    exact Finset.disjoint_left.mp hdisjoint ((hfixed 0).mp h0) (by simp [m22Pair])
  have hnonempty : O.val.Nonempty := Finset.card_pos.mp (by rw [m24Blocks_card _ O.property]; decide)
  obtain ⟨i, hi⟩ := hnonempty
  have hf : ∃ i : Fin 24, g.val • i = i := ⟨i, (hfixed i).mpr hi⟩
  exact ⟨m22Outer_code_involution_displacement_of_fixed g hg houter hf,
    m22Outer_cocode_involution_displacement_of_fixed g hg houter hf⟩

/-- The parameter-table lower bound holds on both actual setwise-pair modules. -/
theorem m22Outer_involution_displacement_lower_bound (g : m22PairStabilizer)
    (hg : orderOf g = 2) :
    3 ≤ fixedCodim m22OuterCodeRepresentation (Subgroup.zpowers g) ∧
      3 ≤ fixedCodim m22OuterCocodeRepresentation (Subgroup.zpowers g) :=
  m22Outer_involution_displacement_ge_three g hg

end CFSG.Quasithin.ChapterH.Section13To16
