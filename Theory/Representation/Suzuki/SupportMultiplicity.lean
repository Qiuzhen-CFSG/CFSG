module
public import Theory.Representation.BinaryOffender.Homogeneous.CommutingMultiplicity
public import Theory.Representation.Suzuki.CommutingDisplacement
public import Theory.SpecificGroups.Suzuki.InvolutionSquares
public import Theory.SpecificGroups.Suzuki.ElementaryNormalizer

/-!
# Suzuki multiplicity in a commuting support orbit

Every Suzuki involution has an order-four square root. Simplicity and the
absence of fixed vectors make the Suzuki action faithful on the nonzero
orbit of any commuting irreducible seed. Its order-four operator forces
at least three copies of that seed by the finite Schur-field calculation.

The Chapter D seed-cost argument applies this lower bound to the same
orbit on which the starred actor has its inherited ratio-two bound.
Source: Aschbacher--Smith A.1.41--42 and D.3.9, pp.31--32,200--201;
the concrete Suzuki square calculation is in InvolutionSquares.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.BinaryOffender.Homogeneous
namespace Representation.Suzuki
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A fixed-free Suzuki actor forces three copies in every commuting simple
support orbit. No prior properness or faithfulness on that orbit is assumed. -/
theorem commuting_support_triple_degree
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G)
    (hfix : fixedSpace ρ K = ⊥)
    (m : ℕ) (hm : 0 < m) (e : K ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
    (X : Subgroup G) (hc : K ≤ centralizer (X : Set G))
    (R : Submodule (ZMod 2) V) (hR : X ≤ subspaceStabilizer ρ R)
    (hi : IsIrreducible (invariantSubspace ρ X R hR).toRepresentation) :
    3 * Module.finrank (ZMod 2) R ≤ Module.finrank (ZMod 2) (Homogeneous.orbitSpan ρ K R) := by
  let : Fact (0 < m) := ⟨hm⟩
  let : IsSimpleGroup K := e.isSimpleGroup
  let O := Homogeneous.orbitSpan ρ K R
  let U := invariantSubspace ρ K O (orbitSpan_invariant ρ K R)
  have hn : U ≠ ⊥ := by
    intro hh
    have hO : O = ⊥ := congrArg Subrepresentation.toSubmodule hh
    have hR0 : R = ⊥ := bot_unique ((le_orbitSpan ρ K R).trans hO.le)
    exact ((Subrepresentation.irreducible_iff_isAtom _).mp hi).ne_bot
      (Subrepresentation.toSubmodule_injective hR0)
  have hf := simple_subrepresentation_faithful_of_fixed_eq_bot (ρ.comp K.subtype) hfix U hn
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card'
    (G := BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) 2
    (BenderSuzuki.MatrixGroups.suzukiMatrixGroup_even_card m hm).two_dvd
  obtain ⟨a,ha⟩ := BenderSuzuki.MatrixGroups.suzuki_involution_is_square m hm t ht
  have ha4 : a^4=1 := by
    calc
      a^4 = (a^2)^2 := pow_mul a 2 2
      _ = t^2 := congrArg (fun x => x^2) ha
      _ = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have ha2 : a^2≠1 := by
    rw [ha]
    intro hh
    simp only [hh,orderOf_one] at ht
    omega
  let b := e.symm a
  have hb : b^4=1 := by apply e.injective; simpa only [b,map_pow,map_one,e.apply_symm_apply] using ha4
  have hb2 : b^2≠1 := by
    intro hh
    apply ha2
    simpa only [b,map_pow,map_one,e.apply_symm_apply] using congrArg e hh
  apply CommutingMultiplicity.commuting_orbit_triple_degree ρ X K hc R hR hi b hb
  by_contra! hz
  apply hb2
  apply hf
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  change ρ (b.val^2) v.val = ρ 1 v.val
  simpa only [map_one,Module.End.one_apply] using hz v.val v.property

end Representation.Suzuki
