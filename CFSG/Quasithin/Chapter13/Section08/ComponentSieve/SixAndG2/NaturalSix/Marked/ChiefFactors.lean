module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked.Outer
public import Theory.Representation.SubspaceQuotient
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Two actual noncentral chief factors for the marked residual

Restrict the standard natural module to the embedded two-residual of H2.
The canonical plane is invariant. Its two-dimensional action and the actual
two-dimensional quotient action are irreducible and noncentral: the pair
cycle `(0 2 4)(1 3 5)` lies in the residual and satisfies `X²+X+1=0` on the
whole natural module. An invariant binary line would contradict that identity.

The residual consequently has no nonzero fixed vector on this standard
module, whereas it fixes the duad vector on the opposite module. This also
proves that the two marked actions, including their alternating restrictions,
have no intertwining linear equivalence with the actor marking held fixed.

Source: Aschbacher–Smith 13.8.26–27, printed pp.962–963. These are actual
irreducible module sections, not assumptions about a chief-factor count.
-/

@[expose] public section

open BinaryPermutation Representation.BinaryOffender
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked

open Module

private theorem binary_plane_irreducible {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (t : G)
    (hd : finrank (ZMod 2) W = 2)
    (hp : ∀ v, ρ t (ρ t v) + ρ t v + v = 0) : Representation.IsIrreducible ρ := by
  have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  intro U
  by_cases hb : U = ⊥
  · exact Or.inl hb
  by_cases ht : U = ⊤
  · exact Or.inr ht
  exfalso
  have hb' : U.toSubmodule ≠ ⊥ := fun h => hb (Subrepresentation.toSubmodule_injective h)
  have ht' : U.toSubmodule ≠ ⊤ := fun h => ht (Subrepresentation.toSubmodule_injective h)
  have hdU : finrank (ZMod 2) U.toSubmodule = 1 := by
    have hl := Submodule.finrank_lt ht'
    have hp' : finrank (ZMod 2) U.toSubmodule ≠ 0 :=
      fun hz => hb' (Submodule.finrank_eq_zero.mp hz)
    rw [hd] at hl
    omega
  have : Nontrivial U.toSubmodule := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : U.toSubmodule)
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdU
    (U.toRepresentation t)
  have hp' : U.toRepresentation t (U.toRepresentation t v) + U.toRepresentation t v + v = 0 :=
    Subtype.ext (hp v)
  rw [hc] at hp'
  have htwo : v + v = 0 := by
    have h := @two_smul (ZMod 2) U.toSubmodule _ _ _ v
    simpa only [show (2 : ZMod 2) = 0 from by decide, zero_smul] using h.symm
  fin_cases c
  · change (0 : ZMod 2) • ((0 : ZMod 2) • v) + (0 : ZMod 2) • v + v = 0 at hp'
    exact hv (by simpa only [zero_smul, zero_add] using hp')
  · change (1 : ZMod 2) • ((1 : ZMod 2) • v) + (1 : ZMod 2) • v + v = 0 at hp'
    exact hv (by simpa only [one_smul, htwo, zero_add] using hp')

/-- The pair-cycling element `(0 2 4)(1 3 5)` in the marked residual. -/
def pairCycle : Symmetric :=
  (Equiv.swap 0 2 * Equiv.swap 2 4) * (Equiv.swap 1 3 * Equiv.swap 3 5)

private theorem pairCycle_cube : pairCycle ^ 3 = 1 := by decide

private theorem pairCycle_mem_H2 : pairCycle ∈ H2 := by decide

theorem pairCycle_mem_residual : pairCycle ∈ residual := by
  let t : H2 := ⟨pairCycle, pairCycle_mem_H2⟩
  have ht : t ^ 3 = 1 := Subtype.ext pairCycle_cube
  refine ⟨t, Subgroup.mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one ht) (by decide)

/-- The polynomial `X²+X+1` annihilates this operator on the actual natural module. -/
theorem pairCycle_polynomial (v : Natural) :
    symmetricAction pairCycle (symmetricAction pairCycle v) +
      symmetricAction pairCycle v + v = 0 := by
  rcases vector_cases v with rfl | ⟨d, rfl⟩
  · simp
  change symmetricAction pairCycle (symmetricAction pairCycle (pairVector d.val.1 d.val.2)) +
    symmetricAction pairCycle (pairVector d.val.1 d.val.2) + pairVector d.val.1 d.val.2 = 0
  simp only [symmetricAction, pairVector_map]
  apply Subtype.ext
  change (constants (Fin 6)).mkQ _ + (constants (Fin 6)).mkQ _ +
    (constants (Fin 6)).mkQ _ = 0
  rw [← map_add, ← map_add]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.mem_span_singleton.mpr
  -- An orbit on pairs is a triangle within one 3-cycle, or a matching between
  -- the two 3-cycles. Its binary sum is respectively zero or the constant vector.
  revert d
  decide +kernel

/-- The residual action retains its actual subgroup embedding. -/
abbrev residualAction := symmetricAction.comp residual.subtype

/-- The canonical plane as an actual subrepresentation of the residual action. -/
def chiefPlane : Subrepresentation residualAction where
  toSubmodule := canonicalPlane
  apply_mem_toSubmodule g _ hv :=
    canonicalPlane_map_le_of_mem (residual_le_H2 g.property) (Submodule.mem_map_of_mem hv)

theorem chiefPlane_finrank : finrank (ZMod 2) chiefPlane.toSubmodule = 2 := canonicalPlane_finrank

theorem chiefQuotient_finrank : finrank (ZMod 2) (Natural ⧸ chiefPlane.toSubmodule) = 2 := by
  have h := canonicalPlane.finrank_quotient_add_finrank
  rw [canonicalPlane_finrank, natural_finrank] at h
  change finrank (ZMod 2) (Natural ⧸ canonicalPlane) = 2
  change finrank (ZMod 2) (Natural ⧸ canonicalPlane) + 2 = 4 at h
  omega

theorem chiefPlane_irreducible : Representation.IsIrreducible chiefPlane.toRepresentation := by
  apply binary_plane_irreducible chiefPlane.toRepresentation ⟨pairCycle, pairCycle_mem_residual⟩
    chiefPlane_finrank
  intro v
  exact Subtype.ext (pairCycle_polynomial v)

theorem chiefQuotient_irreducible : Representation.IsIrreducible chiefPlane.quotientRepresentation := by
  apply binary_plane_irreducible chiefPlane.quotientRepresentation
    ⟨pairCycle, pairCycle_mem_residual⟩ chiefQuotient_finrank
  intro v
  obtain ⟨u, rfl⟩ := chiefPlane.toSubmodule.mkQ_surjective v
  simp only [Subrepresentation.quotientRepresentation_mk]
  change chiefPlane.toSubmodule.mkQ (symmetricAction pairCycle (symmetricAction pairCycle u)) +
    chiefPlane.toSubmodule.mkQ (symmetricAction pairCycle u) + chiefPlane.toSubmodule.mkQ u = 0
  rw [← map_add, ← map_add, pairCycle_polynomial, map_zero]

private theorem polynomial_fixed_eq_zero {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (f : W →ₗ[ZMod 2] W) (hp : ∀ v, f (f v) + f v + v = 0) {v : W} (hv : f v = v) :
    v = 0 := by
  have h := hp v
  rw [hv, hv] at h
  have ht : v + v = 0 := by
    have hh := @two_smul (ZMod 2) W _ _ _ v
    simpa only [show (2 : ZMod 2) = 0 from by decide, zero_smul] using hh.symm
  simpa only [ht, zero_add] using h

private theorem polynomial_noncentral {G W : Type*} [Group G]
    [AddCommGroup W] [Module (ZMod 2) W] [Nontrivial W]
    (ρ : Representation (ZMod 2) G W) (t : G)
    (hp : ∀ v, ρ t (ρ t v) + ρ t v + v = 0) : ∃ v, ρ t v ≠ v := by
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  exact ⟨v, fun he => hv (polynomial_fixed_eq_zero (ρ t) hp he)⟩

theorem chiefPlane_noncentral : ∃ g : residual, ∃ v : chiefPlane.toSubmodule, chiefPlane.toRepresentation g v ≠ v := by
  have : Nontrivial chiefPlane.toSubmodule := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [chiefPlane_finrank]; decide)
  refine ⟨⟨pairCycle, pairCycle_mem_residual⟩, polynomial_noncentral _ _ ?_⟩
  intro v
  exact Subtype.ext (pairCycle_polynomial v)

theorem chiefQuotient_noncentral : ∃ g : residual, ∃ v : Natural ⧸ chiefPlane.toSubmodule,
    chiefPlane.quotientRepresentation g v ≠ v := by
  have : Nontrivial (Natural ⧸ chiefPlane.toSubmodule) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2) (by rw [chiefQuotient_finrank]; decide)
  refine ⟨⟨pairCycle, pairCycle_mem_residual⟩, polynomial_noncentral _ _ ?_⟩
  intro v
  obtain ⟨u, rfl⟩ := chiefPlane.toSubmodule.mkQ_surjective v
  simp only [Subrepresentation.quotientRepresentation_mk]
  change chiefPlane.toSubmodule.mkQ (symmetricAction pairCycle (symmetricAction pairCycle u)) +
    chiefPlane.toSubmodule.mkQ (symmetricAction pairCycle u) + chiefPlane.toSubmodule.mkQ u = 0
  rw [← map_add, ← map_add, pairCycle_polynomial, map_zero]

theorem residual_fixed_eq_zero {v : Natural}
    (hv : ∀ g ∈ residual, symmetricAction g v = v) : v = 0 :=
  polynomial_fixed_eq_zero _ pairCycle_polynomial (hv pairCycle pairCycle_mem_residual)

/-- The two actions cannot be identified while fixing the residual's marking. -/
theorem no_marked_linear_equivalence (e : Natural ≃ₗ[ZMod 2] Natural) :
    ¬ (∀ g ∈ residual, ∀ v, e (symmetricAction g v) = oppositeAction g (e v)) := by
  intro he
  have hz : e.symm (pairVector 4 5) = 0 := by
    apply residual_fixed_eq_zero
    intro g hg
    apply e.injective
    rw [he g hg, e.apply_symm_apply, opposite_H2_fixes (residual_le_H2 hg)]
  exact pairVector45_ne_zero (by simpa only [e.apply_symm_apply, map_zero] using congrArg e hz)

/-- The residual's literal inclusion in the alternating group. -/
def residualToAlternating : residual →* Alternating where
  toFun g := ⟨g.val, residual_le_alternating g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem residualAction_eq_alternating : residualAction =
    alternatingAction.comp residualToAlternating := rfl

theorem opposite_residualAction_eq_alternating : oppositeAction.comp residual.subtype =
    oppositeAlternatingAction.comp residualToAlternating := rfl

/-- The two four-dimensional natural A₆ modules are different with the same
marking of A₆, even though their actions are related by an outer automorphism. -/
theorem no_alternating_linear_equivalence (e : Natural ≃ₗ[ZMod 2] Natural) :
    ¬ (∀ g : Alternating, ∀ v, e (alternatingAction g v) = oppositeAlternatingAction g (e v)) := by
  intro he
  apply no_marked_linear_equivalence e
  intro g hg v
  exact he ⟨g, residual_le_alternating hg⟩ v

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked
