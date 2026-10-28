module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Solvable.Construction.Products.Supports.Models
public import Theory.GroupTheory.NormalSymmetricThreeMarked
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Subnormal.Classification.Products.Coprime
/-!
# Cubic residual planes in the native mixed product cases

The embedded two-residual of an S₃ factor has order three. Averaging makes
its moved space disjoint from every relevant fixed kernel, and hence its
rank is bounded above by the actual natural quotient plane. Faithfulness
supplies the lower bound two. The applications retain the literal star
quotient, offender restriction and subgroup inclusions into the ambient group.

These results concern the cubic residual, not the whole S₃ moved space.
Offender generation and the native case records do not imply the requested
whole-factor disjointness: the exact finite diagnostic in
`FixedKernel/source/mixed_shear.py` checks a seven-dimensional action of
S₃ × SL₃(2) satisfying both native alternatives, with a nonzero fixed kernel.
`FixedKernel/source/obstruction.md` describes the action and the distinction
from the stronger marked hypotheses of 13.6.13. The diagnostic is not used
in any Lean proof. The existing conditional whole-factor APIs are preserved.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.4.8(3), printed p.91; B.5.6(3),(5), p.105; and 13.6.13, p.929.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.SourceInduction CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Subnormal.Classification.Products
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) D V)
omit [Finite D] [Module.Finite (ZMod 2) V] in
private theorem moved_mono {A B : Subgroup D} (hAB : A ≤ B) :
    moved ρ A ≤ moved ρ B := by
  apply Submodule.span_mono
  rintro _ ⟨a, ha, v, hv, rfl⟩
  exact ⟨a, hAB ha, v, hv, rfl⟩
/-- Every cubic subgroup of a native S₃ factor moves a plane, including
when the other factor has the exceptional action. -/
theorem factor_cubic_rank (hfaith : Function.Injective ρ)
    {A R : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) (e : A ≃* Equiv.Perm (Fin 3))
    (hRA : R ≤ A) (hR : Nat.card R = 3) :
    Module.finrank (ZMod 2) (moved ρ R) = 2 := by
  obtain ⟨hm, hd, _⟩ := factor_quotient_plane ρ h e
  exact le_antisymm
    ((cubic_finrank_le_quotientImage ρ R hR U (hm ▸ moved_mono ρ hRA)).trans_eq hd)
    (two_le_finrank_subspaceCommutator_of_card_three ρ R hfaith hR)
/-- The hyperplane calculation uses the second factor's own fixed quotient. -/
theorem hyperplane_cubic_rank (hfaith : Function.Injective ρ)
    {A R : Subgroup D} {U : Subrepresentation ρ}
    (hm : U.toSubmodule = moved ρ A)
    (h : HyperplaneSecondCase ρ A U) (e : A ≃* Equiv.Perm (Fin 3))
    (hRA : R ≤ A) (hR : Nat.card R = 3) :
    Module.finrank (ZMod 2) (moved ρ R) = 2 := by
  obtain ⟨hd, _⟩ := hyperplane_quotient_plane ρ h e
  have hu := cubic_finrank_le_fixedQuotient ρ R hR U.toSubmodule
    (hm ▸ moved_mono ρ hRA)
    (Representation.invariants (U.toRepresentation.comp A.subtype))
    (fun u hu r => congrArg Subtype.val (hu ⟨r, hRA r.property⟩))
  exact le_antisymm (hu.trans_eq hd)
    (two_le_finrank_subspaceCommutator_of_card_three ρ R hfaith hR)

omit [Finite D] [Module.Finite (ZMod 2) V] in
private theorem residual_card {A : Subgroup D} (e : A ≃* Equiv.Perm (Fin 3)) :
    Nat.card ((pResidual 2 A).map A.subtype) = 3 := by
  rw [card_map_of_injective A.subtype_injective,
    ← card_map_of_injective (K := pResidual 2 A) (f := e.toMonoidHom) e.injective,
    map_pResidual, Equiv.Perm.twoResidual_eq_alternating, nat_card_alternatingGroup]
  norm_num [Nat.factorial]

omit [Finite D] [Module.Finite (ZMod 2) V] in
private theorem residual_le (A : Subgroup D) : (pResidual 2 A).map A.subtype ≤ A := by
  rintro _ ⟨a, _, rfl⟩
  exact a.property

/-- The actual embedded residual has no global fixed kernel and moves a plane.
No whole-factor splitting is asserted. -/
theorem twoFactor_residual_plane (hfaith : Function.Injective ρ)
    (c : SourceTwoFactorCase ρ) (A : Subgroup D)
    (hA : A = c.first ∨ A = c.second) (e : A ≃* Equiv.Perm (Fin 3)) :
    let R := (pResidual 2 A).map A.subtype
    Disjoint (moved ρ R) ρ.invariants ∧ Module.finrank (ZMod 2) (moved ρ R) = 2 := by
  dsimp only
  obtain ⟨U, hU⟩ : ∃ U, SourceFactorCase ρ A U := by
    rcases hA with rfl | rfl
    · exact ⟨c.firstSpace, c.firstCase⟩
    · exact ⟨c.secondSpace, c.secondCase⟩
  refine ⟨(cubic_disjoint_fixedSpace ρ _ (residual_card e)).mono_right ?_,
    factor_cubic_rank ρ hfaith hU e (residual_le A) (residual_card e)⟩
  intro u hu r
  exact hu r

/-- The cubic residual misses even the second factor's own fixed space. -/
theorem hyperplane_residual_plane (hfaith : Function.Injective ρ)
    (c : HyperplaneCase ρ) (e : c.second ≃* Equiv.Perm (Fin 3)) :
    let R := (pResidual 2 c.second).map c.second.subtype
    Disjoint (moved ρ R) (fixedSpace ρ c.second) ∧
      Module.finrank (ZMod 2) (moved ρ R) = 2 := by
  dsimp only
  refine ⟨(cubic_disjoint_fixedSpace ρ _ (residual_card e)).mono_right
    (by
      intro u hu
      change ∀ r : (pResidual 2 c.second).map c.second.subtype, ρ (r : D) u = u
      intro r
      exact hu ⟨r, residual_le c.second r.property⟩),
    hyperplane_cubic_rank ρ hfaith c.secondSpace_eq c.secondCase e
      (residual_le c.second) (residual_card e)⟩

omit [Finite D] [Module.Finite (ZMod 2) V] in
private theorem commutator_comp_map {E : Type*} [Group E]
    (f : E →* D) (W : Submodule (ZMod 2) V) (A : Subgroup E) :
    subspaceCommutator (ρ.comp f) W A = subspaceCommutator ρ W (A.map f) := by
  unfold subspaceCommutator
  congr 1
  ext w
  constructor
  · rintro ⟨a, ha, u, hu, rfl⟩
    exact ⟨f a, mem_map_of_mem f ha, u, hu, rfl⟩
  · rintro ⟨_, ⟨a, ha, rfl⟩, u, hu, rfl⟩
    exact ⟨a, ha, u, hu, rfl⟩

section Application
open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives
variable {G : Type*} [Group G] [Finite G] (z v : G) [IsElementaryAbelian 2 (Uv z v)]

omit [Finite G] in
private theorem ambient_moved (A : Subgroup (FFFactors.offenderActor (starRepresentation z v))) :
    ambientSpace z v (moved (FFFactors.offenderRepresentation (starRepresentation z v)) A) =
      movedSubgroup z v (A.map (FFFactors.offenderActor (starRepresentation z v)).subtype) := by
  unfold moved FFFactors.offenderRepresentation
  rw [commutator_comp_map, moved_ambientSpace]

/-- On the literal star action, the selected residual moves an order-four
subgroup. This is the cubic support available to the singleton source branch. -/
theorem twoFactor_residual_moved_card
    (c : SourceTwoFactorCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (A : Subgroup (FFFactors.offenderActor (starRepresentation z v)))
    (hA : A = c.first ∨ A = c.second) (e : A ≃* Equiv.Perm (Fin 3)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let R := (pResidual 2 A).map A.subtype
    Nat.card (movedSubgroup z v (R.map I.subtype)) = 4 := by
  dsimp only
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  have hd := (twoFactor_residual_plane _
    (FFFactors.offender_faithful _ (starRepresentation_injective z v)) c A hA e).2
  rw [← ambient_moved, ambientSpace_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
  rfl

/-- The same order-four conclusion for the literal hyperplane residual. -/
theorem hyperplane_residual_moved_card
    (c : HyperplaneCase (FFFactors.offenderRepresentation (starRepresentation z v)))
    (e : c.second ≃* Equiv.Perm (Fin 3)) :
    let I := FFFactors.offenderActor (starRepresentation z v)
    let R := (pResidual 2 c.second).map c.second.subtype
    Nat.card (movedSubgroup z v (R.map I.subtype)) = 4 := by
  dsimp only
  let : Module.Finite (ZMod 2) (Additive (Uv z v)) := Module.Finite.of_finite
  have hd := (hyperplane_residual_plane _
    (FFFactors.offender_faithful _ (starRepresentation_injective z v)) c e).2
  rw [← ambient_moved, ambientSpace_card,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
  rfl

end Application
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.Supports
