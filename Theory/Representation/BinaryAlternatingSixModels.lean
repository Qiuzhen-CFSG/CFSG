module
public import Theory.Representation.BinaryDuadModule
public import Theory.SpecificGroups.SymmetricSix.Parabolics.QuadrangleActions
public import Theory.Alternating.theorem_5_2_1_2
public import Theory.Representation.Quotient
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Concrete binary representations of A₆ and S₆

The first natural action is the existing duad action on the binary symplectic
four-space. We conjugate the pentad outer automorphism of S₆ so that it
exchanges the literal duad and syntheme parabolics. The second natural action
is the pullback along this automorphism. Both actions and their restrictions
to A₆ are irreducible. Their tensor product supplies a concrete sixteen-space.

The marking proof characterizes the parabolics as centralizers of a
transposition and a fixed-point-free involution. The automorphism's values on
these two permutations are certified through six pentad identities each.
No enumeration of all invariant subspaces or all group automorphisms is used.

The four-model predicates require actual equivariant linear isomorphisms.
Exhaustion, identification of the tensor as Steinberg, and the scalar-extension
claims are separate theorems, not consequences of these definitions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), G.5.1–2,
printed pp.342–343; the exceptional automorphism is the existing pentad
construction in `Theory.Alternating.theorem_5_2_1_2`.
-/

@[expose] public section
namespace BinaryAlternatingSix
open Theory.SpecificGroups.SymmetricSix
open Representation
open scoped TensorProduct

/-- The conjugation aligning the two parabolics in the pentad automorphism. -/
def align : S6 := Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 3 5
private def pointInvolution : S6 := Equiv.swap 0 1
private def lineInvolution : S6 := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

/-- A genuine exceptional automorphism exchanging the marked parabolics. -/
noncomputable def diagramAut : MulAut S6 :=
  GLS3.Chapter5.outerAut.trans (MulAut.conj align)

private theorem outer_point : GLS3.Chapter5.outerHom pointInvolution =
    Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4 := by
  apply Equiv.ext
  intro i
  apply GLS3.Chapter5.pentadAt_injective
  change GLS3.Chapter5.pentadAt (GLS3.Chapter5.outerAct pointInvolution i) = _
  rw [GLS3.Chapter5.outerAct_spec]
  fin_cases i <;> decide +kernel

private theorem outer_line : GLS3.Chapter5.outerHom lineInvolution =
    Equiv.swap 2 4 := by
  apply Equiv.ext
  intro i
  apply GLS3.Chapter5.pentadAt_injective
  change GLS3.Chapter5.pentadAt (GLS3.Chapter5.outerAct lineInvolution i) = _
  rw [GLS3.Chapter5.outerAct_spec]
  fin_cases i <;> decide +kernel

private theorem diagram_point : diagramAut pointInvolution = lineInvolution := by
  change align * GLS3.Chapter5.outerHom pointInvolution * align⁻¹ = lineInvolution
  rw [outer_point]
  decide +kernel

private theorem diagram_line : diagramAut lineInvolution = pointInvolution := by
  change align * GLS3.Chapter5.outerHom lineInvolution * align⁻¹ = pointInvolution
  rw [outer_line]
  decide +kernel

private theorem pair_swap (i j : Letter) :
    pair i j = pair 0 1 ↔ Equiv.swap i j = Equiv.swap (0 : Letter) 1 := by
  decide +revert +kernel

private theorem duad_commute (g : S6) :
    g ∈ duadStabilizer ↔ Commute g pointInvolution := by
  change (pair 0 1).image g = pair 0 1 ↔ _
  simp only [commute_iff_eq, pointInvolution, Equiv.mul_swap_eq_swap_mul,
    mul_right_cancel_iff]
  simpa only [pair, Finset.image_insert, Finset.image_singleton] using pair_swap (g 0) (g 1)

private theorem base_pair (i : Letter) : pair i (lineInvolution i) ∈ baseSyntheme := by
  fin_cases i <;> decide

private theorem base_pair_iff (i j : Letter) (h : i ≠ j) :
    pair i j ∈ baseSyntheme ↔ lineInvolution i = j := by
  decide +revert +kernel

private theorem base_pair_exists (p : Finset Letter) (hp : p ∈ baseSyntheme) :
    ∃ i, p = pair i (lineInvolution i) := by
  change p ∈ ({pair 0 1, pair 2 3, pair 4 5} : Finset (Finset Letter)) at hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨4, rfl⟩

private theorem syntheme_commute (g : S6) :
    g ∈ synthemeStabilizer ↔ Commute g lineInvolution := by
  change baseSyntheme.image (fun p => p.image g) = baseSyntheme ↔ _
  constructor
  · intro he
    apply Equiv.ext
    intro i
    have hm : (pair i (lineInvolution i)).image g ∈ baseSyntheme := by
      rw [← he]
      exact Finset.mem_image_of_mem _ (base_pair i)
    have hn : g i ≠ g (lineInvolution i) := g.injective.ne (by fin_cases i <;> decide)
    have hh := (base_pair_iff (g i) (g (lineInvolution i)) hn).mp
      (by simpa only [pair, Finset.image_insert, Finset.image_singleton] using hm)
    exact hh.symm
  · intro hc
    apply Finset.eq_of_subset_of_card_le
    · rintro p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨i, rfl⟩ := base_pair_exists q hq
      have he : g (lineInvolution i) = lineInvolution (g i) := congrArg (fun f : S6 => f i) hc
      simpa only [pair, Finset.image_insert, Finset.image_singleton, he] using base_pair (g i)
    · rw [Finset.card_image_of_injective _ (Finset.image_injective g.injective)]

private theorem map_commute (a b : S6) :
    Commute (diagramAut a) (diagramAut b) ↔ Commute a b := by
  simp only [commute_iff_eq, ← map_mul, diagramAut.injective.eq_iff]

theorem diagramAut_mem_syntheme (g : S6) :
    diagramAut g ∈ synthemeStabilizer ↔ g ∈ duadStabilizer := by
  rw [syntheme_commute, ← diagram_point, map_commute, ← duad_commute]

theorem diagramAut_mem_duad (g : S6) :
    diagramAut g ∈ duadStabilizer ↔ g ∈ synthemeStabilizer := by
  rw [duad_commute, ← diagram_line, map_commute, ← syntheme_commute]

noncomputable def alternatingDiagramAut : MulAut A6 :=
  GLS3.Chapter5.outerAltAut.trans (MulAut.conjNormal align)

@[simp] theorem alternatingDiagramAut_coe (g : A6) :
    (alternatingDiagramAut g).val = diagramAut g.val := rfl

theorem alternatingDiagramAut_mem_syntheme (g : A6) :
    alternatingDiagramAut g ∈ a6SynthemeStabilizer ↔ g ∈ a6DuadStabilizer :=
  diagramAut_mem_syntheme g.val

theorem alternatingDiagramAut_mem_duad (g : A6) :
    alternatingDiagramAut g ∈ a6DuadStabilizer ↔ g ∈ a6SynthemeStabilizer :=
  diagramAut_mem_duad g.val

noncomputable abbrev firstNatural : Representation (ZMod 2) S6 NaturalModule :=
  BinaryDuadModule.naturalAction
noncomputable def secondNatural : Representation (ZMod 2) S6 NaturalModule :=
  firstNatural.comp diagramAut.toMonoidHom
noncomputable abbrev firstAlternating : Representation (ZMod 2) A6 NaturalModule :=
  firstNatural.comp A6.subtype
noncomputable abbrev secondAlternating : Representation (ZMod 2) A6 NaturalModule :=
  secondNatural.comp A6.subtype

@[simp] theorem secondAlternating_apply (g : A6) (v : NaturalModule) :
    secondAlternating g v = firstAlternating (alternatingDiagramAut g) v := rfl

theorem firstAlternating_irreducible : IsIrreducible firstAlternating :=
  BinaryDuadModule.alternatingNaturalAction_irreducible

theorem secondAlternating_irreducible : IsIrreducible secondAlternating :=
  (irreducible_comp_surjective_iff alternatingDiagramAut.toMonoidHom
    alternatingDiagramAut.surjective firstAlternating).mpr firstAlternating_irreducible

abbrev TensorModule := NaturalModule ⊗[ZMod 2] NaturalModule
noncomputable def tensorAction : Representation (ZMod 2) S6 TensorModule :=
  firstNatural.tprod secondNatural
noncomputable abbrev alternatingTensor := tensorAction.comp A6.subtype

theorem tensor_finrank : Module.finrank (ZMod 2) TensorModule = 16 := by
  rw [Module.finrank_tensorProduct, naturalModule_finrank]


noncomputable abbrev trivialSymmetric : Representation (ZMod 2) S6 (ZMod 2) :=
  Representation.trivial (ZMod 2) S6 (ZMod 2)
noncomputable abbrev trivialAlternating : Representation (ZMod 2) A6 (ZMod 2) :=
  trivialSymmetric.comp A6.subtype

/-- The proposed symmetric catalogue records genuine equivariant isomorphisms.
Its universal exhaustion is not assumed or asserted by the model construction. -/
def IsSymmetricModel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) S6 V) : Prop :=
  Nonempty (ρ.Equiv trivialSymmetric) ∨ Nonempty (ρ.Equiv firstNatural) ∨
    Nonempty (ρ.Equiv secondNatural) ∨ Nonempty (ρ.Equiv tensorAction)

/-- The four concrete restricted actions, with actual intertwining equivalences. -/
def IsAlternatingModel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) A6 V) : Prop :=
  Nonempty (ρ.Equiv trivialAlternating) ∨ Nonempty (ρ.Equiv firstAlternating) ∨
    Nonempty (ρ.Equiv secondAlternating) ∨ Nonempty (ρ.Equiv alternatingTensor)

theorem firstNatural_irreducible : IsIrreducible firstNatural := by
  let : IsIrreducible firstAlternating := firstAlternating_irreducible
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun P => ?_⟩
  let Q : Subrepresentation firstAlternating :=
    ⟨P.toSubmodule, fun g _ hv => P.apply_mem_toSubmodule g.val hv⟩
  rcases eq_bot_or_eq_top Q with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective
      (congrArg (fun T : Subrepresentation firstAlternating => T.toSubmodule) h))
  · exact Or.inr (Subrepresentation.toSubmodule_injective
      (congrArg (fun T : Subrepresentation firstAlternating => T.toSubmodule) h))

theorem secondNatural_irreducible : IsIrreducible secondNatural :=
  (irreducible_comp_surjective_iff diagramAut.toMonoidHom diagramAut.surjective
    firstNatural).mpr firstNatural_irreducible

private theorem oneDimensional_irreducible {H : Type*} [Group H]
    (ρ : Representation (ZMod 2) H (ZMod 2)) : IsIrreducible ρ := by
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun P => ?_⟩
  rcases eq_bot_or_eq_top P.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem trivialSymmetric_irreducible : IsIrreducible trivialSymmetric :=
  oneDimensional_irreducible _

theorem trivialAlternating_irreducible : IsIrreducible trivialAlternating :=
  oneDimensional_irreducible _

end BinaryAlternatingSix
