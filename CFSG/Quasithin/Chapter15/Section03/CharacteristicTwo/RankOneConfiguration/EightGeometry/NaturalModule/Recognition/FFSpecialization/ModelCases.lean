module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.OffenderActor
public import Theory.Representation.BinaryOffender.AmbientSectionTransport

/-!
# Unmarked module outputs and their transport

B.5.1 classifies the component commutator module and sometimes only its
quotient by fixed vectors. Its output coordinates need not use the original
S₈ or PSL₄(2) marking. These types retain those distinctions, as well as the
one-to-three repeated-natural possibility. They are outputs to be proved,
not an assumed reduction of the source classification.

The quotient map gives a surjective projection with precisely the fixed-space
kernel. Restriction to an overgroup containing the component leaves the fixed
space and its quotient unchanged; the three alternatives therefore transport
back without introducing an action of that overgroup on the target coordinates.
Reconciling independently chosen model isomorphisms, preserving the parabolic
marking, and excluding repeated natural modules still require model mathematics.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2(9–10),
B.5.1(1), and 15.3.32(1), printed pp.86, 99–103 and 1132.
-/

@[expose] public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization
open Chapter2.ComponentRefinement.LieType.Binary
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]

/-- The literal quotient by component-fixed vectors, with an independently chosen
alternating-group model. This is classification output, not a source hypothesis. -/
structure OrthogonalQuotient (ρ : Representation (ZMod 2) K V) (L : Subgroup K) where
  model : L ≃* alternatingGroup (Fin 8)
  coordinates : (V ⧸ fixedSpace ρ L) ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 8)
  equivariant : ∀ (l : L) v, coordinates ((fixedSpace ρ L).mkQ (ρ l v)) =
    BinaryPermutation.naturalRepresentation (Fin 8) (model l).val
      (coordinates ((fixedSpace ρ L).mkQ v))

/-- An actual sum of r isomorphic natural modules. The model allows either
choice of the four-dimensional natural module; the multiplicity is retained. -/
structure RepeatedNatural (ρ : Representation (ZMod 2) K V)
    (L : Subgroup K) (r : ℕ) where
  model : L ≃* PSL 4
  coordinates : V ≃ₗ[ZMod 2] (Fin r → Vector 4)
  equivariant : ∀ (l : L) v i, coordinates (ρ l v) i =
    Models.naturalFour (model l) (coordinates v i)

/-- The unreconciled A₈ outputs: an orthogonal quotient, natural plus dual,
or one to three isomorphic natural summands. The classification sieve must
prove this disjunction; it is not assumed as a universal source theorem. -/
def UnmarkedCases (ρ : Representation (ZMod 2) K V) (L : Subgroup K) : Prop :=
  Nonempty (OrthogonalQuotient ρ L) ∨
    (∃ model : L ≃* PSL 4, Nonempty (Models.NaturalDual ρ L model)) ∨
    ∃ r : ℕ, 0 < r ∧ r ≤ 3 ∧ Nonempty (RepeatedNatural ρ L r)

/-- The quotient coordinates yield an actual linear projection on the whole module. -/
noncomputable def OrthogonalQuotient.projection {ρ : Representation (ZMod 2) K V}
    {L : Subgroup K} (h : OrthogonalQuotient ρ L) :
    V →ₗ[ZMod 2] BinaryPermutation.natural (Fin 8) :=
  h.coordinates.toLinearMap.comp (fixedSpace ρ L).mkQ

/-- Both the quotient map and its coordinates are onto. -/
theorem OrthogonalQuotient.projection_surjective {ρ : Representation (ZMod 2) K V}
    {L : Subgroup K} (h : OrthogonalQuotient ρ L) :
    Function.Surjective h.projection :=
  h.coordinates.surjective.comp (Submodule.mkQ_surjective _)

/-- The projection kernel is exactly the original component-fixed space. -/
theorem OrthogonalQuotient.projection_ker {ρ : Representation (ZMod 2) K V}
    {L : Subgroup K} (h : OrthogonalQuotient ρ L) :
    h.projection.ker = fixedSpace ρ L := by
  ext v
  change h.coordinates ((fixedSpace ρ L).mkQ v) = 0 ↔ v ∈ fixedSpace ρ L
  rw [LinearEquiv.map_eq_zero_iff, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]

/-- Compatible quotient coordinates and full commutator generation give the
published orthogonal cover, with the original star marking. -/
noncomputable def OrthogonalQuotient.cover {ρ : Representation (ZMod 2) K V}
    {L : Subgroup K} (h : OrthogonalQuotient ρ L)
    (e : K ≃* Equiv.Perm (Fin 8))
    (he : ∀ l : L, (h.model l).val = e l)
    (hfull : Representation.Coinvariants.ker (ρ.comp L.subtype) = ⊤) :
    Models.OrthogonalCover ρ L e where
  projection := h.projection
  onto := h.projection_surjective
  equivariant l v := by
    change h.coordinates ((fixedSpace ρ L).mkQ (ρ l v)) =
      BinaryPermutation.naturalRepresentation (Fin 8) (e l)
        (h.coordinates ((fixedSpace ρ L).mkQ v))
    rw [h.equivariant, he]
  kernel := h.projection_ker
  generated := hfull

/-- Transport the literal fixed-space quotient across restriction of the ambient
actor. The component elements, quotient representatives and actions are preserved. -/
noncomputable def OrthogonalQuotient.of_subgroupOf
    {ρ : Representation (ZMod 2) K V} {J L : Subgroup K} (hL : L ≤ J)
    (h : OrthogonalQuotient (ρ.comp J.subtype) (L.subgroupOf J)) :
    OrthogonalQuotient ρ L where
  model := (subgroupOfEquivOfLe hL).symm.trans h.model
  coordinates := (Submodule.quotEquivOfEq _ _
    (fixedSpace_subgroupOf ρ L J hL).symm).trans h.coordinates
  equivariant l v := by
    simp only [LinearEquiv.trans_apply, Submodule.mkQ_apply,
      Submodule.quotEquivOfEq_mk]
    exact h.equivariant ((subgroupOfEquivOfLe hL).symm l) v

/-- Reindex the same natural-plus-dual coordinates by the original component. -/
noncomputable def naturalDual_of_subgroupOf
    {ρ : Representation (ZMod 2) K V} {J L : Subgroup K} (hL : L ≤ J)
    {model : L.subgroupOf J ≃* PSL 4}
    (h : Models.NaturalDual (ρ.comp J.subtype) (L.subgroupOf J) model) :
    Models.NaturalDual ρ L ((subgroupOfEquivOfLe hL).symm.trans model) where
  coordinates := h.coordinates
  equivariant l v := h.equivariant ((subgroupOfEquivOfLe hL).symm l) v

/-- Reindex every natural summand without changing the representation or multiplicity. -/
noncomputable def RepeatedNatural.of_subgroupOf
    {ρ : Representation (ZMod 2) K V} {J L : Subgroup K} {r : ℕ} (hL : L ≤ J)
    (h : RepeatedNatural (ρ.comp J.subtype) (L.subgroupOf J) r) :
    RepeatedNatural ρ L r where
  model := (subgroupOfEquivOfLe hL).symm.trans h.model
  coordinates := h.coordinates
  equivariant l v i := h.equivariant ((subgroupOfEquivOfLe hL).symm l) v i

/-- Classification output on a restricted actor concerns the same original
component module after restoring its ambient group. -/
theorem UnmarkedCases.of_subgroupOf
    {ρ : Representation (ZMod 2) K V} {J L : Subgroup K} (hL : L ≤ J)
    (h : UnmarkedCases (ρ.comp J.subtype) (L.subgroupOf J)) : UnmarkedCases ρ L := by
  rcases h with h | h | h
  · obtain ⟨h⟩ := h
    exact Or.inl ⟨h.of_subgroupOf hL⟩
  · obtain ⟨model, ⟨h⟩⟩ := h
    exact Or.inr (Or.inl ⟨_, ⟨naturalDual_of_subgroupOf hL h⟩⟩)
  · obtain ⟨r, hr, hb, ⟨h⟩⟩ := h
    exact Or.inr (Or.inr ⟨r, hr, hb, ⟨h.of_subgroupOf hL⟩⟩)

/-- The B.5.1 input conditions, specialized to V = [V,L]. Finiteness is
explicit; normality is internal to the acting group. The source classifier must
use the genuine known-simple class in the SQTK premise. No model alternative
is part of this record. -/
structure FFInput [Finite K] [Finite V] (known : GroupClass) (ρ : Representation (ZMod 2) K V)
    (L : Subgroup K) : Prop where
  normal : L.Normal
  quasisimple : Theory.GroupTheory.IsQuasisimple L
  sqtk : IsSQTK known L
  faithful : Function.Injective ρ
  twoCore : pCore 2 K = ⊥
  offenders : offenderSubgroup ρ = ⊤
  generalizedFitting : Theory.GroupTheory.generalizedFitting K = L ⊔ center K
  full : Representation.Coinvariants.ker (ρ.comp L.subtype) = ⊤

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.NaturalModule.Recognition.FFSpecialization

end
