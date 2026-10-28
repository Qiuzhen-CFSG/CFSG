module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.Reduction
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.SpecificGroups.BinaryLinear.NaturalDualFlag

/-!
# Actual module coordinates for the four-dimensional branch

The actor on `U_L = [W_L,L]` is ambient conjugation. The earlier bound
`O₂(L) ≤ R ≤ C_G(V)` makes this action descend through the actual
quotient `L/O₂(L)`. The two output types below describe the entire `U_L`,
with equivariant coordinates on repeated natural modules or on the natural
module plus its contragredient. Each retains its own projective-linear
marking; no agreement between independently chosen markings is assumed.

`ModuleAlternatives` is an output interface for the B.5.1 application in
15.3.24. Neither its existence nor either case's exclusion is asserted here.
In particular, the central quotient in the discarded orthogonal case must
be treated separately before constructing this output.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed p.1129 (PDF p.1146).
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

variable {G : Type*} [Group G] (d : LocalData G)

/-- The original component commutator is contained in its conjugate span. -/
theorem spanCommutator_le_span (L : Subgroup G) :
    spanCommutator d L ≤ d.componentSpan L :=
  le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy d.V L)

/-- Conjugation by `L` on the actual subgroup `[W_L,L]`. -/
def commutatorAction (L : Subgroup G) : L →* MulAut (spanCommutator d L) :=
  (spanCommutator d L).normalizerMonoidHom.comp
    (inclusion (normalizer_commutator_ge_right (d.componentSpan L) L))

/-- The action uses the same elements and the ambient conjugation convention. -/
theorem commutatorAction_apply (L : Subgroup G) (l : L) (u : spanCommutator d L) :
    (commutatorAction d L l u : G) = (l : G) * u * (l : G)⁻¹ := rfl

/-- The kernel is the literal centralizer inside the component. -/
theorem commutatorAction_ker (L : Subgroup G) :
    (commutatorAction d L).ker =
      (centralizer (spanCommutator d L : Set G)).subgroupOf L := by
  rw [commutatorAction, ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
  rfl

/-- The core bound in 15.3.12 kills the action on the commutator module,
as well as on the whole span. -/
theorem core_le_commutatorAction_ker (L : Subgroup G)
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G)) :
    pCore 2 L ≤ (commutatorAction d L).ker := by
  rw [commutatorAction_ker]
  intro l hl
  exact centralizer_le (spanCommutator_le_span d L)
    (core_centralizes_span d L hcore hR (mem_map.mpr ⟨l, hl, rfl⟩))

/-- The action of the actual two-core quotient on `U_L`. -/
def commutatorQuotientAction (L : Subgroup G)
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G)) :
    (L ⧸ pCore 2 L) →* MulAut (spanCommutator d L) :=
  QuotientGroup.lift (pCore 2 L) (commutatorAction d L)
    (core_le_commutatorAction_ker d L hcore hR)

theorem commutatorQuotientAction_apply (L : Subgroup G)
    (hcore : L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    (l : L) (u : spanCommutator d L) :
    (commutatorQuotientAction d L hcore hR (QuotientGroup.mk' _ l) u : G) =
      (l : G) * u * (l : G)⁻¹ := rfl

/-- The concrete binary projective model, with its literal center quotient. -/
abbrev Projective (n : ℕ) := Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2)

/-- Pull the binary natural action back along an actual core-quotient
isomorphism. The dimension restriction is needed for the center comparison. -/
noncomputable def linearAction {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) : L →* LinearGroup n :=
  ((projectiveEquivLinear hn).toMonoidHom.comp e.toMonoidHom).comp
    (QuotientGroup.mk' (pCore 2 L))

/-- Every linear automorphism is realized by an element of the original
component, not just by an abstract element of the projective model. -/
theorem linearAction_surjective {L : Subgroup G} {n : ℕ} (hn : 0 < n)
    (e : (L ⧸ pCore 2 L) ≃* Projective n) :
    Function.Surjective (linearAction hn e) :=
  (projectiveEquivLinear hn).surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))

/-- The parabolic with both end nodes in its Levi factor is the stabilizer
of a two-dimensional subspace. The equality describes the actual preimage
in `L`, in a specified core-quotient marking. It is an output to construct
in 15.3.24, not a parabolic-containment hypothesis for the final exclusion. -/
structure PlaneParabolic (L : Subgroup G)
    (model : (L ⧸ pCore 2 L) ≃* Projective 4) where
  plane : Submodule (ZMod 2) (Space 4)
  dimension : Module.finrank (ZMod 2) plane = 2
  intersection : (d.M ⊓ L).subgroupOf L =
    (BinaryLinear.parabolic plane).comap (linearAction (by decide) model)

/-- The full commutator module is a sum of `r` isomorphic natural modules.
A group equivalence to the elementary binary space retains every vector;
equivariance is with the actual conjugation action, not an unrelated tag. -/
structure RepeatedNatural (L : Subgroup G) (r : ℕ) where
  model : (L ⧸ pCore 2 L) ≃* Projective 4
  coordinates : spanCommutator d L ≃* Multiplicative (Fin r → Space 4)
  equivariant : ∀ (l : L) (u : spanCommutator d L) (i : Fin r),
    (coordinates (commutatorAction d L l u)).toAdd i =
      linearAction (by decide) model l ((coordinates u).toAdd i)

/-- The two summands are natural and dual for the same actor marking.
The inverse in the contragredient action is part of the specification. -/
structure NaturalDual (L : Subgroup G) where
  model : (L ⧸ pCore 2 L) ≃* Projective 4
  coordinates : spanCommutator d L ≃*
    Multiplicative (Space 4 × Module.Dual (ZMod 2) (Space 4))
  equivariant : ∀ (l : L) (u : spanCommutator d L),
    (coordinates (commutatorAction d L l u)).toAdd =
      BinaryLinear.NaturalDualFlag.action (linearAction (by decide) model l)
        (coordinates u).toAdd

/-- The actual remaining B.5.1 outputs after the orthogonal quotient is
excluded. The classification producer must establish this disjunction. -/
def ModuleAlternatives (L : Subgroup G) : Prop :=
  (∃ r : ℕ, 0 < r ∧ r ≤ 3 ∧ Nonempty (RepeatedNatural d L r)) ∨
    Nonempty (NaturalDual d L)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

end
