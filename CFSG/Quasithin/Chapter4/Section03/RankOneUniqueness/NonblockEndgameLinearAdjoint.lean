module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameLinearFixedModule
public import Theory.Representation.SL3.AdjointCubicCentralizer.FixedLevi

/-!
# The ordinary adjoint exclusion and the surviving fixed-space twist

Every invariant section of the original O₂(K_Z) has at most sixteen fixed
elements under the source cubic. An ordinary adjoint model with its marked
diagonal cubic would have at least 256, so it is excluded on these literal
core sections.

The determinant-twisted model has the same entire natural SL₂ fixed-space
action as the original fixed radical. The comparison uses the original
C_K₂(X) action and its original linear-part projection. Thus neither the
fixed-point bound nor the proved natural fixed-module marking selects the
ordinary extension. This does not assert that the twist occurs as a chief
factor of the source group, or give a counterexample to the ambient theorem.

The full extension chief-factor argument, strict secondary core enlargement
and construction of MSData remain with the same nonblock assembly owner,
qt-d-1222-rankone-uniqueness-nonblock. The original A₅ obligation has already
been proved in NonblockAlternatingFiveApplication.
Source: Aschbacher--Smith B.4.14, p.98, and original 4.3.2, pp.618--619.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame
open Representation.SL3.AdjointCubicCentralizer
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}

/-- The original component core has no equivariant quotient with the ordinary
adjoint action of the marked diagonal cubic. Both core subtype maps and the
original action on the section are retained. -/
theorem core_section_not_untwisted_adjoint (d : MSData c 2)
    (m : RootCoordinates d) (s : SecondarySourceData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
    (A : Subgroup G)
    (hA : A ≤ ((pCore 2 s.component).map s.component.subtype).map (rootNormalizer c).subtype)
    [Normalizes X A] {M : Type*} [Group M] [MulDistribMulAction X M]
    (f : A →* M) (hf : Function.Surjective f)
    (he : ∀ (x : X) (a : A), f (x • a) = x • f a)
    (hF : Nat.card F = 4) (x : X) (hx : x ≠ 1) (ω : Fˣ)
    (e : M ≃ TraceZero F)
    (hmodel : ∀ v, e (x • v) = projectiveAdjoint F
      (Matrix.ProjGenLinGroup.mk (diagonalUnit F ω)) (e v)) : False := by
  let : Finite M := Finite.of_surjective f hf
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hu := m.cubic_component_section_fixed_card_le D s X hX hXK hfix A hA f hf he
  have hl := fixed_card_ge_of_adjoint_generator F hF x
    (zpowers_eq_top_of_prime_card hX hx) ω e hmodel
  omega
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceEndgame

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.RootCoordinates
open Representation.SL3.AdjointCubicCentralizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {d : MSData c 2}

/-- The original cubic-fixed radical has exactly the twisted fixed-space action
under the same secondary centralizer. This comparison concerns the fixed
subgroup only; it does not identify a whole component-core chief factor. -/
theorem fixedRadical_equiv_twistedFixed (m : RootCoordinates d)
    (s : SecondarySourceData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (X : Subgroup G) (hX : Nat.card X = 3) (hXK : X ≤ (K c).coreCenterIn 2)
    (hfix : Q c ⊓ centralizer (X : Set G) = ⊥)
    (ω : d.field.Carrierˣ) (hω : (ω : d.field.Carrier) ≠ 1)
    (hω2 : (ω : d.field.Carrier)^2 ≠ 1) :
    ∃ E : (R₂ c ⊓ centralizer (X : Set G) : Subgroup G) ≃*
        Multiplicative (twistedFixedSpace d.field.Carrier ω),
      ∀ k v, (E (fixedRadicalAction X k v)).toAdd =
        (twistedFixedSubrepresentation d.field.Carrier ω hω hω2).toRepresentation
          (m.fixedSecondaryLinear X k) (E v).toAdd := by
  let eN := m.fixedRadicalCoordinates D s X hX hXK hfix
  let eT := twistedFixedRepresentationEquiv d.field.Carrier ω hω hω2
  let E := eN.trans eT.toLinearEquiv.toAddEquiv.toMultiplicative.symm
  refine ⟨E,?_⟩
  intro k v
  change eT.symm.toLinearEquiv (eN (fixedRadicalAction X k v)).toAdd =
    (twistedFixedSubrepresentation d.field.Carrier ω hω hω2).toRepresentation
      (m.fixedSecondaryLinear X k) (eT.symm.toLinearEquiv (eN v).toAdd)
  have hn := m.fixedRadical_action_natural D s X hX hXK hfix k v
  change eN (fixedRadicalAction X k v) =
    Matrix.SL2.naturalAction d.field.Carrier (m.fixedSecondaryLinear X k) (eN v) at hn
  rw [hn]
  exact Representation.IntertwiningMap.isIntertwining _ _ eT.symm.toIntertwiningMap
    (m.fixedSecondaryLinear X k) (eN v).toAdd
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.RootCoordinates
