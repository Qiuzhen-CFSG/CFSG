module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.ThreePrimary.NonsplitTwist
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# A full nonsplit torus in the even-characteristic octonion group

The Coxeter twist from `NonsplitTwist` descends the two independent groups
of (q + 1)-st roots of unity. Injectivity of field extension makes the
chosen descents a homomorphism and reflects its injectivity. Roots of unity
in the algebraic closure have the required cardinality because q + 1 is
prime to the characteristic. The image is therefore an actual subgroup
of G₂(F) of order (q + 1)².

The construction retains its conjugation formula and Lang identity so that
the same conjugator can descend the Weyl normalizer. Constructing that
normalizer and adjoining its order-three cycle remain the missing inputs
to `Nondefining.ThreePrimary`; no multiplier assertion is made here.

Sources: Steinberg 10.7–10.8 in refs/KGroup/GLS3/Chapter2St2.tex;
Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
The octonion model is the licensed ATLAS port; see LICENSES/ATLAS.txt
and LICENSES/ATLAS-CITATION.cff.
-/

open Subgroup
namespace Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
open PRegularClasses.FieldExtension PRegularClasses.RationalFusion
variable (F : Type*) [Field F] [Finite F]
local notation "K" => AlgebraicClosure F

/-- Norm-one coordinates in the algebraic closure of the finite field. -/
public noncomputable abbrev NormOne := rootsOfUnity (Nat.card F + 1) K

/-- Every possible norm-one scalar occurs; its cyclic group has order q + 1. -/
public theorem card_normOne : Nat.card (NormOne F) = Nat.card F + 1 := by
  let := Fintype.ofFinite F
  let : NeZero (Nat.card F + 1) := ⟨by omega⟩
  let : NeZero ((Nat.card F + 1 : ℕ) : F) := ⟨by
    simp [Nat.card_eq_fintype_card]⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K (Nat.card F + 1)

variable [CharP F 2]

/-- A concrete norm-one torus in the finite-field octonion group. -/
public theorem exists_nonsplit_torus :
    ∃ (u : Model K) (j : NormOne F × NormOne F →* Model F),
      u * (frobenius F u)⁻¹ = (weylR * weylS)^3 ∧
      Function.Injective j ∧
      (∀ a : NormOne F × NormOne F,
        fieldEmbedding (algebraMap F K) (j a) = u⁻¹ * torus a.1 a.2 * u) ∧
      Nat.card j.range = (Nat.card F + 1)^2 := by
  obtain ⟨u, hu, hd⟩ := exists_nonsplit_torus_descent F
  have he := fieldEmbedding_injective (algebraMap F K)
  have hex (a : NormOne F × NormOne F) : ∃ d : Model F,
      fieldEmbedding (algebraMap F K) d = u⁻¹ * torus a.1 a.2 * u :=
    hd a.1 a.2 a.1.property a.2.property
  choose s hs using hex
  let j : NormOne F × NormOne F →* Model F := {
    toFun := s
    map_one' := by
      apply he
      rw [hs, map_one]
      change u⁻¹ * torus 1 1 * u = 1
      rw [show (torus (1 : Kˣ) 1 : Model K) = 1 from torusHom.map_one]
      simp
    map_mul' := by
      intro a b
      apply he
      rw [hs, map_mul, hs, hs]
      have ht : (torus ((a*b).1 : Kˣ) ((a*b).2 : Kˣ) : Model K) =
          torus a.1 a.2 * torus b.1 b.2 :=
        map_mul torusHom ((a.1 : Kˣ), (a.2 : Kˣ)) ((b.1 : Kˣ), (b.2 : Kˣ))
      rw [ht]
      group }
  have hj : Function.Injective j := by
    intro a b hab
    have hab' := congrArg (fieldEmbedding (algebraMap F K)) hab
    change fieldEmbedding (algebraMap F K) (s a) =
      fieldEmbedding (algebraMap F K) (s b) at hab'
    rw [hs, hs] at hab'
    have ht : (torus (a.1 : Kˣ) (a.2 : Kˣ) : Model K) = torus b.1 b.2 :=
      mul_left_cancel (mul_right_cancel hab')
    have ht' : ((a.1 : Kˣ), (a.2 : Kˣ)) = ((b.1 : Kˣ), (b.2 : Kˣ)) :=
      torusHom_injective ht
    exact Prod.ext (Subtype.ext (congrArg Prod.fst ht'))
      (Subtype.ext (congrArg Prod.snd ht'))
  refine ⟨u, j, hu, hj, hs, ?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, Nat.card_prod, card_normOne]
  ring

end Atlas.G2.MultiplierOrdinary.Nondefining.ThreePrimary
