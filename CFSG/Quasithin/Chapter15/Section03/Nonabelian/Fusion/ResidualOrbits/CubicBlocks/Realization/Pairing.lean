module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization.Summands

/-!
# The actual square and commutator tensor pairing

The square of an element of P lies in V. Since V is central and elementary,
its lower coordinates depend only on the literal quotient coordinate in P/V.
Conjugation makes this square map equivariant for the common product actor.

An equivariant map from the sum of the two natural binary planes to their
tensor product is either zero or the outer-product map. The complementary
cubic kills its value on either pure summand. The stabilizer of a mixed
vector fixes just its tensor line, and the nine mixed vectors form one orbit.
These small matrix checks never enumerate functions between the modules.
The zero square map would make P abelian, contradicting V = [P,P] and |V| = 16.
Finally, the universal identity [x,y] = x² (x⁻¹y)² (y²)⁻¹ gives the required
commutator formula in the same coordinates.

Thus `pairingFormula_of_layerActions` constructs the two fields of the existing
`PairingFormula` from the earlier layer actions and the genuine relative center.
It supplies the pairing calculation to cubic-block realization; it does not
assume block coordinates or any lifted-action conclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.53–55 and 15.3.58(2), printed pp.1146–1148.
-/

@[expose] public section
open Subgroup Matrix
open scoped commutatorElement
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers
open CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
private def seedVector : SumVector :=
  (Multiplicative.ofAdd ![1, 0], Multiplicative.ofAdd ![1, 0])
private def tensorSquare (x : SumVector) : TensorVector :=
  Multiplicative.ofAdd (Matrix.vecMulVec x.1.toAdd x.2.toAdd)
private def shear : PlaneActor := ⟨!![1, 1; 0, 1], by decide +kernel⟩

private theorem seed_fixed :
    sumAction (shear, 1) seedVector = seedVector ∧
    sumAction (1, shear) seedVector = seedVector := by decide +kernel

private theorem tensor_fixed_line : ∀ z : TensorVector,
    tensorAction (shear, 1) z = z → tensorAction (1, shear) z = z →
    z = 1 ∨ z = tensorSquare seedVector := by decide +kernel

private theorem mixed_orbit : ∀ x : SumVector, x.1 ≠ 1 → x.2 ≠ 1 →
    ∃ a : Actor, sumAction a seedVector = x := by decide +kernel

private theorem tensorSquare_equivariant (a : Actor) (x : SumVector) :
    tensorSquare (sumAction a x) = tensorAction a (tensorSquare x) := by
  exact (tensorAction_outer a x.1.toAdd x.2.toAdd).symm

private theorem tensorSquare_pure : ∀ x : SumVector,
    x.1 = 1 ∨ x.2 = 1 → tensorSquare x = 1 := by decide +kernel

private theorem pure_fixed : ∀ x : SumVector,
    x.1 = 1 ∨ x.2 = 1 → ∃ i : Fin 2,
      sumAction (complementaryRotation i) x = x := by decide +kernel

private theorem equivariant_dichotomy (q : SumVector → TensorVector)
    (hq : ∀ (a : Actor) (x : SumVector),
      q (sumAction a x) = tensorAction a (q x)) :
    (∀ x, q x = 1) ∨ (∀ x, q x = tensorSquare x) := by
  have hpure (x : SumVector) (hx : x.1 = 1 ∨ x.2 = 1) : q x = 1 := by
    obtain ⟨i, hi⟩ := pure_fixed x hx
    apply cubic_tensor_fixed i
    rw [← hq, hi]
  have hseed := tensor_fixed_line (q seedVector)
    (by rw [← hq, seed_fixed.1]) (by rw [← hq, seed_fixed.2])
  rcases hseed with hzero | hone
  · left
    intro x
    by_cases hx : x.1 = 1 ∨ x.2 = 1
    · exact hpure x hx
    · push Not at hx
      obtain ⟨a, rfl⟩ := mixed_orbit x hx.1 hx.2
      rw [hq, hzero, map_one]
  · right
    intro x
    by_cases hx : x.1 = 1 ∨ x.2 = 1
    · rw [hpure x hx, tensorSquare_pure x hx]
    · push Not at hx
      obtain ⟨a, rfl⟩ := mixed_orbit x hx.1 hx.2
      rw [hq, hone, tensorSquare_equivariant]
variable {G : Type*} [Group G] {I Y P V : Subgroup G}
  {hIP : I ≤ normalizer (P : Set G)} {hIV : I ≤ normalizer (V : Set G)}
  [(V.subgroupOf P).Normal]

private theorem square_mem (d : LayerActions I Y P V hIP hIV) (x : P) :
    (x : G) ^ 2 ∈ V := by
  have h : x ^ 2 ∈ V.subgroupOf P := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (V.subgroupOf P) (x ^ 2) = 1
    rw [map_pow]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      d.elementary_upper.exponent_dvd_p _
  exact h

private noncomputable def squareValue (d : LayerActions I Y P V hIP hIV)
    (x : P) : TensorVector := d.lowerCoordinates ⟨(x : G) ^ 2, square_mem d x⟩

private theorem squareValue_eq (d : LayerActions I Y P V hIP hIV)
    (hcenter : V = (center P).map P.subtype) (x y : P)
    (he : upperMap d x = upperMap d y) : squareValue d x = squareValue d y := by
  have hq : QuotientGroup.mk' (V.subgroupOf P) x = QuotientGroup.mk' _ y :=
    d.upperCoordinates.injective he
  have hv : (x : G) / (y : G) ∈ V := by
    change x / y ∈ V.subgroupOf P
    exact QuotientGroup.eq_iff_div_mem.mp hq
  have hc : Commute ((x : G) / (y : G)) (y : G) :=
    (LayerActions.lower_central hcenter hv y y.property).symm
  have hs : ((x : G) / (y : G)) ^ 2 = 1 := by
    let _ := d.elementary_lower
    exact elemPow_eq_one_of_isElementaryAbelian _ hv
  have heq : (x : G) ^ 2 = (y : G) ^ 2 := by
    calc
      (x : G) ^ 2 = ((x : G) / (y : G) * y) ^ 2 := by rw [div_mul_cancel]
      _ = ((x : G) / (y : G)) ^ 2 * (y : G) ^ 2 := hc.mul_pow 2
      _ = (y : G) ^ 2 := by rw [hs, one_mul]
  exact congrArg d.lowerCoordinates (Subtype.ext heq)

private theorem upperMap_surjective (d : LayerActions I Y P V hIP hIV) :
    Function.Surjective (upperMap d) :=
  d.upperCoordinates.surjective.comp (QuotientGroup.mk'_surjective _)

private noncomputable def squareCoordinates (d : LayerActions I Y P V hIP hIV)
    (x : SumVector) : TensorVector := squareValue d ((upperMap_surjective d x).choose)

private theorem squareCoordinates_upperMap (d : LayerActions I Y P V hIP hIV)
    (hcenter : V = (center P).map P.subtype) (x : P) :
    squareCoordinates d (upperMap d x) = squareValue d x :=
  squareValue_eq d hcenter _ x (upperMap_surjective d (upperMap d x)).choose_spec

private theorem squareValue_conj (d : LayerActions I Y P V hIP hIV) (g : I) (x : P) :
    squareValue d ⟨(g : G) * (x : G) * (g : G)⁻¹,
      (mem_normalizer_iff.mp (hIP g.property) x).mp x.property⟩ =
      tensorAction (d.actor g) (squareValue d x) := by
  unfold squareValue
  rw [← d.lower_compatible]
  apply congrArg d.lowerCoordinates
  apply Subtype.ext
  change ((g : G) * (x : G) * (g : G)⁻¹) ^ 2 =
    (g : G) * (x : G) ^ 2 * (g : G)⁻¹
  simp only [pow_two, mul_assoc, inv_mul_cancel_left]

private theorem squareCoordinates_equivariant (d : LayerActions I Y P V hIP hIV)
    (hcenter : V = (center P).map P.subtype) (a : Actor) (u : SumVector) :
    squareCoordinates d (sumAction a u) = tensorAction a (squareCoordinates d u) := by
  obtain ⟨g, rfl⟩ := d.onto a
  obtain ⟨x, rfl⟩ := upperMap_surjective d u
  rw [← upperMap_conj d g x, squareCoordinates_upperMap d hcenter,
    squareCoordinates_upperMap d hcenter, squareValue_conj]

private theorem tensor_polarization (u v : SumVector) :
    tensorSquare u * tensorSquare (u⁻¹ * v) * (tensorSquare v)⁻¹ =
      Multiplicative.ofAdd (Matrix.vecMulVec u.1.toAdd v.2.toAdd +
        Matrix.vecMulVec v.1.toAdd u.2.toAdd) := by
  have h : ∀ u v : SumVector,
      tensorSquare u * tensorSquare (u⁻¹ * v) * (tensorSquare v)⁻¹ =
        Multiplicative.ofAdd (Matrix.vecMulVec u.1.toAdd v.2.toAdd +
          Matrix.vecMulVec v.1.toAdd u.2.toAdd) := by decide +kernel
  exact h u v

private theorem commutator_eq_squares (x y : G) :
    ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y ^ 2)⁻¹ := by
  simp [commutatorElement_def, pow_two, mul_assoc]

private theorem squareValue_formula [Finite G] (d : LayerActions I Y P V hIP hIV)
    (hVP : V ≤ P) (hcenter : V = (center P).map P.subtype) (x : P) :
    squareValue d x = tensorSquare (upperMap d x) := by
  rcases equivariant_dichotomy (squareCoordinates d)
    (squareCoordinates_equivariant d hcenter) with hz | hf
  · have hs (y : P) : (y : G) ^ 2 = 1 := by
      have hy : squareValue d y = 1 := by
        rw [← squareCoordinates_upperMap d hcenter y]
        exact hz _
      have he : (⟨(y : G) ^ 2, square_mem d y⟩ : V) = 1 := by
        apply d.lowerCoordinates.injective
        simpa only [squareValue, map_one] using hy
      exact congrArg V.subtype he
    have hcomm (a b : P) : ⁅(a : G), (b : G)⁆ = 1 := by
      rw [commutator_eq_squares, hs a, hs b]
      have hab := hs (a⁻¹ * b)
      change ((a : G)⁻¹ * (b : G)) ^ 2 = 1 at hab
      rw [hab]
      simp
    have hD : ⁅P, P⁆ = ⊥ := by
      apply bot_unique
      apply commutator_le.mpr
      intro a ha b hb
      exact hcomm ⟨a, ha⟩ ⟨b, hb⟩
    have hc : Nat.card V = 1 := by
      rw [d.lower_eq_derived hVP hcenter, hD]
      simp
    rw [d.card_lower] at hc
    contradiction
  · rw [← squareCoordinates_upperMap d hcenter x, hf]

/-- In the earlier source coordinates, squares are pure tensors and commutators
are their polar cross-pairings. All membership witnesses are for the actual
ambient elements; the center is the center of P mapped into G. -/
theorem pairingFormula_of_layerActions [Finite G]
    (d : LayerActions I Y P V hIP hIV) (hVP : V ≤ P)
    (hcenter : V = (center P).map P.subtype) : PairingFormula d := by
  refine ⟨fun x => ⟨square_mem d x, squareValue_formula d hVP hcenter x⟩, ?_⟩
  intro x y
  have hc : ⁅(x : G), (y : G)⁆ ∈ V :=
    d.derived_le_lower (commutator_mem_commutator x.property y.property)
  refine ⟨hc, ?_⟩
  have he : (⟨⁅(x : G), (y : G)⁆, hc⟩ : V) =
      ⟨(x : G) ^ 2, square_mem d x⟩ *
      ⟨((x : G)⁻¹ * (y : G)) ^ 2, square_mem d (x⁻¹ * y)⟩ *
      (⟨(y : G) ^ 2, square_mem d y⟩ : V)⁻¹ :=
    Subtype.ext (commutator_eq_squares _ _)
  change d.lowerCoordinates ⟨⁅(x : G), (y : G)⁆, hc⟩ = _
  rw [he, map_mul, map_mul, map_inv]
  change squareValue d x * squareValue d (x⁻¹ * y) * (squareValue d y)⁻¹ = _
  rw [squareValue_formula d hVP hcenter, squareValue_formula d hVP hcenter,
    squareValue_formula d hVP hcenter, map_mul, map_inv]
  exact tensor_polarization _ _
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.ResidualOrbits.CubicBlocks.Realization
