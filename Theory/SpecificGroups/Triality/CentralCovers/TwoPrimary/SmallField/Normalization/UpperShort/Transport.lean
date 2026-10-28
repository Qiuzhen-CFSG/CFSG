module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Normalization.LongPair

/-!
# Transport of the upper short-root trace relation

The inverse folded rotation sends short roots 1 and 2 to short roots 2 and 0,
with parameters F²(s) and F(t). Reversing the commutator preserves the cubic
trace parameter in characteristic two. The same chosen Weyl lift defines
long root 1, so this gives its exact correction in the cover.

The original highest section is the binary section of `highestLift`: its
extra Weyl word projects to the identity and is therefore central. If the
long-pair commutator agrees with `highestLift` at one, the normalized highest
section agrees at both binary parameters. These facts assemble the two
upper exchanges from the still explicit highest trace and comparison inputs.
No equality of lifts is inferred from equality of their projections.

Sources: GLS3 §2.4.5(b)(2), §6.1 (`refs/KGroup/GLS3/chapter2.tex` and
`chapter6.tex`); Aschbacher–Smith A.2.4 and I.1.3
(`refs/quasithin.pdf`, PDF pp.44 and 418).
-/

public section
open Triality.Standard Triality.Standard.ConcreteBruhat
open Triality.Standard.RadicalCoordinates.LeviCommutators
open Triality.Standard.RadicalCoordinates.Centers
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField.UpperShort
noncomputable section

private theorem conjugate_product {G : Type*} [Group G] (g h x : G) :
    (g*h)*x*(g*h)⁻¹ = g*(h*x*h⁻¹)*g⁻¹ := by group

/-- The inverse rotation sends short root 1 to short root 2 with the F² marking. -/
theorem short_one_rotate_back (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    weylRepresentative P hp (.r 5) * short P hp 1 t *
      (weylRepresentative P hp (.r 5))⁻¹ =
        short P hp 2 (fieldFrobenius P (fieldFrobenius P t)) := by
  rw [← short_one_conjugate_carrier P hp t, ← conjugate_product,
    ← weylRepresentative_mul]
  have hw : (DihedralGroup.r 5 : DihedralGroup 6) * .r 2 = .r 1 := by decide
  rw [hw]
  simpa only [fieldFrobenius_three] using short_two_conjugate_carrier P hp
    (fieldFrobenius P (fieldFrobenius P t))

/-- The inverse rotation sends short root 2 to short root 0 with the F marking. -/
theorem short_two_rotate_back (P : Parameters) (hp : P.prime = 2)
    (t : ExtensionField P) :
    weylRepresentative P hp (.r 5) * short P hp 2 t *
      (weylRepresentative P hp (.r 5))⁻¹ =
        short P hp 0 (fieldFrobenius P t) := by
  rw [← short_two_conjugate_carrier P hp t, ← conjugate_product,
    ← weylRepresentative_mul]
  have hw : (DihedralGroup.r 5 : DihedralGroup 6) * .r 1 = 1 := by decide
  rw [hw, weylRepresentative_one, one_mul, inv_one, mul_one]

local notation "P" => binaryParameters 1 Nat.zero_lt_one
local notation "G" => BinaryCarrier 1 Nat.zero_lt_one
variable {E : Type*} [Group E] (f : E →* G)
    (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)

/-- The lift of the identity Weyl word is central, so the original highest section
is exactly the binary section of the chosen short commutator. -/
theorem initialRootSections_long_two (t : fixedField P) :
    (initialRootSections f hf hk).longRoot 2 (.ofAdd t) =
      binaryRootLift (highestLift f hf hk) (highestLift_spec f hf hk).1 (.ofAdd t) := by
  change weylLift f hf (longWeyl 2) * _ * (weylLift f hf (longWeyl 2))⁻¹ = _
  have hc : weylLift f hf (longWeyl 2) ∈ Subgroup.center E := by
    apply hk
    rw [MonoidHom.mem_ker, weylLift_project]
    exact weylRepresentative_one P rfl
  rw [(Subgroup.mem_center_iff.mp hc _).symm, mul_inv_cancel_right]

/-- Every value of an additive binary long-root section is its own inverse. -/
theorem longRoot_inv (L : RootSections 1 Nat.zero_lt_one f) (i : Fin 3)
    (t : fixedField P) : (L.longRoot i (.ofAdd t))⁻¹ = L.longRoot i (.ofAdd t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul]
  have h : (Multiplicative.ofAdd t) * .ofAdd t = 1 := by
    apply Multiplicative.toAdd.injective
    change t + t = 0
    apply Subtype.ext
    exact CharTwo.add_self_eq_zero (t.val : GaloisField 2 3)
  rw [h, map_one]

/-- The remaining highest short-pair calculation for the original sections.
This predicate is a proof obligation, not an asserted identity. -/
@[expose] def HighestShortTrace : Prop :=
  ∀ s t : ExtensionField P,
    ⁅(initialRootSections f hf hk).shortRoot 1 (.ofAdd s),
      (initialRootSections f hf hk).shortRoot 2 (.ofAdd t)⁆ =
        (initialRootSections f hf hk).longRoot 2
          (.ofAdd (cubicTrace P (s * fieldFrobenius P t)))

/-- Transport the highest short-pair formula through the literal inverse Weyl rotation.
Only commutators are compared using their images; the long-root lift is transported
by its defining Weyl word. -/
theorem zero_two_commutator (ht : HighestShortTrace f hf hk)
    (s t : ExtensionField P) :
    ⁅(initialRootSections f hf hk).shortRoot 0 (.ofAdd s),
      (initialRootSections f hf hk).shortRoot 2 (.ofAdd t)⁆ =
        (initialRootSections f hf hk).longRoot 1
          (.ofAdd (cubicTrace P (s * fieldFrobenius P t))) := by
  let L := initialRootSections f hf hk
  let w := weylLift f hf (.r 5)
  have hp1 : f (w * L.shortRoot 1 (.ofAdd (fieldFrobenius P t)) * w⁻¹) =
      f (L.shortRoot 2 (.ofAdd t)) := by
    simp only [map_mul, map_inv, L.project_short, w, weylLift_project]
    simpa only [fieldFrobenius_three] using
      short_one_rotate_back P rfl (fieldFrobenius P t)
  have hp2 : f (w * L.shortRoot 2
      (.ofAdd (fieldFrobenius P (fieldFrobenius P s))) * w⁻¹) =
        f (L.shortRoot 0 (.ofAdd s)) := by
    simp only [map_mul, map_inv, L.project_short, w, weylLift_project]
    simpa only [fieldFrobenius_three] using
      short_two_rotate_back P rfl (fieldFrobenius P (fieldFrobenius P s))
  have hc : ⁅L.shortRoot 0 (.ofAdd s), L.shortRoot 2 (.ofAdd t)⁆ =
      w * ⁅L.shortRoot 1 (.ofAdd (fieldFrobenius P t)),
        L.shortRoot 2 (.ofAdd (fieldFrobenius P (fieldFrobenius P s)))⁆⁻¹ * w⁻¹ := by
    rw [commutatorElement_inv, conjugate_commutatorElement]
    exact CentralExtension.commutator_eq_of_image_eq f hk hp2.symm hp1.symm
  change ⁅L.shortRoot 0 (.ofAdd s), L.shortRoot 2 (.ofAdd t)⁆ = _
  rw [hc, ht, longRoot_inv, fieldFrobenius_three, mul_comm (fieldFrobenius P t) s]
  rw [initialRootSections_long_two]
  rfl

/-- Agreement of the two commutators at one identifies their entire binary sections. -/
theorem normalized_long_two
    (hcomm : CommutingPairs (initialRootSections f hf hk))
    (he : longPairHighest (initialRootSections f hf hk) = highestLift f hf hk)
    (t : fixedField P) :
    (longPairSections hk (initialRootSections f hf hk) hcomm).longRoot 2 (.ofAdd t) =
      (initialRootSections f hf hk).longRoot 2 (.ofAdd t) := by
  rw [initialRootSections_long_two]
  simp [longPairSections, binaryRootLift, he]

private theorem short_inv (L : RootSections 1 Nat.zero_lt_one f) (i : Fin 3)
    (t : ExtensionField P) : (L.shortRoot i (.ofAdd t))⁻¹ = L.shortRoot i (.ofAdd t) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← map_mul]
  have h : (Multiplicative.ofAdd t) * .ofAdd t = 1 := by
    apply Multiplicative.toAdd.injective
    exact CharTwo.add_self_eq_zero (t : GaloisField 2 3)
  rw [h, map_one]

private theorem exchange_of_commutator {x y z : E}
    (hx : x⁻¹ = x) (hy : y⁻¹ = y) (hc : ⁅x,y⁆ = z) : x*y = y*x*z := by
  rw [← hc, commutatorElement_def, hx, hy]
  have hxx : x*x = 1 := by simpa only [hx] using inv_mul_cancel x
  have hyy : y*y = 1 := by simpa only [hy] using inv_mul_cancel y
  calc
    x*y = (y*(x*x)*y)*(x*y) := by rw [hxx, mul_one, hyy, one_mul]
    _ = _ := by group

/-- The highest trace formula and the commutator comparison supply both upper exchanges,
with explicit singleton correction words for all positive parameter tuples. -/
theorem relations_of_trace_and_comparison
    (hcomm : CommutingPairs (initialRootSections f hf hk))
    (ht : HighestShortTrace f hf hk)
    (he : longPairHighest (initialRootSections f hf hk) = highestLift f hf hk) :
    PairExchange (longPairSections hk (initialRootSections f hf hk) hcomm) 0 3 ∧
      PairExchange (longPairSections hk (initialRootSections f hf hk) hcomm) 2 3 := by
  let L := initialRootSections f hf hk
  let M := longPairSections hk L hcomm
  have h03 (s t : ExtensionField P) :
      M.shortRoot 0 (.ofAdd s) * M.shortRoot 2 (.ofAdd t) =
        M.shortRoot 2 (.ofAdd t) * M.shortRoot 0 (.ofAdd s) *
          M.longRoot 1 (.ofAdd (cubicTrace P (s * fieldFrobenius P t))) := by
    apply exchange_of_commutator (short_inv f M 0 s) (short_inv f M 2 t)
    exact zero_two_commutator f hf hk ht s t
  have h23 (s t : ExtensionField P) :
      M.shortRoot 1 (.ofAdd s) * M.shortRoot 2 (.ofAdd t) =
        M.shortRoot 2 (.ofAdd t) * M.shortRoot 1 (.ofAdd s) *
          M.longRoot 2 (.ofAdd (cubicTrace P (s * fieldFrobenius P t))) := by
    apply exchange_of_commutator (short_inv f M 1 s) (short_inv f M 2 t)
    change ⁅L.shortRoot 1 (.ofAdd s), L.shortRoot 2 (.ofAdd t)⁆ = _
    rw [ht, normalized_long_two f hf hk hcomm he]
  constructor
  · intro a b
    refine ⟨[(4, (0, ![0, cubicTrace P (a.1 0 * fieldFrobenius P (b.1 2)), 0]))], ?_, ?_⟩
    · simp [height]
    · simpa [RootSections.factor, FilteredCollection.wordProduct] using h03 (a.1 0) (b.1 2)
  · intro a b
    refine ⟨[(5, (0, ![0, 0, cubicTrace P (a.1 1 * fieldFrobenius P (b.1 2))]))], ?_, ?_⟩
    · simp [height]
    · simpa [RootSections.factor, FilteredCollection.wordProduct] using h23 (a.1 1) (b.1 2)
end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField.UpperShort
