module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.Coordinates
public import Mathlib.SetTheory.Cardinal.Order
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.LocalWords

/-!
# An injection from the E6 complement into its fixed diagram space

For the long A2 pair, the folded nodes are the fixed E6 nodes 3 and 2.
The difference of a root and its diagram mate is unchanged by either simple
root step. Orienting each nonzero difference therefore supplies integral
root signs which turn antisymmetric root coordinates into symmetric ones.
The two antisymmetric Cartan coordinates are sent to the invariant vectors
`h₀ + h₅` and `3h₁ - 4h₂ + 2h₃ + 3h₄`. Reading coordinates 0 and 3 proves
injectivity in every characteristic other than two, including three.

The precise signed-generator intertwining remains the separate `Intertwines`
obligation. The parent LongA2 module uses this injection to transfer identity
words from the fixed block to the complement; it assumes no irreducibility.
Sources: the common-lattice construction in GLS3 §2.6.2
(`refs/KGroup/GLS3/chapter2.tex`) and the F4 inclusions in Aschbacher--Smith
A.2.17, printed p.39 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
open Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq Classical.propDecidable

/-- Difference from the diagram mate; fixed simple-root steps preserve it. -/
def displacement (r : typeE6Roots) : typeE6RootSpan :=
  typeE6RootPairing.root r - typeE6RootPairing.root (typeE6DiagramEquiv.indexEquiv r)

@[simp] theorem displacement_diagram (r : typeE6Roots) :
    displacement (typeE6DiagramEquiv.indexEquiv r) = -displacement r := by
  simp [displacement, neg_sub]

@[simp] theorem displacement_eq_zero (r : typeE6Roots) :
    displacement r = 0 ↔ typeE6DiagramEquiv.indexEquiv r = r := by
  rw [displacement, sub_eq_zero, typeE6RootPairing.root.injective.eq_iff, eq_comm]

/-- A coefficient-independent choice of orientation of a nonzero antipodal pair.
Only totality, not compatibility of the auxiliary order with addition, is used. -/
def orientation (x : typeE6RootSpan) : ℤ :=
  if WellOrderingRel x (-x) then 1 else if WellOrderingRel (-x) x then -1 else 0

@[simp] theorem orientation_zero : orientation 0 = 0 := by simp [orientation, irrefl]

@[simp] theorem orientation_neg (x : typeE6RootSpan) :
    orientation (-x) = -orientation x := by
  by_cases h : WellOrderingRel x (-x)
  · have h' : ¬ WellOrderingRel (-x) x := asymm h
    simp [orientation, h, h']
  · by_cases h' : WellOrderingRel (-x) x <;> simp [orientation, h, h']

theorem orientation_sq (x : typeE6RootSpan) (hx : x ≠ 0) : orientation x ^ 2 = 1 := by
  have hn : x ≠ -x := by
    intro h
    apply hx
    have h2 : (2 : ℝ) • x = 0 := by
      calc
        (2 : ℝ) • x = x + x := by module
        _ = 0 := by nth_rw 1 [h]; exact neg_add_cancel x
    exact (smul_eq_zero.mp h2).resolve_left (by norm_num)
  rcases trichotomous_of WellOrderingRel x (-x) with h | h | h
  · simp [orientation, h]
  · exact (hn h).elim
  · simp [orientation, h, asymm h]

/-- Root-coordinate signs are constant along the two fixed-node strings. -/
def rootSign (r : typeE6Roots) : ℤ := orientation (displacement r)

@[simp] theorem rootSign_diagram (r : typeE6Roots) :
    rootSign (typeE6DiagramEquiv.indexEquiv r) = -rootSign r := by
  simp [rootSign]

theorem rootSign_fixed {r : typeE6Roots}
    (h : typeE6DiagramEquiv.indexEquiv r = r) : rootSign r = 0 := by
  simp [rootSign, (displacement_eq_zero r).mpr h]

theorem rootSign_sq {r : typeE6Roots}
    (h : typeE6DiagramEquiv.indexEquiv r ≠ r) : rootSign r ^ 2 = 1 :=
  orientation_sq _ (fun hz => h ((displacement_eq_zero r).mp hz))

/-- No string-length or irreducibility hypothesis is needed for the sign equality. -/
theorem rootSign_add {a r t : typeE6Roots}
    (ha : typeE6DiagramEquiv.indexEquiv a = a)
    (h : typeE6RootPairing.root r = typeE6RootPairing.root a + typeE6RootPairing.root t) :
    rootSign r = rootSign t := by
  have hd := congrArg typeE6DiagramEquiv.weightMap h
  simp only [map_add, typeE6Diagram_weight_root, ha] at hd
  have he : displacement r = displacement t := by
    rw [displacement, h, hd, displacement]
    abel
  exact congrArg orientation he

/-- The same orientation is preserved by negative fixed-node steps. -/
theorem rootSign_sub {a r t : typeE6Roots}
    (ha : typeE6DiagramEquiv.indexEquiv a = a)
    (h : typeE6RootPairing.root r = typeE6RootPairing.root t - typeE6RootPairing.root a) :
    rootSign r = rootSign t := by
  apply Eq.symm
  apply rootSign_add ha
  rw [h]
  abel

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2

namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
open WordDescent Theory.AlgebraicGroup.StandardRootSystem
attribute [local instance] Classical.decEq Classical.propDecidable

/-- The two invariant Cartan vectors for E6 nodes 3 and 2. -/
def cartanZero : Fin 6 → ℤ := ![1, 0, 0, 0, 0, 1]
def cartanOne : Fin 6 → ℤ := ![0, 3, -4, 2, 3, 0]

/-- Both displayed Cartan vectors are killed by the two fixed-node Geck rows. -/
theorem cartanZero_killed (i : Fin 6) (hi : i = 2 ∨ i = 3) :
    ∑ j, |typeE6CartanMatrix i j| * cartanZero j = 0 := by
  rcases hi with rfl | rfl <;> decide

theorem cartanOne_killed (i : Fin 6) (hi : i = 2 ∨ i = 3) :
    ∑ j, |typeE6CartanMatrix i j| * cartanOne j = 0 := by
  rcases hi with rfl | rfl <;> decide

section Ambient
variable (F : Type*) [CommRing F]

/-- Integral sign and Cartan map on the ambient E6 coordinate space. -/
def ambientMap : Space F →ₗ[F] Space F where
  toFun v j := match j with
    | .inl i =>
      (cartanZero (typeE6RootPairing_baseEquiv.symm i) : F) *
        (v (.inl (simpleIndex 0)) - v (.inl (simpleIndex 5))) +
      (cartanOne (typeE6RootPairing_baseEquiv.symm i) : F) *
        (v (.inl (simpleIndex 1)) - v (.inl (simpleIndex 4)))
    | .inr r => (rootSign r : F) * v (.inr r)
  map_add' v w := by
    ext (i | r)
    · simp only [Pi.add_apply]; ring
    · simp only [Pi.add_apply]; ring
  map_smul' a v := by
    ext (i | r)
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem ambientMap_cartan (v : Space F) (i : Fin 6) :
    ambientMap F v (.inl (simpleIndex i)) =
      (cartanZero i : F) * (v (.inl (simpleIndex 0)) - v (.inl (simpleIndex 5))) +
      (cartanOne i : F) * (v (.inl (simpleIndex 1)) - v (.inl (simpleIndex 4))) := by
  simp [ambientMap, simpleIndex]

@[simp] theorem ambientMap_root (v : Space F) (r : typeE6Roots) :
    ambientMap F v (.inr r) = (rootSign r : F) * v (.inr r) := rfl

end Ambient

variable (F : Type*) [Field F]

/-- The literal complement relation, with the original pinned permutation. -/
theorem complement_coordinate (v : complementSpace F) (j : Index) :
    (v : Space F) (typeE6PinnedIndexEquiv j) = -(v : Space F) j :=
  by simpa only [diagramLinear, LinearMap.coe_mk, AddHom.coe_mk,
      neg_smul, one_smul, Pi.neg_apply] using congrFun v.property j

theorem complement_fixed_coordinate (htwo : (2 : F) ≠ 0)
    (v : complementSpace F) (j : Index) (hj : typeE6PinnedIndexEquiv j = j) :
    (v : Space F) j = 0 := by
  have he := complement_coordinate F v j
  rw [hj] at he
  have hz : (2 : F) * (v : Space F) j = 0 := by linear_combination he
  exact (mul_eq_zero.mp hz).resolve_left htwo

/-- Antisymmetric coordinates become diagram-fixed coordinates. -/
theorem ambientMap_mem_fixedSpace (v : complementSpace F) :
    ambientMap F v ∈ fixedSpace F := by
  rw [mem_eigenspace, one_smul]
  ext (i | r)
  · obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    change ambientMap F v (.inl (typeE6DiagramBasePermutation
        (typeE6RootPairing_baseEquiv i))) =
      ambientMap F v (.inl (typeE6RootPairing_baseEquiv i))
    rw [typeE6DiagramBasePermutation_numbered]
    change ambientMap F v (.inl (simpleIndex (typeE6DiagramPermutation i))) =
      ambientMap F v (.inl (simpleIndex i))
    simp only [ambientMap_cartan]
    fin_cases i <;> rfl
  · change (rootSign (typeE6DiagramEquiv.indexEquiv r) : F) *
      (v : Space F) (.inr (typeE6DiagramEquiv.indexEquiv r)) =
        (rootSign r : F) * (v : Space F) (.inr r)
    rw [rootSign_diagram, Int.cast_neg]
    have hv := complement_coordinate F v (.inr r)
    change (v : Space F) (.inr (typeE6DiagramEquiv.indexEquiv r)) =
      -(v : Space F) (.inr r) at hv
    rw [hv, neg_mul_neg]

/-- A concrete embedding candidate; its equivariance is proved separately. -/
def toFixed : complementSpace F →ₗ[F] fixedSpace F :=
  ((ambientMap F).comp (complementSpace F).subtype).codRestrict _
    (ambientMap_mem_fixedSpace F)

@[simp] theorem toFixed_val (v : complementSpace F) :
    (toFixed F v : Space F) = ambientMap F v := rfl

/-- This map remains injective when 3 = 0; coordinate recovery uses only 2. -/
theorem toFixed_injective (htwo : (2 : F) ≠ 0) : Function.Injective (toFixed F) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hz : ambientMap F v = 0 := congrArg Subtype.val hv
  have hc (i : Fin 6) := complement_coordinate F v (.inl (simpleIndex i))
  simp only [typeE6PinnedIndexEquiv_inl, simpleIndex,
    typeE6DiagramBasePermutation_numbered] at hc
  have h0 := congrFun hz (.inl (simpleIndex 0))
  have h3 := congrFun hz (.inl (simpleIndex 3))
  simp only [ambientMap_cartan, Pi.zero_apply] at h0 h3
  have h5 : (v : Space F) (.inl (simpleIndex 5)) =
      -(v : Space F) (.inl (simpleIndex 0)) := hc 0
  have h4 : (v : Space F) (.inl (simpleIndex 4)) =
      -(v : Space F) (.inl (simpleIndex 1)) := hc 1
  have hv0 : (v : Space F) (.inl (simpleIndex 0)) = 0 := by
    have he : (2 : F) * (v : Space F) (.inl (simpleIndex 0)) = 0 := by
      simpa [cartanZero, cartanOne, h5, two_mul] using h0
    exact (mul_eq_zero.mp he).resolve_left htwo
  have hv1 : (v : Space F) (.inl (simpleIndex 1)) = 0 := by
    have he : (2 : F) * ((2 : F) * (v : Space F) (.inl (simpleIndex 1))) = 0 := by
      simpa [cartanZero, cartanOne, h4, two_mul] using h3
    exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left htwo)).resolve_left htwo
  apply Subtype.ext
  ext (i | r)
  · obtain ⟨i, rfl⟩ := typeE6RootPairing_baseEquiv.surjective i
    fin_cases i
    · exact hv0
    · exact hv1
    · exact complement_fixed_coordinate F htwo v _ (by
        simp only [typeE6PinnedIndexEquiv_inl, typeE6DiagramBasePermutation_numbered]; rfl)
    · exact complement_fixed_coordinate F htwo v _ (by
        simp only [typeE6PinnedIndexEquiv_inl, typeE6DiagramBasePermutation_numbered]; rfl)
    · simpa [hv1] using h4
    · simpa [hv0] using h5
  · by_cases hr : typeE6DiagramEquiv.indexEquiv r = r
    · exact complement_fixed_coordinate F htwo v _ (congrArg Sum.inr hr)
    · have hs : (rootSign r : F) ^ 2 = 1 := by
        simpa only [map_pow, map_one, Int.coe_castRingHom] using
          congrArg (Int.castRingHom F) (rootSign_sq hr)
      have hs0 : (rootSign r : F) ≠ 0 := by
        intro he
        simp [he] at hs
      exact (mul_eq_zero.mp (congrFun hz (.inr r))).resolve_left hs0

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2

namespace TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
open WordDescent
variable (F : Type*) [Field F]

/-- The only local geometric obligation on the displayed sign and Cartan map. -/
def Intertwines : Prop := ∀ (s k : Bool) (t : F) (v : complementSpace F),
  toFixed F (eigenspaceAction F (-1) (f4Simple F s (pairNode 0 1 k) t) v) =
    eigenspaceAction F 1 (f4Simple F s (pairNode 0 1 k) t) (toFixed F v)

/-- The literal E6 action of long-pair words on either diagram block. -/
def wordAction (a : F) : PairWord F →* (eigenspace F a ≃ₗ[F] eigenspace F a) :=
  ((eigenspaceAction F a).comp (foldedEvaluation F)).comp (pairInclusion F 0 1)

@[simp] theorem wordAction_of (a : F) (s k : Bool) (t : F) :
    wordAction F a (FreeGroup.of (s, k, t)) =
      eigenspaceAction F a (f4Simple F s (pairNode 0 1 k) t) := by
  simp [wordAction]

/-- Both signs, multiplication and inverses preserve the literal intertwining. -/
theorem word_intertwines (h : Intertwines F) (w : PairWord F)
    (v : complementSpace F) :
    toFixed F (wordAction F (-1) w v) = wordAction F 1 w (toFixed F v) := by
  induction w using FreeGroup.induction_on generalizing v with
  | C1 => simp
  | of x =>
    obtain ⟨s, k, t⟩ := x
    simpa only [wordAction_of] using h s k t v
  | inv_of x ih =>
    simp only [map_inv]
    change toFixed F ((wordAction F (-1) (FreeGroup.of x)).symm v) =
      (wordAction F 1 (FreeGroup.of x)).symm (toFixed F v)
    apply (wordAction F 1 (FreeGroup.of x)).injective
    rw [LinearEquiv.apply_symm_apply]
    simpa only [LinearEquiv.apply_symm_apply] using
      (ih ((wordAction F (-1) (FreeGroup.of x)).symm v)).symm
  | mul x y hx hy =>
    simp only [map_mul, LinearEquiv.mul_apply, hx, hy]

end TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.LongA2
