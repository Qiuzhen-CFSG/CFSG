module
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.E6Folding
public import Theory.FieldTheory.QuadraticFrobeniusFixed

/-!
# The folded E6 subgroup inside the genuine twisted central cover

For q = p^(m+1), the actual q-Frobenius fixed subfield of GF(q²) has q
elements. A field equivalence with GF(q) gives a specified coefficient
embedding. The eight folded simple root curves with fixed coefficients are
fixed by the graph--field involution and killed by p, so they lie in the
literal O^{p'} subgroup used by `TwistedE6.Model`.

Entrywise coefficient mapping embeds the folded subgroup over GF(q) into
this defining-characteristic cover. The closure argument proves residual
membership for its whole image, not just for individual generators.
`coverEmbedding` is injective; `modelMap` composes it with the cover's actual
central projection. Injectivity and properness of `modelMap`, and the F4
identification of its source, remain separate mathematical obligations.

Sources: GLS3 §§2.2--2.4 (`refs/KGroup/GLS3/chapter2.tex`), and the
F4(q) < ²E6(q) inclusion in Aschbacher--Smith A.2.17, printed p.39 of
`refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace TwistedE6.FoldedSubsystem
attribute [local instance] Classical.decEq

variable (p : ℕ) [Fact p.Prime]

def fixedField (m : ℕ) : Subfield (CoefficientField p m) :=
  (fieldTwist p m).toRingHom.eqLocusField (RingHom.id _)

abbrev FixedField (m : ℕ) := ↥(fixedField p m)

@[simp] theorem fixedField_pow (m : ℕ) (t : FixedField p m) :
    (t : CoefficientField p m) ^ parameter p m = t := t.property

theorem fixedField_card (m : ℕ) : Nat.card (FixedField p m) = parameter p m := by
  have h : fixedField p m = FixedBy.subfield (CoefficientField p m) (fieldTwist p m) := by
    ext x
    rfl
  change Nat.card ↥(fixedField p m) = parameter p m
  rw [h]
  exact GaloisField.card_fixedBy_quadraticFrobenius p (m + 1) (by omega)

def coefficientEquiv (m : ℕ) : GaloisField p (m + 1) ≃+* FixedField p m := by
  letI : Fintype (GaloisField p (m + 1)) := Fintype.ofFinite _
  letI : Fintype (FixedField p m) := Fintype.ofFinite _
  apply FiniteField.ringEquivOfCardEq
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    GaloisField.card p (m + 1) (by omega), fixedField_card, parameter]

def coefficientEmbedding (m : ℕ) : GaloisField p (m + 1) →+* CoefficientField p m :=
  (fixedField p m).subtype.comp (coefficientEquiv p m).toRingHom

@[simp] theorem coefficientEmbedding_pow (m : ℕ) (t : GaloisField p (m + 1)) :
    coefficientEmbedding p m t ^ parameter p m = coefficientEmbedding p m t :=
  fixedField_pow p m (coefficientEquiv p m t)

theorem simpleRoot_twist (m : ℕ) (s : Bool) (i : Fin 6) (t : FixedField p m) :
    graphFieldTwist p m (simpleRoot (CoefficientField p m) s i t) =
      simpleRoot (CoefficientField p m) s (typeE6DiagramPermutation i) t := by
  let := Pairing.indexNeg
  cases s
  · change graphFieldTwist p m (rootElement (CoefficientField p m) (-(simpleIndex i) : typeE6Roots) t) =
      rootElement (CoefficientField p m) (-(simpleIndex (typeE6DiagramPermutation i)) : typeE6Roots) t
    rw [graphFieldTwist_negative, fixedField_pow]
    congr 2
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)
  · change graphFieldTwist p m (rootElement (CoefficientField p m) (simpleIndex i) t) =
      rootElement (CoefficientField p m) (simpleIndex (typeE6DiagramPermutation i)) t
    rw [graphFieldTwist_positive, fixedField_pow]
    congr 1
    exact congrArg Subtype.val (typeE6DiagramBasePermutation_numbered i)

def foldedSplit (m : ℕ) (s : Bool) (i : Fin 4) (t : FixedField p m) :
    rootGeneratedSubgroup p m := foldedSimple (CoefficientField p m) s i t

theorem foldedSplit_add (m : ℕ) (s : Bool) (i : Fin 4) (t u : FixedField p m) :
    foldedSplit p m s i (t + u) = foldedSplit p m s i t * foldedSplit p m s i u :=
  foldedSimple_add (CoefficientField p m) s i t u

@[simp] theorem foldedSplit_zero (m : ℕ) (s : Bool) (i : Fin 4) :
    foldedSplit p m s i 0 = 1 := foldedSimple_zero (CoefficientField p m) s i

theorem foldedSplit_fixed (m : ℕ) (s : Bool) (i : Fin 4) (t : FixedField p m) :
    graphFieldTwist p m (foldedSplit p m s i t) = foldedSplit p m s i t := by
  fin_cases i
  · change graphFieldTwist p m (simpleRoot (CoefficientField p m) s 0 t * simpleRoot (CoefficientField p m) s 5 t) = _
    rw [map_mul, simpleRoot_twist, simpleRoot_twist]
    exact (simpleRoot_commute (CoefficientField p m) s 5 0 (by decide) (by decide) t t).eq
  · change graphFieldTwist p m (simpleRoot (CoefficientField p m) s 1 t * simpleRoot (CoefficientField p m) s 4 t) = _
    rw [map_mul, simpleRoot_twist, simpleRoot_twist]
    exact (simpleRoot_commute (CoefficientField p m) s 4 1 (by decide) (by decide) t t).eq
  · simp [foldedSplit, foldedSimple, simpleRoot_twist, typeE6DiagramPermutation]
  · simp [foldedSplit, foldedSimple, simpleRoot_twist, typeE6DiagramPermutation]

def foldedFixed (m : ℕ) (s : Bool) (i : Fin 4) (t : FixedField p m) : rationalFixedSubgroup p m :=
  ⟨(foldedSplit p m s i t).val,
    (mem_rationalFixedSubgroup_iff p m _).mpr (foldedSplit_fixed p m s i t)⟩

theorem foldedFixed_add (m : ℕ) (s : Bool) (i : Fin 4) (t u : FixedField p m) :
    foldedFixed p m s i (t + u) = foldedFixed p m s i t * foldedFixed p m s i u :=
  Subtype.ext (congrArg (fun g : rootGeneratedSubgroup p m => g.val) (foldedSplit_add p m s i t u))

@[simp] theorem foldedFixed_zero (m : ℕ) (s : Bool) (i : Fin 4) : foldedFixed p m s i 0 = 1 :=
  Subtype.ext (congrArg (fun g : rootGeneratedSubgroup p m => g.val) (foldedSplit_zero p m s i))

theorem foldedFixed_nsmul (m : ℕ) (s : Bool) (i : Fin 4) (t : FixedField p m)
    (n : ℕ) : foldedFixed p m s i (n • t) = foldedFixed p m s i t ^ n := by
  induction n with
  | zero => simp only [zero_nsmul, foldedFixed_zero, pow_zero]
  | succ n ih => rw [succ_nsmul, foldedFixed_add, ih, pow_succ]

theorem foldedFixed_pow (m : ℕ) (s : Bool) (i : Fin 4) (t : FixedField p m) :
    foldedFixed p m s i t ^ p = 1 := by
  rw [← foldedFixed_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, foldedFixed_zero]

def foldedRoot (m : ℕ) (s : Bool) (i : Fin 4) (t : FixedField p m) : definingCharacteristicSubgroup p m :=
  ⟨foldedFixed p m s i t,
    Subgroup.mem_primePowerGenerated_of_pow (n := 1) (by
      simpa only [pow_one] using foldedFixed_pow p m s i t)⟩

def ambientInclusion (m : ℕ) : definingCharacteristicSubgroup p m →* AmbientGroup p m :=
  (rationalFixedSubgroup p m).subtype.comp (definingCharacteristicSubgroup p m).subtype

theorem ambientInclusion_injective (m : ℕ) : Function.Injective (ambientInclusion p m) :=
  Subtype.val_injective.comp Subtype.val_injective

@[simp] theorem foldedRoot_ambient (m : ℕ) (s : Bool) (i : Fin 4) (t : FixedField p m) :
    ambientInclusion p m (foldedRoot p m s i t) = (foldedSplit p m s i t).val := rfl

theorem foldedRoot_add (m : ℕ) (s : Bool) (i : Fin 4) (t u : FixedField p m) :
    foldedRoot p m s i (t + u) = foldedRoot p m s i t * foldedRoot p m s i u :=
  Subtype.ext (foldedFixed_add p m s i t u)

@[simp] theorem foldedRoot_zero (m : ℕ) (s : Bool) (i : Fin 4) : foldedRoot p m s i 0 = 1 :=
  Subtype.ext (foldedFixed_zero p m s i)

def foldedRootHom (m : ℕ) (s : Bool) (i : Fin 4) :
    Multiplicative (FixedField p m) →* definingCharacteristicSubgroup p m where
  toFun x := foldedRoot p m s i x.toAdd
  map_one' := foldedRoot_zero p m s i
  map_mul' x y := foldedRoot_add p m s i x.toAdd y.toAdd


/-- The folded subgroup over GF(q) is fixed by graph--field twisting after
entrywise inclusion in GF(q²). -/
theorem splitFieldMap_fixed (m : ℕ)
    {g : splitCarrier (GaloisField p (m + 1))}
    (hg : g ∈ splitSubgroup (GaloisField p (m + 1))) :
    graphFieldTwist p m (splitFieldMap (coefficientEmbedding p m) g) =
      splitFieldMap (coefficientEmbedding p m) g := by
  have h : splitSubgroup (GaloisField p (m + 1)) ≤
      ((graphFieldTwist p m).toMonoidHom.comp (splitFieldMap (coefficientEmbedding p m))).eqLocus
        (splitFieldMap (coefficientEmbedding p m)) := by
    rw [splitSubgroup, Subgroup.closure_le]
    rintro _ ⟨⟨s, i, t⟩, rfl⟩
    change graphFieldTwist p m
      (splitFieldMap (coefficientEmbedding p m) (foldedSimple _ s i t)) =
      splitFieldMap (coefficientEmbedding p m) (foldedSimple _ s i t)
    rw [splitFieldMap_foldedSimple]
    exact foldedSplit_fixed p m s i (coefficientEquiv p m t)
  exact h hg

/-- The folded subgroup over the source field in the actual rational fixed group. -/
def fixedEmbedding (m : ℕ) :
    splitSubgroup (GaloisField p (m + 1)) →* rationalFixedSubgroup p m where
  toFun g := ⟨(splitFieldMap (coefficientEmbedding p m) g.val).val,
    (mem_rationalFixedSubgroup_iff p m _).mpr (splitFieldMap_fixed p m g.property)⟩
  map_one' := by
    apply Subtype.ext
    exact congrArg (fun x : splitCarrier (CoefficientField p m) => x.val)
      (map_one (splitFieldMap (coefficientEmbedding p m)))
  map_mul' g h := by
    apply Subtype.ext
    exact congrArg (fun x : splitCarrier (CoefficientField p m) => x.val)
      (map_mul (splitFieldMap (coefficientEmbedding p m)) g.val h.val)

theorem fixedEmbedding_mem_residual (m : ℕ)
    (g : splitSubgroup (GaloisField p (m + 1))) :
    fixedEmbedding p m g ∈ definingCharacteristicSubgroup p m := by
  let f := (splitCarrier (CoefficientField p m)).subtype.comp
    (splitFieldMap (coefficientEmbedding p m))
  let j := ambientInclusion p m
  have h : splitSubgroup (GaloisField p (m + 1)) ≤ j.range.comap f := by
    rw [splitSubgroup, Subgroup.closure_le]
    rintro _ ⟨⟨s, i, t⟩, rfl⟩
    refine ⟨foldedRoot p m s i (coefficientEquiv p m t), ?_⟩
    change (foldedSplit p m s i (coefficientEquiv p m t)).val =
      (splitFieldMap (coefficientEmbedding p m) (foldedSimple _ s i t)).val
    rw [splitFieldMap_foldedSimple]
    rfl
  obtain ⟨x, hx⟩ := h g.property
  have he : x.val = fixedEmbedding p m g := Subtype.ext hx
  exact he ▸ x.property

/-- The actual injective coefficient map into O^{p'} of the graph--field fixed group. -/
def coverEmbedding (m : ℕ) :
    splitSubgroup (GaloisField p (m + 1)) →* definingCharacteristicSubgroup p m :=
  (fixedEmbedding p m).codRestrict _ (fixedEmbedding_mem_residual p m)

theorem coverEmbedding_injective (m : ℕ) : Function.Injective (coverEmbedding p m) := by
  intro g h he
  apply Subtype.ext
  apply splitFieldMap_injective (coefficientEmbedding p m)
  apply Subtype.ext
  exact congrArg (fun x : definingCharacteristicSubgroup p m => x.val.val) he

@[simp] theorem coverEmbedding_ambient (m : ℕ)
    (g : splitSubgroup (GaloisField p (m + 1))) :
    ambientInclusion p m (coverEmbedding p m g) =
      (splitFieldMap (coefficientEmbedding p m) g.val).val := rfl

@[simp] theorem coverEmbedding_foldedSimple (m : ℕ) (s : Bool) (i : Fin 4)
    (t : GaloisField p (m + 1)) :
    coverEmbedding p m ⟨foldedSimple _ s i t, foldedSimple_mem _ s i t⟩ =
      foldedRoot p m s i (coefficientEquiv p m t) := by
  apply ambientInclusion_injective p m
  rw [coverEmbedding_ambient, foldedRoot_ambient, splitFieldMap_foldedSimple]
  rfl

@[simp] theorem coverEmbedding_f4Simple (m : ℕ) (s : Bool) (i : Fin 4)
    (t : GaloisField p (m + 1)) :
    coverEmbedding p m (f4Simple _ s i t) =
      foldedRoot p m s i.rev (coefficientEquiv p m t) :=
  coverEmbedding_foldedSimple p m s i.rev t

/-- The coefficient embedding followed by the model's literal central projection.
Faithfulness and properness of this projected map remain separate obligations. -/
def modelMap (m : ℕ) :
    splitSubgroup (GaloisField p (m + 1)) →* Model p m :=
  (toModel p m).comp (coverEmbedding p m)

@[simp] theorem modelMap_foldedSimple (m : ℕ) (s : Bool) (i : Fin 4)
    (t : GaloisField p (m + 1)) :
    modelMap p m ⟨foldedSimple _ s i t, foldedSimple_mem _ s i t⟩ =
      toModel p m (foldedRoot p m s i (coefficientEquiv p m t)) := by
  change toModel p m (coverEmbedding p m _) = _
  rw [coverEmbedding_foldedSimple]

/-- The remaining faithfulness question is exactly intersection with the
center of the defining-characteristic subgroup, not with the ambient matrix center. -/
@[simp] theorem modelMap_eq_one_iff (m : ℕ)
    (g : splitSubgroup (GaloisField p (m + 1))) :
    modelMap p m g = 1 ↔
      coverEmbedding p m g ∈ Subgroup.center (definingCharacteristicSubgroup p m) :=
  toModel_eq_one p m (coverEmbedding p m g)

end TwistedE6.FoldedSubsystem
