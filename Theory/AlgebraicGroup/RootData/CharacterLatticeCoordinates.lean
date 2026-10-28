module

public import Theory.AlgebraicGroup.RootData.FiniteReflectionSeed
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.Data.Real.Basic

/-!
# Character-lattice reflection coordinates

This module packages integral character--coroot reflection data and its canonical real
coordinates.  The integral pairing is the evaluation pairing on a finite free lattice.  A
finite basis and its dual identify the lattice with `Fin (Module.finrank ℤ L) → ℝ`; the resulting
dot-product pairing has the same Cartan integers and reflection permutations.  Roots are not
assumed to generate the lattice over `ℤ`; the real root and coroot spanning hypotheses are
therefore supplied separately in `RealCoordinateHypotheses`.  The latter also carries the
reducedness condition needed by `FiniteReflectionSeed`.

The construction is purely linear algebra and is intended as the coordinate adapter for later
root-system and torus-root-system identifications.  Composing it with `FiniteReflectionSeed`
produces a based realization whose partial addition is characterized both in real coordinates
and in the original character lattice.
-/

@[expose] public section

noncomputable section

open Function Set Submodule

namespace Theory.AlgebraicGroup

universe u v

/-- Integral reflection data on a finite free character lattice. -/
public structure CharacterLatticeReflectionData
    (ι : Type u) (L : Type v)
    [Finite ι]
    [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L] where
  root : ι ↪ L
  coroot : ι ↪ Module.Dual ℤ L
  reflectionPerm : ι → (ι ≃ ι)
  root_coroot_two (i : ι) : coroot i (root i) = 2
  reflection_root (i j : ι) :
    root j - (coroot i (root j)) • root i = root (reflectionPerm i j)
  reflection_coroot (i j : ι) :
    coroot j - (coroot j (root i)) • coroot i = coroot (reflectionPerm i j)

namespace CharacterLatticeReflectionData

variable {ι : Type u} {L : Type v}
  [Finite ι]
  [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L]
  (S : CharacterLatticeReflectionData ι L)

local instance : Fintype ι := Fintype.ofFinite ι

/-- The rank used by the real coordinate adapter. -/
public abbrev rank (_S : CharacterLatticeReflectionData ι L) : ℕ := Module.finrank ℤ L

/-- Coordinates of a lattice root in the real vector space attached to a finite basis. -/
public noncomputable def rootCoordinates (i : ι) : Fin (rank S) → ℝ :=
  fun a => Int.cast ((Module.finBasis ℤ L).equivFun (S.root i) a)

/-- Coordinates of a lattice coroot in the dual real coordinate space. -/
public noncomputable def corootCoordinates (i : ι) : Fin (rank S) → ℝ :=
  fun a => Int.cast ((Module.finBasis ℤ L).dualBasis.equivFun (S.coroot i) a)

public lemma rootCoordinates_injective : Function.Injective (rootCoordinates S) := by
  intro i j hij
  apply S.root.injective
  apply (Module.finBasis ℤ L).equivFun.injective
  funext a
  exact Int.cast_injective (congrFun hij a)

public lemma corootCoordinates_injective : Function.Injective (corootCoordinates S) := by
  intro i j hij
  apply S.coroot.injective
  apply (Module.finBasis ℤ L).dualBasis.equivFun.injective
  funext a
  exact Int.cast_injective (congrFun hij a)

public lemma rootCoordinates_sub_smul (i j : ι) :
    rootCoordinates S (S.reflectionPerm i j) =
      rootCoordinates S j - (S.coroot i (S.root j) : ℝ) • rootCoordinates S i := by
  ext a
  change (((Module.finBasis ℤ L).equivFun (S.root (S.reflectionPerm i j)) a : ℤ) : ℝ) = _
  rw [← S.reflection_root i j]
  simp [rootCoordinates, map_zsmul, sub_eq_add_neg, smul_eq_mul]

public lemma corootCoordinates_sub_smul (i j : ι) :
    corootCoordinates S (S.reflectionPerm i j) =
      corootCoordinates S j - (S.coroot j (S.root i) : ℝ) • corootCoordinates S i := by
  ext a
  change (((Module.finBasis ℤ L).dualBasis.equivFun
    (S.coroot (S.reflectionPerm i j)) a : ℤ) : ℝ) = _
  rw [← S.reflection_coroot i j]
  simp [corootCoordinates, sub_eq_add_neg, smul_eq_mul]

public lemma dotProduct_coordinates (i j : ι) :
    dotProduct (rootCoordinates S i) (corootCoordinates S j) =
      Int.cast (S.coroot j (S.root i)) := by
  have hInt : (S.coroot j) (S.root i) =
      ∑ a, (Module.finBasis ℤ L).repr (S.root i) a *
        (S.coroot j) ((Module.finBasis ℤ L) a) := by
    have hsum := congrArg (S.coroot j) ((Module.finBasis ℤ L).sum_repr (S.root i))
    rw [map_sum] at hsum
    simpa [map_smul, smul_eq_mul] using hsum.symm
  simp only [rootCoordinates, corootCoordinates, Module.Basis.equivFun_apply,
    dotProduct, Module.Basis.dualBasis_repr]
  norm_cast
  rw [hInt]

/-- The evaluation pairing on the character lattice and its dual. -/
public noncomputable def integralPairing {ι : Type u} {L : Type v}
    [Finite ι] [AddCommGroup L] [Module ℤ L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (S : CharacterLatticeReflectionData ι L) :
    RootPairing ι ℤ L (Module.Dual ℤ L) := by
  letI : (Module.Dual.eval ℤ L).IsPerfPair := inferInstance
  exact
    { toLinearMap := Module.Dual.eval ℤ L
      root := S.root
      coroot := S.coroot
      root_coroot_two := by
        intro i
        exact S.root_coroot_two i
      reflectionPerm := S.reflectionPerm
      reflectionPerm_root := by
        intro i j
        rw [Module.Dual.eval_apply]
        change S.root j - @SMul.smul ℤ L
          (DistribMulAction.toDistribSMul.toSMul)
          (S.coroot i (S.root j)) (S.root i) = _
        rw [show @SMul.smul ℤ L (DistribMulAction.toDistribSMul.toSMul)
          (S.coroot i (S.root j)) (S.root i) =
            (S.coroot i (S.root j)) • S.root i from
          (Int.cast_smul_eq_zsmul ℤ (S.coroot i (S.root j)) (S.root i))]
        exact S.reflection_root i j
      reflectionPerm_coroot := by
        intro i j
        rw [Module.Dual.eval_apply]
        change S.coroot j - @SMul.smul ℤ (Module.Dual ℤ L)
          (DistribMulAction.toDistribSMul.toSMul)
          (S.coroot j (S.root i)) (S.coroot i) = _
        rw [show @SMul.smul ℤ (Module.Dual ℤ L)
          (DistribMulAction.toDistribSMul.toSMul)
          (S.coroot j (S.root i)) (S.coroot i) =
            (S.coroot j (S.root i)) • S.coroot i from
          (Int.cast_smul_eq_zsmul ℤ
            (S.coroot j (S.root i)) (S.coroot i))]
        exact S.reflection_coroot i j }

@[simp] public lemma integralPairing_root (i : ι) :
    (S.integralPairing).root i = S.root i := by
  change S.root i = S.root i
  rfl

@[simp] public lemma integralPairing_coroot (i : ι) :
    (S.integralPairing).coroot i = S.coroot i := by
  change S.coroot i = S.coroot i
  rfl

@[simp] public lemma integralPairing_pairing (i j : ι) :
    (S.integralPairing).pairing i j = S.coroot j (S.root i) := by
  change (Module.Dual.eval ℤ L) (S.root i) (S.coroot j) = _
  rw [Module.Dual.eval_apply]

/-- The standard dot-product pairing on the finite real coordinate space. -/
public noncomputable def coordinatePairing :
    (Fin (rank S) → ℝ) →ₗ[ℝ] (Fin (rank S) → ℝ) →ₗ[ℝ] ℝ :=
  (dotProductEquiv ℝ (Fin (rank S))).toLinearMap

public instance coordinatePairing_isPerfPair : (S.coordinatePairing).IsPerfPair where
  bijective_left := (dotProductEquiv ℝ (Fin (rank S))).bijective
  bijective_right := by
    let e := dotProductEquiv ℝ (Fin (rank S))
    have hflip : (S.coordinatePairing).flip = e.toLinearMap := by
      ext x y
      simp [coordinatePairing, e, dotProduct_comm]
    rw [hflip]
    exact e.bijective

public lemma coordinatePairing_apply (x y : Fin (rank S) → ℝ) :
    S.coordinatePairing x y = dotProduct x y := by
  simp [coordinatePairing, dotProductEquiv]

/-- The real root pairing carried by the lattice coordinates. -/
public noncomputable def realCoordinateRootPairing :
    RootPairing ι ℝ (Fin (rank S) → ℝ) (Fin (rank S) → ℝ) := by
  letI : (S.coordinatePairing).IsPerfPair := inferInstance
  exact
    { toLinearMap := S.coordinatePairing
      root := ⟨rootCoordinates S, rootCoordinates_injective S⟩
      coroot := ⟨corootCoordinates S, corootCoordinates_injective S⟩
      root_coroot_two := by
        intro i
        change S.coordinatePairing (rootCoordinates S i) (corootCoordinates S i) = 2
        rw [coordinatePairing_apply, dotProduct_coordinates]
        norm_num [S.root_coroot_two]
      reflectionPerm := S.reflectionPerm
      reflectionPerm_root := by
        intro i j
        change rootCoordinates S j -
          S.coordinatePairing (rootCoordinates S j) (corootCoordinates S i) •
            rootCoordinates S i = rootCoordinates S (S.reflectionPerm i j)
        rw [coordinatePairing_apply]
        rw [dotProduct_coordinates]
        exact (rootCoordinates_sub_smul S i j).symm
      reflectionPerm_coroot := by
        intro i j
        change corootCoordinates S j -
          S.coordinatePairing (rootCoordinates S i) (corootCoordinates S j) •
            corootCoordinates S i = corootCoordinates S (S.reflectionPerm i j)
        rw [coordinatePairing_apply]
        rw [dotProduct_coordinates]
        exact (corootCoordinates_sub_smul S i j).symm }

@[simp] public lemma realCoordinateRootPairing_root (i : ι) :
    S.realCoordinateRootPairing.root i = rootCoordinates S i := by
  rfl

@[simp] public lemma realCoordinateRootPairing_coroot (i : ι) :
    S.realCoordinateRootPairing.coroot i = corootCoordinates S i := by
  rfl

@[simp] public lemma realCoordinateRootPairing_pairing (i j : ι) :
    S.realCoordinateRootPairing.pairing i j =
      (S.coroot j (S.root i) : ℝ) := by
  change S.coordinatePairing (rootCoordinates S i) (corootCoordinates S j) = _
  rw [coordinatePairing_apply, dotProduct_coordinates]

@[simp] public lemma realCoordinateRootPairing_reflectionPerm (i j : ι) :
    S.realCoordinateRootPairing.reflectionPerm i j = S.reflectionPerm i j := rfl

/-- Spanning and reducedness hypotheses for the real coordinate adapter. -/
public structure RealCoordinateHypotheses where
  span_root : span ℝ (range (rootCoordinates S)) = ⊤
  span_coroot : span ℝ (range (corootCoordinates S)) = ⊤
  reduced_scalar_multiple (i j : ι)
      (h : ¬ LinearIndependent ℝ ![rootCoordinates S i, rootCoordinates S j]) :
    rootCoordinates S i = rootCoordinates S j ∨
      rootCoordinates S i = -rootCoordinates S j

public theorem realCoordinateIsRootSystem (H : S.RealCoordinateHypotheses) :
    S.realCoordinateRootPairing.IsRootSystem where
  span_root_eq_top := by
    change span ℝ (range (rootCoordinates S)) = ⊤
    exact H.span_root
  span_coroot_eq_top := by
    change span ℝ (range (corootCoordinates S)) = ⊤
    exact H.span_coroot

public theorem realCoordinateIsCrystallographic :
    S.realCoordinateRootPairing.IsCrystallographic where
  exists_value i j := ⟨S.coroot j (S.root i), by
    rw [realCoordinateRootPairing_pairing]
    norm_num⟩

public theorem realCoordinateIsReduced (H : S.RealCoordinateHypotheses) :
    S.realCoordinateRootPairing.IsReduced where
  eq_or_eq_neg := by
    intro i j h
    simpa only [realCoordinateRootPairing_root] using H.reduced_scalar_multiple i j h

/-- Convert the lattice reflection data and real hypotheses to a `FiniteReflectionSeed`. -/
public noncomputable def toFiniteReflectionSeed (H : S.RealCoordinateHypotheses) :
    FiniteReflectionSeed ι ℝ (Fin (rank S) → ℝ) (Fin (rank S) → ℝ) where
  pairing := S.coordinatePairing
  pairing_isPerfPair := inferInstance
  root := ⟨rootCoordinates S, rootCoordinates_injective S⟩
  coroot := ⟨corootCoordinates S, corootCoordinates_injective S⟩
  cartan := fun i j => S.coroot j (S.root i)
  pairing_eq_cartan := by
    intro i j
    change S.coordinatePairing (rootCoordinates S i) (corootCoordinates S j) = _
    rw [coordinatePairing_apply, dotProduct_coordinates]
  cartan_self := by
    intro i
    exact S.root_coroot_two i
  reflectionPerm := S.reflectionPerm
  reflection_root := by
    intro i j
    exact (rootCoordinates_sub_smul S i j).symm
  reflection_coroot := by
    intro i j
    exact (corootCoordinates_sub_smul S i j).symm
  span_root := H.span_root
  span_coroot := H.span_coroot
  reduced_scalar_multiple := H.reduced_scalar_multiple

@[simp] public lemma toFiniteReflectionSeed_pairing (H : S.RealCoordinateHypotheses)
    (i j : ι) :
    (S.toFiniteReflectionSeed H).pairing (rootCoordinates S i) (corootCoordinates S j) =
      (S.coroot j (S.root i) : ℝ) := by
  change S.coordinatePairing (rootCoordinates S i) (corootCoordinates S j) = _
  rw [coordinatePairing_apply, dotProduct_coordinates]

/-- The reflection-index negation in real coordinates. -/
public def neg (i : ι) : ι := S.reflectionPerm i i

@[simp] public lemma root_neg (i : ι) :
    rootCoordinates S (S.neg i) = -rootCoordinates S i := by
  simpa [neg, S.root_coroot_two, two_smul] using (S.rootCoordinates_sub_smul i i)

@[simp] public lemma coroot_neg (i : ι) :
    corootCoordinates S (S.neg i) = -corootCoordinates S i := by
  simpa [neg, S.root_coroot_two, two_smul] using (S.corootCoordinates_sub_smul i i)

/-- Partial addition of roots, defined exactly when the coordinate sum is a root. -/
public noncomputable def add (i j : ι) : Option ι := by
  classical
  exact if h : ∃ k, rootCoordinates S k = rootCoordinates S i + rootCoordinates S j then
    some h.choose else none

public lemma add_eq_some_iff {i j k : ι} :
    S.add i j = some k ↔
      rootCoordinates S k = rootCoordinates S i + rootCoordinates S j := by
  classical
  simp only [add]
  split_ifs with h
  · constructor
    · intro hEq
      cases Option.some.inj hEq
      exact h.choose_spec
    · intro hk
      apply congrArg some
      exact S.rootCoordinates_injective (h.choose_spec.trans hk.symm)
  · constructor
    · intro hEq
      cases hEq
    · intro hk
      exact (h ⟨k, hk⟩).elim

public lemma rootCoordinates_eq_add_iff (i j k : ι) :
    rootCoordinates S k = rootCoordinates S i + rootCoordinates S j ↔
      S.root k = S.root i + S.root j := by
  constructor
  · intro h
    apply (Module.finBasis ℤ L).equivFun.injective
    funext a
    have ha := congrFun h a
    exact Int.cast_injective (by simpa [rootCoordinates, map_add] using ha)
  · intro h
    ext a
    change (((Module.finBasis ℤ L).equivFun (S.root k) a : ℤ) : ℝ) = _
    rw [h, map_add]
    simp [rootCoordinates]

/-- The complete based real realization obtained from integral reflection data.

This is the principal composite construction: the coordinate adapter supplies a finite reduced
crystallographic root system in the exact real coordinate space used downstream, while
`FiniteReflectionSeed.realization` supplies its base, negation, partial addition, positive and
simple roots, and integral height. -/
public noncomputable def finiteRealization (H : S.RealCoordinateHypotheses) :
    (S.toFiniteReflectionSeed H).Realization :=
  (S.toFiniteReflectionSeed H).realization

@[simp] public lemma finiteRealization_pairing (H : S.RealCoordinateHypotheses) (i j : ι) :
    (S.finiteRealization H).pairing i j = S.coroot j (S.root i) := rfl

@[simp] public lemma finiteRealization_reflect (H : S.RealCoordinateHypotheses) (i j : ι) :
    (S.finiteRealization H).reflect i j = S.reflectionPerm i j := rfl

@[simp] public lemma finiteRealization_neg (H : S.RealCoordinateHypotheses) (i : ι) :
    (S.finiteRealization H).neg i = S.reflectionPerm i i := rfl

public lemma finiteRealization_add_eq_some_iff (H : S.RealCoordinateHypotheses) (i j k : ι) :
    (S.finiteRealization H).add i j = some k ↔ S.root k = S.root i + S.root j := by
  rw [(S.finiteRealization H).root_add_iff]
  exact S.rootCoordinates_eq_add_iff i j k

@[simp] public lemma finiteRealization_simple (H : S.RealCoordinateHypotheses) :
    (S.finiteRealization H).simple = (S.finiteRealization H).base.support := rfl

@[simp] public lemma finiteRealization_height (H : S.RealCoordinateHypotheses) (i : ι) :
    (S.finiteRealization H).height i = (S.finiteRealization H).base.height i := rfl

end CharacterLatticeReflectionData

end Theory.AlgebraicGroup
