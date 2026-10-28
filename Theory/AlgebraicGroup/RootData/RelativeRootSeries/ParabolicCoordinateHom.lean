module

public import Theory.AlgebraicGroup.RootData.RelativeRootSeries.ParabolicCoordinates

universe u

set_option linter.style.haveILetI false

/-!
The multiplicative coordinate map onto an adjacent positive standard-parabolic
relative-root quotient, indexed by the absolute roots of one exact relative
height.

For downstream arguments, this module exposes the underlying absolute root and
height equation of an exact-height index, and characterizes evaluation of both
the individual root-coordinate homomorphism and their combined coordinate
homomorphism.  The individual formula is the quotient class of the relevant
Chevalley parameter; the combined formula is the finite product of those
classes.  The proofs unfold the constructions local to this module and use the
normality and commutativity of adjacent positive layers established by the
imported relative-root-series API.  Surjectivity comes from exact-height
coordinate generation in `ParabolicCoordinates`; no uniqueness of coordinates
is asserted or used.
-/

namespace Theory.AlgebraicGroup

open scoped IsMulCommutative

variable {k : Type u} [Field k]

/-- Absolute roots whose relative height is exactly `i`.

The subtype representation is intentionally exposed so a public accessor can
eliminate an index and public finite-product statements can synthesize its
finite indexing data.  The coordinate homomorphism implementations remain
unexposed. -/
@[expose] public def StandardParabolicRelativeRootSetup.ExactHeightRoot
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) :=
  {α : S.D.Root // RelativeRootHeight S.coeff S.rationalBase.support
    (S.rootEquiv '' S.J) (S.rootEquiv α) = i}

namespace StandardParabolicRelativeRootSetup.ExactHeightRoot

/-- The absolute root underlying an exact-height index. -/
public def root
    {K : Variety k} [AlgebraicGroup K]
    {S : StandardParabolicRelativeRootSetup K} {i : ℕ}
    (α : S.ExactHeightRoot i) : S.D.Root :=
  α.1

/-- The public root accessor is the underlying subtype value. -/
@[simp] public theorem root_eq_coe
    {K : Variety k} [AlgebraicGroup K]
    {S : StandardParabolicRelativeRootSetup K} {i : ℕ}
    (α : S.ExactHeightRoot i) : α.root = α.1 := by
  rfl

/-- The exact-height index is determined by its underlying absolute root. -/
public theorem root_injective
    {K : Variety k} [AlgebraicGroup K]
    {S : StandardParabolicRelativeRootSetup K} {i : ℕ} :
    Function.Injective (@root k _ K _ S i) := by
  intro α β h
  apply Subtype.ext
  exact h

/-- The defining relative-height equation for an exact-height index. -/
public lemma height_eq
    {K : Variety k} [AlgebraicGroup K]
    {S : StandardParabolicRelativeRootSetup K} {i : ℕ}
    (α : S.ExactHeightRoot i) :
    RelativeRootHeight S.coeff S.rationalBase.support
      (S.rootEquiv '' S.J) (S.rootEquiv α.root) = i :=
  α.2

end StandardParabolicRelativeRootSetup.ExactHeightRoot

/-- The Chevalley one-parameter subgroup for one exact-height root, mapped to
the adjacent relative-root quotient. -/
public noncomputable def standardParabolicRelativeRootLayer_rootCoordinateHom
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (α : S.ExactHeightRoot i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    Multiplicative k →*
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  let N := (S.layer (i + 1)).subgroupOf (S.layer i)
  let rootPoint (t : k) : S.layer i :=
    ⟨S.C.x α.1 t, by
      rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
        RootSubgroupGenerated]
      apply Subgroup.subset_closure
      simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
      refine ⟨α.1, by rw [α.2], ?_⟩
      rw [← (S.chevalleySystem.1 α.1).2]
      exact ⟨t, rfl⟩⟩
  refine
    { toFun := fun t => QuotientGroup.mk' N (rootPoint t.toAdd)
      map_one' := ?_
      map_mul' := ?_ }
  · have hzero : S.C.x α.1 0 = 1 := by
      simpa using (S.chevalleySystem.2.2.2.1 α.1 0 0)
    have hone : rootPoint 0 = 1 := by
      apply Subtype.ext
      exact hzero
    change QuotientGroup.mk' N (rootPoint 0) = 1
    rw [hone, map_one]
  · intro a b
    have hadd : rootPoint (a.toAdd + b.toAdd) =
        rootPoint a.toAdd * rootPoint b.toAdd := by
      apply Subtype.ext
      exact (S.chevalleySystem.2.2.2.1 α.1 a.toAdd b.toAdd).symm
    change QuotientGroup.mk' N (rootPoint (a.toAdd + b.toAdd)) =
      QuotientGroup.mk' N (rootPoint a.toAdd) *
        QuotientGroup.mk' N (rootPoint b.toAdd)
    rw [hadd, map_mul]

/-- Evaluation of one exact-height root coordinate is the quotient class of
the corresponding Chevalley parameter. -/
public lemma standardParabolicRelativeRootLayer_rootCoordinateHom_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (α : S.ExactHeightRoot i) (t : Multiplicative k) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    standardParabolicRelativeRootLayer_rootCoordinateHom S i hi α t =
      QuotientGroup.mk'
        ((S.layer (i + 1)).subgroupOf (S.layer i))
        ⟨S.C.x α.root t.toAdd, by
          rw [StandardParabolicRelativeRootSetup.layer, RelativeRootSeries,
            RootSubgroupGenerated]
          apply Subgroup.subset_closure
          simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
          refine ⟨α.root, by rw [α.height_eq], ?_⟩
          rw [← (S.chevalleySystem.1 α.root).2]
          exact ⟨t.toAdd, rfl⟩⟩ := by
  rfl

/-- Multiply all exact-height Chevalley coordinates in the commutative
adjacent quotient. -/
public noncomputable def standardParabolicRelativeRootLayer_coordinateHom
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    let := hN
    ((α : S.ExactHeightRoot i) → Multiplicative k) →*
      (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i)) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype (S.ExactHeightRoot i) := by
    unfold StandardParabolicRelativeRootSetup.ExactHeightRoot
    infer_instance
  dsimp only
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  let := standardParabolicRelativeRootLayer_quotient_commutative S i hi
  exact (Pi.monoidHomMulEquiv
    (fun _ : S.ExactHeightRoot i => Multiplicative k)
    (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i))).symm
      (fun α => standardParabolicRelativeRootLayer_rootCoordinateHom S i hi α)

/-- The combined exact-height coordinate map evaluates as the finite product
of its individual root-coordinate values. -/
public lemma standardParabolicRelativeRootLayer_coordinateHom_apply
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i)
    (a : (α : S.ExactHeightRoot i) → Multiplicative k) :
    letI : Fintype S.D.Root := Fintype.ofFinite _
    letI : Fintype (S.ExactHeightRoot i) := by
      unfold StandardParabolicRelativeRootSetup.ExactHeightRoot
      infer_instance
    let hN := standardParabolicRelativeRootLayer_next_normal S i hi
    letI := hN
    let hcomm := standardParabolicRelativeRootLayer_quotient_commutative S i hi
    letI := hcomm
    standardParabolicRelativeRootLayer_coordinateHom S i hi a =
      ∏ α : S.ExactHeightRoot i,
        standardParabolicRelativeRootLayer_rootCoordinateHom S i hi α (a α) := by
  dsimp only
  simp [standardParabolicRelativeRootLayer_coordinateHom,
    Pi.monoidHomMulEquiv]

/-- The product of all exact-height Chevalley coordinates surjects onto the
adjacent relative-root quotient.  No uniqueness of coordinates is asserted. -/
public lemma standardParabolicRelativeRootLayer_coordinateHom_surjective
    {K : Variety k} [AlgebraicGroup K]
    (S : StandardParabolicRelativeRootSetup K) (i : ℕ) (hi : 0 < i) :
    Function.Surjective
      (standardParabolicRelativeRootLayer_coordinateHom S i hi) := by
  letI := Fintype.ofFinite S.D.Root
  classical
  letI : Fintype (S.ExactHeightRoot i) := by
    unfold StandardParabolicRelativeRootSetup.ExactHeightRoot
    infer_instance
  let := standardParabolicRelativeRootLayer_next_normal S i hi
  let := standardParabolicRelativeRootLayer_quotient_commutative S i hi
  let f := standardParabolicRelativeRootLayer_coordinateHom S i hi
  have hcoordinate :
      standardParabolicRelativeRootLayer_exactHeightCoordinates S i hi ≤
        f.range := by
    intro q hq
    rw [mem_standardParabolicRelativeRootLayer_exactHeightCoordinates] at hq
    rcases hq with ⟨α, hα, t, rfl⟩
    let a : S.ExactHeightRoot i := ⟨α, hα⟩
    refine ⟨Pi.mulSingle a (Multiplicative.ofAdd t), ?_⟩
    change
      ((Pi.monoidHomMulEquiv
        (fun _ : S.ExactHeightRoot i => Multiplicative k)
        (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i))).symm
          (fun β =>
            standardParabolicRelativeRootLayer_rootCoordinateHom S i hi β))
        (Pi.mulSingle a (Multiplicative.ofAdd t)) =
      QuotientGroup.mk'
        ((S.layer (i + 1)).subgroupOf (S.layer i))
        ⟨S.C.x α t, _⟩
    have ha := congrArg
      (fun g => g a)
      ((Pi.monoidHomMulEquiv
        (fun _ : S.ExactHeightRoot i => Multiplicative k)
        (S.layer i ⧸ (S.layer (i + 1)).subgroupOf (S.layer i))).apply_symm_apply
          (fun β =>
            standardParabolicRelativeRootLayer_rootCoordinateHom S i hi β))
    exact DFunLike.congr_fun ha (Multiplicative.ofAdd t)
  have hclosure : Subgroup.closure
      (standardParabolicRelativeRootLayer_exactHeightCoordinates S i hi) ≤
      f.range := by
    rw [Subgroup.closure_le]
    exact hcoordinate
  have hrange : f.range = ⊤ := by
    apply top_unique
    rw [← standardParabolicRelativeRootLayer_exactHeightCoordinates_closure_eq_top
      S i hi]
    exact hclosure
  exact MonoidHom.range_eq_top.mp hrange

end Theory.AlgebraicGroup
