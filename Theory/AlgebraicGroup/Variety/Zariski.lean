module

public import Mathlib.Topology.Constructions
public import Theory.AlgebraicGroup.Variety.Morphism

universe u

/-!
The Zariski topology on rational points of presented affine varieties.
-/

namespace Theory.AlgebraicGroup

open scoped TensorProduct

open LinearMap Submodule

variable {k : Type u} [Field k]

/-- Zariski-closed subsets of a presented variety. -/
@[expose]
public def IsZariskiClosed (V : Variety k) (S : Set (Variety.Point V)) : Prop :=
  ∃ equations : Set (MvPolynomial V.Coordinates k),
    S = {x | ∀ p ∈ equations, evalPolynomial x.val p = 0}

/-- Zariski-open subsets are complements of Zariski-closed subsets. -/
public def IsZariskiOpen (V : Variety k) (S : Set (Variety.Point V)) : Prop :=
  IsZariskiClosed V Sᶜ

/-- The defining complement characterization of a Zariski-open subset. -/
public theorem isZariskiOpen_iff {V : Variety k} {S : Set (Variety.Point V)} :
    IsZariskiOpen V S ↔ IsZariskiClosed V Sᶜ := Iff.rfl

/-- A subset is Zariski dense if every closed subset containing it is the whole
variety. -/
public def IsZariskiDense (V : Variety k) (S : Set (Variety.Point V)) : Prop :=
  ∀ Z : Set (Variety.Point V), IsZariskiClosed V Z → S ⊆ Z → Z = Set.univ

/-- A chosen family of equations cutting out a Zariski-closed subset. -/
public abbrev Variety.closedEquations {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S) :
    Set (MvPolynomial V.Coordinates k) :=
  Classical.choose hS

/-- The chosen equations cut out the given closed subset. -/
public theorem Variety.closedEquations_spec {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S) :
    S = {x | ∀ p ∈ Variety.closedEquations hS, evalPolynomial x.val p = 0} :=
  Classical.choose_spec hS

/-- A Zariski-closed subset, presented as a zero locus in the same ambient
affine space. -/
public abbrev Variety.closedSubvariety {V : Variety k} {S : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) : Variety k where
  Coordinates := V.Coordinates
  finiteCoordinates := V.finiteCoordinates
  equations := V.equations ∪ Variety.closedEquations hS

/-- The points of a closed subvariety are exactly the ambient points belonging
to the closed subset. -/
@[expose]
public def Variety.closedSubvarietyPointEquiv {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S) :
    Variety.Point (Variety.closedSubvariety hS) ≃ {x : Variety.Point V // x ∈ S} where
  toFun := fun x ↦ by
    let y : Variety.Point V :=
      ⟨x.val, fun p hp ↦ x.isZero p (Set.mem_union_left _ hp)⟩
    refine ⟨y, ?_⟩
    rw [Variety.closedEquations_spec hS]
    change ∀ p ∈ Variety.closedEquations hS, evalPolynomial x.val p = 0
    intro p hp
    exact x.isZero p (Set.mem_union_right _ hp)
  invFun := fun x ↦ by
    let y : Variety.Point V := x.val
    have hy : y ∈ S := x.property
    rw [Variety.closedEquations_spec hS] at hy
    exact
      ⟨y.val, by
      intro p hp
      rcases hp with hp | hp
      · exact y.isZero p hp
      · exact hy p hp⟩
  left_inv := by
    intro x
    apply Variety.Point.ext
    rfl
  right_inv := by
    intro x
    apply Subtype.ext
    apply Variety.Point.ext
    rfl

/-- Rational points are Zariski closed. -/
public theorem isZariskiClosed_singleton (V : Variety k) (x : Variety.Point V) :
    IsZariskiClosed V ({x} : Set (Variety.Point V)) := by
  refine ⟨Set.range (fun i : V.Coordinates ↦
    MvPolynomial.X i - MvPolynomial.C (x.val i)), ?_⟩
  ext y
  constructor
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    intro p hp
    rcases hp with ⟨i, rfl⟩
    simp [evalPolynomial]
  · intro hy
    rw [Set.mem_singleton_iff]
    apply Variety.Point.ext
    funext i
    have h := hy (MvPolynomial.X i - MvPolynomial.C (x.val i)) ⟨i, rfl⟩
    exact sub_eq_zero.mp (by simpa [evalPolynomial] using h)

/-- Arbitrary intersections of Zariski-closed subsets are Zariski closed. -/
public theorem isZariskiClosed_iInter {V : Variety k} {ι : Type*}
    (S : ι → Set (Variety.Point V)) (hS : ∀ i, IsZariskiClosed V (S i)) :
    IsZariskiClosed V (⋂ i, S i) := by
  refine ⟨⋃ i, Variety.closedEquations (hS i), ?_⟩
  ext x
  constructor
  · intro hx p hp
    rw [Set.mem_iInter] at hx
    rcases Set.mem_iUnion.mp hp with ⟨i, hp⟩
    have hxi := hx i
    rw [Variety.closedEquations_spec (hS i)] at hxi
    exact hxi p hp
  · intro hx
    rw [Set.mem_iInter]
    intro i
    rw [Variety.closedEquations_spec (hS i)]
    intro p hp
    exact hx p (Set.mem_iUnion.mpr ⟨i, hp⟩)

/-- Binary intersections of Zariski-closed subsets are Zariski closed. -/
public theorem isZariskiClosed_inter {V : Variety k}
    {S T : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) (hT : IsZariskiClosed V T) :
    IsZariskiClosed V (S ∩ T) := by
  refine ⟨Variety.closedEquations hS ∪ Variety.closedEquations hT, ?_⟩
  ext x
  constructor
  · intro hx p hp
    rcases hp with hp | hp
    · have hxS := hx.1
      rw [Variety.closedEquations_spec hS] at hxS
      exact hxS p hp
    · have hxT := hx.2
      rw [Variety.closedEquations_spec hT] at hxT
      exact hxT p hp
  · intro hx
    constructor
    · rw [Variety.closedEquations_spec hS]
      intro p hp
      exact hx p (Set.mem_union_left _ hp)
    · rw [Variety.closedEquations_spec hT]
      intro p hp
      exact hx p (Set.mem_union_right _ hp)

/-- The equalizer of two polynomial morphisms is Zariski closed. -/
public theorem Variety.Morphism.isZariskiClosed_equalizer {V W : Variety k}
    (f g : Variety.Morphism V W) :
    IsZariskiClosed V {x | f.toFun x = g.toFun x} := by
  let fp : W.Coordinates → MvPolynomial V.Coordinates k :=
    fun i ↦ Classical.choose (f.regular i)
  let gp : W.Coordinates → MvPolynomial V.Coordinates k :=
    fun i ↦ Classical.choose (g.regular i)
  refine ⟨Set.range (fun i ↦ fp i - gp i), ?_⟩
  ext x
  constructor
  · intro hx p hp
    rcases hp with ⟨i, rfl⟩
    have hcoordinate := congrArg (fun y : Variety.Point W ↦ y.val i) hx
    have heq : evalPolynomial x.val (fp i) = evalPolynomial x.val (gp i) := by
      calc
        evalPolynomial x.val (fp i) = (f.toFun x).val i := by
          simpa [fp] using (Classical.choose_spec (f.regular i) x).symm
        _ = (g.toFun x).val i := hcoordinate
        _ = evalPolynomial x.val (gp i) := by
          simpa [gp] using Classical.choose_spec (g.regular i) x
    simpa [evalPolynomial] using sub_eq_zero.mpr heq
  · intro hx
    apply Variety.Point.ext
    funext i
    have hzero := hx (fp i - gp i) ⟨i, rfl⟩
    have heq : evalPolynomial x.val (fp i) = evalPolynomial x.val (gp i) := by
      exact sub_eq_zero.mp (by simpa [evalPolynomial] using hzero)
    calc
      (f.toFun x).val i = evalPolynomial x.val (fp i) := by
        simpa [fp] using Classical.choose_spec (f.regular i) x
      _ = evalPolynomial x.val (gp i) := heq
      _ = (g.toFun x).val i := by
        simpa [gp] using (Classical.choose_spec (g.regular i) x).symm

private def polynomialProductSet {σ : Type*} (E F : Set (MvPolynomial σ k)) :
    Set (MvPolynomial σ k) :=
  {p | ∃ q ∈ E, ∃ r ∈ F, p = q * r}

private lemma zero_of_polynomialProductSet
    {V : Variety k} {E F : Set (MvPolynomial V.Coordinates k)}
    {x : Variety.Point V}
    (h : ∀ p ∈ polynomialProductSet E F,
      evalPolynomial x.val p = 0) :
    (∀ q ∈ E, evalPolynomial x.val q = 0) ∨
      (∀ r ∈ F, evalPolynomial x.val r = 0) := by
  classical
  by_cases hE : ∀ q ∈ E, evalPolynomial x.val q = 0
  · exact Or.inl hE
  · by_cases hF : ∀ r ∈ F, evalPolynomial x.val r = 0
    · exact Or.inr hF
    · push Not at hE hF
      rcases hE with ⟨q, hq, hq0⟩
      rcases hF with ⟨r, hr, hr0⟩
      have hp := h (q * r) ⟨q, hq, r, hr, rfl⟩
      have hmul : evalPolynomial x.val (q * r) =
          evalPolynomial x.val q * evalPolynomial x.val r :=
        evalPolynomial_mul x.val q r
      have hprod0 : evalPolynomial x.val q * evalPolynomial x.val r = 0 := by
        simpa [hmul] using hp
      exact False.elim ((mul_ne_zero hq0 hr0) hprod0)

public theorem isZariskiClosed_union {V : Variety k}
    {S T : Set (Variety.Point V)}
    (hS : IsZariskiClosed V S) (hT : IsZariskiClosed V T) :
    IsZariskiClosed V (S ∪ T) := by
  rcases hS with ⟨E, hE⟩
  rcases hT with ⟨F, hF⟩
  refine ⟨polynomialProductSet E F, ?_⟩
  rw [hE, hF]
  ext x
  constructor
  · intro hx p hp
    rcases hx with hxE | hxF
    · rcases hp with ⟨q, hq, r, hr, rfl⟩
      rw [evalPolynomial_mul, hxE q hq, zero_mul]
    · rcases hp with ⟨q, hq, r, hr, rfl⟩
      rw [evalPolynomial_mul, hxF r hr, mul_zero]
  · intro hx
    change (∀ p ∈ polynomialProductSet E F, evalPolynomial x.val p = 0) at hx
    change (∀ q ∈ E, evalPolynomial x.val q = 0) ∨
      (∀ r ∈ F, evalPolynomial x.val r = 0)
    exact zero_of_polynomialProductSet hx

public theorem isZariskiClosed_of_finite {V : Variety k}
    {S : Set (Variety.Point V)} (hS : S.Finite) :
    IsZariskiClosed V S := by
  refine Set.Finite.induction_on
    (motive := fun T _ ↦ IsZariskiClosed V T) S hS ?_ ?_
  · refine ⟨{MvPolynomial.C 1}, ?_⟩
    ext x
    constructor
    · intro hx
      simp at hx
    · intro hx
      have hone := hx (MvPolynomial.C 1) (Set.mem_singleton _)
      have hzero : (1 : k) = 0 := by
        calc
          1 = evalPolynomial x.val (MvPolynomial.C 1) := by
            simp [evalPolynomial]
          _ = 0 := hone
      exact one_ne_zero hzero
  · intro x T hx hT ih
    change IsZariskiClosed V ({x} ∪ T)
    exact isZariskiClosed_union (isZariskiClosed_singleton V x) ih

/-- The Zariski topology determined by the polynomial zero loci in a presented
variety. -/
@[expose, reducible]
public def Variety.zariskiTopology (V : Variety k) :
    TopologicalSpace (Variety.Point V) :=
  TopologicalSpace.ofClosed
    {S | IsZariskiClosed V S}
    (isZariskiClosed_of_finite Set.finite_empty)
    (by
      intro A hA
      rw [Set.sInter_eq_iInter]
      exact isZariskiClosed_iInter (fun S : A ↦ S.val)
        (fun S ↦ hA S.property))
    (by
      intro S hS T hT
      exact isZariskiClosed_union hS hT)

@[reducible]
public instance Variety.pointTopologicalSpace (V : Variety k) :
    TopologicalSpace (Variety.Point V) := V.zariskiTopology

public theorem Variety.isClosed_iff_isZariskiClosed {V : Variety k}
    {S : Set (Variety.Point V)} :
    IsClosed S ↔ IsZariskiClosed V S := by
  constructor
  · intro hS
    have hopen : IsOpen Sᶜ := hS.isOpen_compl
    change IsZariskiClosed V Sᶜᶜ at hopen
    simpa using hopen
  · intro hS
    constructor
    change IsZariskiClosed V Sᶜᶜ
    simpa using hS

/-- The inverse image of a Zariski-closed set under a polynomial morphism is
Zariski closed. -/
public theorem Variety.Morphism.isZariskiClosed_preimage {V W : Variety k}
    (f : Variety.Morphism V W) {S : Set (Variety.Point W)}
    (hS : IsZariskiClosed W S) :
    IsZariskiClosed V (f.toFun ⁻¹' S) := by
  rcases hS with ⟨equations, rfl⟩
  let coordinatePolynomial : W.Coordinates →
      MvPolynomial V.Coordinates k :=
    fun i ↦ Classical.choose (f.regular i)
  refine ⟨MvPolynomial.bind₁ coordinatePolynomial '' equations, ?_⟩
  ext x
  constructor
  · intro hx p hp
    rcases hp with ⟨q, hq, rfl⟩
    have hzero := hx q hq
    rw [evalPolynomial_bind₁]
    have hcoordinate :
        (fun i ↦ evalPolynomial x.val (coordinatePolynomial i)) =
          (f.toFun x).val := by
      funext i
      exact (Classical.choose_spec (f.regular i) x).symm
    rw [hcoordinate]
    exact hzero
  · intro hx q hq
    have hzero := hx (MvPolynomial.bind₁ coordinatePolynomial q) ⟨q, hq, rfl⟩
    rw [evalPolynomial_bind₁] at hzero
    have hcoordinate :
        (fun i ↦ evalPolynomial x.val (coordinatePolynomial i)) =
          (f.toFun x).val := by
      funext i
      exact (Classical.choose_spec (f.regular i) x).symm
    rw [← hcoordinate]
    exact hzero

public theorem Variety.Morphism.continuous {V W : Variety k}
    (f : Variety.Morphism V W) : Continuous f.toFun := by
  rw [continuous_iff_isClosed]
  intro S hS
  rw [Variety.isClosed_iff_isZariskiClosed] at hS ⊢
  exact f.isZariskiClosed_preimage hS

variable {k : Type u} [Field k]

/-- A Zariski-closed subset of a closed subvariety remains closed after its
canonical inclusion into the ambient variety. -/
public theorem closedSubvariety_image_isZariskiClosed {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S)
    {T : Set (Variety.Point (Variety.closedSubvariety hS))}
    (hT : IsZariskiClosed (Variety.closedSubvariety hS) T) :
    IsZariskiClosed V ((fun y : Variety.Point (Variety.closedSubvariety hS) =>
      (Variety.closedSubvarietyPointEquiv hS y).1) '' T) := by
  let W : Variety k := Variety.closedSubvariety hS
  let e : Variety.Point W → Variety.Point V := fun y =>
    (Variety.closedSubvarietyPointEquiv hS y).1
  rcases hT with ⟨E, hE⟩
  let Z : Set (Variety.Point V) := {x | ∀ p ∈ E, evalPolynomial x.val p = 0}
  have hZz : IsZariskiClosed V Z := ⟨E, rfl⟩
  have hEq : e '' T = S ∩ Z := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyT, hy⟩
      have hyE : ∀ p ∈ E, evalPolynomial y.val p = 0 := by
        rw [hE] at hyT
        exact hyT
      constructor
      · rw [← hy]
        exact (Variety.closedSubvarietyPointEquiv hS y).2
      · intro p hp
        rw [← hy]
        have hyx : (Variety.closedSubvarietyPointEquiv hS y).1.val = y.val := by rfl
        simpa [e, hyx] using hyE p hp
    · intro hx
      rcases hx with ⟨hxS, hxZ⟩
      let y : Variety.Point W :=
        (Variety.closedSubvarietyPointEquiv hS).symm ⟨x, hxS⟩
      refine ⟨y, ?_, ?_⟩
      · rw [hE]
        change ∀ p ∈ E, evalPolynomial y.val p = 0
        intro p hp
        have hyx : y.val = x.val := by rfl
        simpa [y, hyx] using hxZ p hp
      · simp [e, y]
  rw [hEq]
  exact isZariskiClosed_inter hS hZz

/-- The point space of a closed subvariety is canonically homeomorphic to the
corresponding closed subset of the ambient point space. -/
@[expose]
public noncomputable def Variety.closedSubvarietyPointHomeomorph {V : Variety k}
    {S : Set (Variety.Point V)} (hS : IsZariskiClosed V S) :
    Variety.Point (Variety.closedSubvariety hS) ≃ₜ
      {x : Variety.Point V // x ∈ S} := by
  let W := Variety.closedSubvariety hS
  let e := Variety.closedSubvarietyPointEquiv hS
  let inc : Variety.Morphism W V :=
    { toFun := fun y => (e y).1
      regular := fun i => ⟨MvPolynomial.X i, fun y => by
        have hyv : (e y).1.val = y.val := by rfl
        rw [hyv]
        simp [evalPolynomial]⟩ }
  have hcont : Continuous e := inc.continuous.subtype_mk _
  have hclosed : IsClosedMap e := by
    intro T hTc
    have hTz : IsZariskiClosed W T :=
      Variety.isClosed_iff_isZariskiClosed.mp hTc
    have himageZ := closedSubvariety_image_isZariskiClosed hS hTz
    have himageC : IsClosed ((fun y : Variety.Point W => (e y).1) '' T) :=
      Variety.isClosed_iff_isZariskiClosed.mpr himageZ
    have hpre : e '' T =
        Subtype.val ⁻¹' ((fun y : Variety.Point W => (e y).1) '' T) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, hxy⟩
        refine ⟨y, hy, ?_⟩
        apply Subtype.ext
        exact hxy
    rw [hpre]
    exact himageC.preimage continuous_subtype_val
  exact e.toHomeomorphOfContinuousClosed hcont hclosed

end Theory.AlgebraicGroup
