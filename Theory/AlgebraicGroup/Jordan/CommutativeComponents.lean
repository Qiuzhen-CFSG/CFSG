module

public import Theory.AlgebraicGroup.Jordan.CommutativeRegularity
public import Theory.AlgebraicGroup.Morphism.Operations

/-!
# Jordan component homomorphisms for commutative algebraic groups

For a commutative algebraic group over an algebraically closed field, this module upgrades the
regular semisimple projection to an algebraic-group morphism and constructs the regular
unipotent projection. It also proves the multiplication laws for both components and the
criteria detecting semisimple or unipotent points by vanishing of the opposite component.

The algebraic input is Jordan uniqueness. Closure of commuting unipotent elements under
multiplication is proved directly on common finite invariant coordinate submodules, so this
module remains independent of maximal-torus theory. These morphisms supply the kernels used
in `Jordan.Commutative`.

The statements implement the component-morphism portion of Bor1, Chapter 1, Theorem 4.7.
-/

universe u

set_option linter.style.haveILetI false

namespace Theory.AlgebraicGroup

open _root_.Module.End

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private lemma unipotentElement_mul_of_commute
    {G : Variety k} [AlgebraicGroup G] {x y : Variety.Point G}
    (hx : IsUnipotentElement G x) (hy : IsUnipotentElement G y)
    (hxy : Commute x y) : IsUnipotentElement G (x * y) := by
  let A := Variety.PolynomialFunction G
  let T : Module.End k A := rightTranslationPullback G x
  let U : Module.End k A := rightTranslationPullback G y
  have hTU : Commute T U := by
    change T.comp U = U.comp T
    rw [← rightTranslationPullback_mul, ← rightTranslationPullback_mul]
    exact congrArg (rightTranslationPullback G) hxy.eq
  have hTloc : Module.End.IsLocallyFinite T :=
    rightTranslationPullback_locallyFinite G x
  have hUloc : Module.End.IsLocallyFinite U :=
    rightTranslationPullback_locallyFinite G y
  intro f
  let P : Submodule k A := hTloc.submodule f
  have hPfinite : Module.Finite k P := hTloc.finite f
  have hP : P ∈ T.invtSubmodule := hTloc.invariant f
  obtain ⟨Q, hQfinite, hPQ, hTQ, hUQ⟩ :=
    hTloc.exists_common_finite_invariant_extension hUloc hTU P
  letI : Module.Finite k Q := hQfinite
  let TQ : Module.End k Q := T.restrict hTQ
  let UQ : Module.End k Q := U.restrict hUQ
  have hTQnil : IsNilpotent (TQ - 1) := by
    refine ⟨Module.finrank k Q,
      endomorphism_pow_finrank_eq_zero_of_locallyNilpotent (TQ - 1) ?_⟩
    intro z
    obtain ⟨n, hn⟩ := hx z.1
    refine ⟨n, ?_⟩
    have hiterate : ∀ (m : ℕ) (w : Q),
        ((((⇑(TQ - 1))^[m]) w : Q) : A) =
          ((⇑(T - 1))^[m]) w.1 := by
      intro m
      induction m with
      | zero => intro w; rfl
      | succ m ih =>
          intro w
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          calc
            ((((⇑(TQ - 1))^[m]) ((TQ - 1) w) : Q) : A) =
                ((⇑(T - 1))^[m]) ((TQ - 1) w).1 := ih ((TQ - 1) w)
            _ = ((⇑(T - 1))^[m]) ((T - 1) w.1) := by
              congr 1
    apply Subtype.ext
    exact (hiterate n z).trans hn
  have hUQnil : IsNilpotent (UQ - 1) := by
    refine ⟨Module.finrank k Q,
      endomorphism_pow_finrank_eq_zero_of_locallyNilpotent (UQ - 1) ?_⟩
    intro z
    obtain ⟨n, hn⟩ := hy z.1
    refine ⟨n, ?_⟩
    have hiterate : ∀ (m : ℕ) (w : Q),
        ((((⇑(UQ - 1))^[m]) w : Q) : A) =
          ((⇑(U - 1))^[m]) w.1 := by
      intro m
      induction m with
      | zero => intro w; rfl
      | succ m ih =>
          intro w
          rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
          calc
            ((((⇑(UQ - 1))^[m]) ((UQ - 1) w) : Q) : A) =
                ((⇑(U - 1))^[m]) ((UQ - 1) w).1 := ih ((UQ - 1) w)
            _ = ((⇑(U - 1))^[m]) ((U - 1) w.1) := by
              congr 1
    apply Subtype.ext
    exact (hiterate n z).trans hn
  have hTUQ : Commute TQ UQ := by
    change TQ * UQ = UQ * TQ
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    exact LinearMap.congr_fun hTU.eq z.1
  have hDU : Commute (TQ - 1) (UQ - 1) := by
    change (TQ - 1) * (UQ - 1) = (UQ - 1) * (TQ - 1)
    apply LinearMap.ext
    intro z
    change TQ (UQ z - z) - (UQ z - z) =
      UQ (TQ z - z) - (TQ z - z)
    rw [map_sub, map_sub]
    have hpoint := LinearMap.congr_fun hTUQ.eq z
    change TQ (UQ z) = UQ (TQ z) at hpoint
    rw [hpoint]
    abel
  have hprodNil : IsNilpotent (TQ * UQ - 1) := by
    have hmulNil : IsNilpotent ((TQ - 1) * (UQ - 1)) :=
      hDU.isNilpotent_mul_right hTQnil
    have hD_mul : Commute (TQ - 1) ((TQ - 1) * (UQ - 1)) := by
      exact (Commute.refl (TQ - 1)).mul_right hDU
    have hE_mul : Commute (UQ - 1) ((TQ - 1) * (UQ - 1)) := by
      exact hDU.symm.mul_right (Commute.refl (UQ - 1))
    have hsumNil : IsNilpotent ((TQ - 1) + (UQ - 1) +
        (TQ - 1) * (UQ - 1)) :=
      Commute.isNilpotent_add (hD_mul.add_left hE_mul)
        (hDU.isNilpotent_add hTQnil hUQnil) hmulNil
    convert hsumNil using 1
    apply LinearMap.ext
    intro z
    change TQ (UQ z) - z =
      (TQ z - z) + (UQ z - z) + (TQ (UQ z - z) - (UQ z - z))
    rw [map_sub]
    abel
  obtain ⟨n, hn⟩ := hprodNil
  refine ⟨n, ?_⟩
  have hfQ : f ∈ Q := hPQ (hTloc.mem f)
  let z : Q := ⟨f, hfQ⟩
  have hpower : ∀ (m : ℕ) (w : Q),
      ((((TQ * UQ - 1) ^ m) w : Q) : A) =
        ((T * U - 1) ^ m) w.1 := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
        intro w
        rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
        calc
          (((TQ * UQ - 1) (((TQ * UQ - 1) ^ m) w) : Q) : A) =
              (T * U - 1) ((((TQ * UQ - 1) ^ m) w : Q) : A) := by rfl
          _ = (T * U - 1) (((T * U - 1) ^ m) w.1) := by rw [ih w]
  have hz : ((T * U - 1) ^ n) f = 0 := by
    calc
      ((T * U - 1) ^ n) f =
          ((((TQ * UQ - 1) ^ n) z : Q) : A) := (hpower n z).symm
      _ = 0 := by rw [hn]; rfl
  change ((⇑(rightTranslationPullback G (x * y) -
    (1 : Module.End k A)) : A → A)^[n]) f = 0
  rw [rightTranslationPullback_mul]
  change ((⇑(T * U - 1) : A → A)^[n]) f = 0
  simpa only [Module.End.coe_pow] using hz

private lemma semisimpleElement_mul_of_commute
    {G : Variety k} [AlgebraicGroup G] {x y : Variety.Point G}
    (hx : IsSemisimpleElement G x) (hy : IsSemisimpleElement G y)
    (hxy : Commute x y) : IsSemisimpleElement G (x * y) := by
  have hTU : Commute (rightTranslationPullback G x)
      (rightTranslationPullback G y) := by
    change (rightTranslationPullback G x).comp (rightTranslationPullback G y) =
      (rightTranslationPullback G y).comp (rightTranslationPullback G x)
    rw [← rightTranslationPullback_mul, ← rightTranslationPullback_mul]
    exact congrArg (rightTranslationPullback G) hxy.eq
  rw [IsSemisimpleElement, rightTranslationPullback_mul]
  exact Module.End.IsFinitelySemisimple.mul_of_commute
    (rightTranslationPullback_locallyFinite G x)
    (rightTranslationPullback_locallyFinite G y) hx hy hTU

private noncomputable def commutativeJordanDecompositionMul
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G))
    (x y : Variety.Point G) : JordanDecomposition (x * y) := by
  have hc := isMulCommutative_iff.mp hcomm
  let dx := jordanDecomposition x
  let dy := jordanDecomposition y
  refine
    { semisimplePart := dx.semisimplePart * dy.semisimplePart
      unipotentPart := dx.unipotentPart * dy.unipotentPart
      eq_mul := ?_
      commute := hc _ _
      semisimple := semisimpleElement_mul_of_commute dx.semisimple dy.semisimple (hc _ _)
      unipotent := unipotentElement_mul_of_commute dx.unipotent dy.unipotent (hc _ _) }
  calc
    x * y = (dx.semisimplePart * dx.unipotentPart) *
        (dy.semisimplePart * dy.unipotentPart) := by rw [← dx.eq_mul, ← dy.eq_mul]
    _ = dx.semisimplePart * (dx.unipotentPart * dy.semisimplePart) *
        dy.unipotentPart := by group
    _ = dx.semisimplePart * (dy.semisimplePart * dx.unipotentPart) *
        dy.unipotentPart := by rw [hc dx.unipotentPart dy.semisimplePart]
    _ = (dx.semisimplePart * dy.semisimplePart) *
        (dx.unipotentPart * dy.unipotentPart) := by group

/-- The semisimple Jordan component preserves multiplication in a commutative algebraic group. -/
public lemma commutativeSemisimpleComponent_mul
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G))
    (x y : Variety.Point G) :
    (jordanDecomposition (x * y)).semisimplePart =
      (jordanDecomposition x).semisimplePart *
        (jordanDecomposition y).semisimplePart := by
  exact congrArg JordanDecomposition.semisimplePart
    ((jordanDecomposition (x * y)).unique
      (commutativeJordanDecompositionMul G hcomm x y))

/-- The unipotent Jordan component preserves multiplication in a commutative algebraic group. -/
public lemma commutativeUnipotentComponent_mul
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G))
    (x y : Variety.Point G) :
    (jordanDecomposition (x * y)).unipotentPart =
      (jordanDecomposition x).unipotentPart *
        (jordanDecomposition y).unipotentPart := by
  exact congrArg JordanDecomposition.unipotentPart
    ((jordanDecomposition (x * y)).unique
      (commutativeJordanDecompositionMul G hcomm x y))

private noncomputable def oneJordanDecomposition
    (G : Variety k) [AlgebraicGroup G] :
    JordanDecomposition (1 : Variety.Point G) where
  semisimplePart := 1
  unipotentPart := 1
  eq_mul := (mul_one 1).symm
  commute := Commute.refl 1
  semisimple := one_isSemisimpleElement G
  unipotent := one_isUnipotentElement G

/-- The semisimple Jordan component of the identity is the identity. -/
public lemma commutativeSemisimpleComponent_one
    (G : Variety k) [AlgebraicGroup G] :
    (jordanDecomposition (1 : Variety.Point G)).semisimplePart = 1 := by
  exact congrArg JordanDecomposition.semisimplePart
    ((jordanDecomposition (1 : Variety.Point G)).unique (oneJordanDecomposition G))

/-- The unipotent Jordan component of the identity is the identity. -/
public lemma commutativeUnipotentComponent_one
    (G : Variety k) [AlgebraicGroup G] :
    (jordanDecomposition (1 : Variety.Point G)).unipotentPart = 1 := by
  exact congrArg JordanDecomposition.unipotentPart
    ((jordanDecomposition (1 : Variety.Point G)).unique (oneJordanDecomposition G))

/-- The semisimple Jordan component as an algebraic-group endomorphism. -/
@[expose]
public noncomputable def commutativeSemisimpleComponentMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup.Morphism G G where
  toVariety :=
    { toFun := fun g => (jordanDecomposition g).semisimplePart
      regular := commutativeSemisimpleComponent_regular G hcomm }
  map_one := commutativeSemisimpleComponent_one G
  map_mul := commutativeSemisimpleComponent_mul G hcomm

/-- Evaluation of the semisimple-component algebraic-group morphism. -/
public lemma commutativeSemisimpleComponentMorphism_apply
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) (g : Variety.Point G) :
    (commutativeSemisimpleComponentMorphism G hcomm).onPoints g =
      (jordanDecomposition g).semisimplePart := rfl

/-- The unipotent Jordan component as a regular self-map of the underlying variety. -/
@[expose]
public noncomputable def commutativeUnipotentComponentVarietyMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) : Variety.Morphism G G :=
  (AlgebraicGroup.mulMorphism G).comp
    (((AlgebraicGroup.invMorphism G).comp
      (commutativeSemisimpleComponentMorphism G hcomm).toVariety).pair
        (Variety.Morphism.id G))

private lemma commutativeUnipotentComponentVarietyMorphism_apply
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) (g : Variety.Point G) :
    (commutativeUnipotentComponentVarietyMorphism G hcomm).toFun g =
      (jordanDecomposition g).unipotentPart := by
  change (jordanDecomposition g).semisimplePart⁻¹ * g =
    (jordanDecomposition g).unipotentPart
  calc
    (jordanDecomposition g).semisimplePart⁻¹ * g =
        (jordanDecomposition g).semisimplePart⁻¹ *
          ((jordanDecomposition g).semisimplePart *
            (jordanDecomposition g).unipotentPart) :=
      congrArg ((jordanDecomposition g).semisimplePart⁻¹ * ·)
        (jordanDecomposition g).eq_mul
    _ = (jordanDecomposition g).unipotentPart := by group

/-- The unipotent Jordan component as an algebraic-group endomorphism. -/
@[expose]
public noncomputable def commutativeUnipotentComponentMorphism
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) :
    AlgebraicGroup.Morphism G G where
  toVariety := commutativeUnipotentComponentVarietyMorphism G hcomm
  map_one := by
    rw [commutativeUnipotentComponentVarietyMorphism_apply G hcomm,
      commutativeUnipotentComponent_one G]
  map_mul := by
    intro x y
    rw [commutativeUnipotentComponentVarietyMorphism_apply G hcomm,
      commutativeUnipotentComponentVarietyMorphism_apply G hcomm,
      commutativeUnipotentComponentVarietyMorphism_apply G hcomm,
      commutativeUnipotentComponent_mul G hcomm]

/-- Evaluation of the unipotent-component algebraic-group morphism. -/
public lemma commutativeUnipotentComponentMorphism_apply
    (G : Variety k) [AlgebraicGroup G]
    (hcomm : IsMulCommutative (Variety.Point G)) (g : Variety.Point G) :
    (commutativeUnipotentComponentMorphism G hcomm).onPoints g =
      (jordanDecomposition g).unipotentPart :=
  commutativeUnipotentComponentVarietyMorphism_apply G hcomm g

/-- A point is semisimple exactly when its unipotent Jordan component is the identity. -/
public theorem isSemisimpleElement_iff_unipotentComponent_eq_one
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    IsSemisimpleElement G g ↔
      (jordanDecomposition g).unipotentPart = 1 := by
  constructor
  · intro hg
    let d : JordanDecomposition g :=
      { semisimplePart := g
        unipotentPart := 1
        eq_mul := (mul_one g).symm
        commute := Commute.one_right g
        semisimple := hg
        unipotent := one_isUnipotentElement G }
    exact congrArg JordanDecomposition.unipotentPart
      ((jordanDecomposition g).unique d)
  · intro hu
    have hs := (jordanDecomposition g).semisimple
    rw [(jordanDecomposition g).eq_mul, hu, mul_one]
    exact hs

/-- A point is unipotent exactly when its semisimple Jordan component is the identity. -/
public theorem isUnipotentElement_iff_semisimpleComponent_eq_one
    (G : Variety k) [AlgebraicGroup G] (g : Variety.Point G) :
    IsUnipotentElement G g ↔
      (jordanDecomposition g).semisimplePart = 1 := by
  constructor
  · intro hg
    let d : JordanDecomposition g :=
      { semisimplePart := 1
        unipotentPart := g
        eq_mul := (one_mul g).symm
        commute := Commute.one_left g
        semisimple := one_isSemisimpleElement G
        unipotent := hg }
    exact congrArg JordanDecomposition.semisimplePart
      ((jordanDecomposition g).unique d)
  · intro hs
    have hu := (jordanDecomposition g).unipotent
    rw [(jordanDecomposition g).eq_mul, hs, one_mul]
    exact hu


end Theory.AlgebraicGroup
