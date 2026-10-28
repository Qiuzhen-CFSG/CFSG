module
public import Theory.Character.ModularBlock.PrimitiveCentralIdempotent
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Idempotents

/-!
# Nilpotence in finite primitive central corners

Let e be a centrally primitive idempotent in a finite ring. A central element
a satisfying a * e = a is nilpotent if a unital homomorphism to a nontrivial
commutative ring sends e to one and a to zero. This is the ring-theoretic
nilpotence input for eliminating augmentation-zero transfer witnesses in the
principal-block corner; it assumes no principal-block primitivity theorem.

The corner of the commutative center cut out by e has only trivial
idempotents. Artinian idempotent separation makes its maximal ideal unique,
so this finite corner is local. The given homomorphism restricts to a unital
map on the corner, making a a nonunit there and hence nilpotent. The corner
inclusion into the ambient ring is not unital: the proof excludes exponent
zero before transporting a positive vanishing power.

Ported from the four generic ring results in
`Submission/ZStar/PrimitiveCorner.lean` at revision `c3503435` of
`public/lean-eval/glauberman_zStar`. The shared
`ModularBlock.IsCentrallyPrimitive` predicate is used throughout. The
locality proof uses the existing unique-maximal-ideal criterion directly.
-/

noncomputable section

namespace ModularBlock
namespace PrimitiveCorner

universe u v

/-- A finite nontrivial commutative ring with only trivial idempotents is
local. -/
public theorem isLocalRing_of_finite_of_isIdempotentElem_eq_zero_or_one
    (A : Type u) [CommRing A] [Finite A] [Nontrivial A]
    (hidem : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1) :
    IsLocalRing A := by
  let : IsArtinianRing A := isArtinian_of_finite
  obtain ⟨p, hp⟩ := Ideal.exists_maximal A
  apply IsLocalRing.of_unique_max_ideal
  refine ⟨p, hp, ?_⟩
  intro q hq
  by_contra hqp
  let : p.IsPrime := hp.isPrime
  obtain ⟨r, hrp, hridem, hrq⟩ :=
    IsArtinianRing.exists_not_mem_forall_mem_of_ne p
  rcases hidem r hridem with rfl | rfl
  · exact hrp p.zero_mem
  · have hone : (1 : A) ∈ q := hrq q hq.isPrime hqp
    exact hq.ne_top ((Ideal.eq_top_iff_one q).mpr hone)

/-- In a finite local commutative ring, the nonunits are exactly the
nilpotent elements. -/
public theorem isNilpotent_iff_not_isUnit_of_finite_local
    (A : Type u) [CommRing A] [Finite A] [IsLocalRing A]
    (x : A) :
    IsNilpotent x ↔ ¬ IsUnit x := by
  let : IsArtinianRing A := isArtinian_of_finite
  have hbase : Ring.KrullDimLE 0 A ∧ IsLocalRing A :=
    ⟨inferInstance, inferInstance⟩
  have hall : ∀ y : A, IsNilpotent y ↔ ¬ IsUnit y :=
    ((Ring.krullDimLE_zero_and_isLocalRing_tfae A).out 0 2).mp
      hbase
  exact hall x

/-- The central corner cut out by a centrally primitive idempotent in a
finite ring is local. -/
public theorem centrallyPrimitive_centerCorner_isLocalRing
    {A : Type u} [Ring A] [Finite A]
    (e : A) (he : IsCentrallyPrimitive e) :
    let Z := Subring.center A
    let eZ : Z := ⟨e, he.1⟩
    let heZ : IsIdempotentElem eZ := by
      exact Subtype.ext he.2.1.eq
    IsLocalRing heZ.Corner := by
  let Z := Subring.center A
  let eZ : Z := ⟨e, he.1⟩
  have heZ : IsIdempotentElem eZ := by
    exact Subtype.ext he.2.1.eq
  let C := heZ.Corner
  let : Finite Z :=
    Finite.of_injective (fun z : Z => (z : A)) Subtype.val_injective
  let : Finite C :=
    Finite.of_injective (fun x : C => ((x.1 : Z) : A)) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact h)
  have hne : (1 : C) ≠ 0 := by
    intro h
    apply he.2.2.1
    have h' := congrArg (fun x : C => ((x.1 : Z) : A)) h
    change e = 0 at h'
    exact h'
  let : Nontrivial C := ⟨⟨1, 0, hne⟩⟩
  apply isLocalRing_of_finite_of_isIdempotentElem_eq_zero_or_one C
  intro x hx
  by_cases hxzero : ((x.1 : Z) : A) = 0
  · left
    apply Subtype.ext
    apply Subtype.ext
    exact hxzero
  · right
    have hxidem : IsIdempotentElem ((x.1 : Z) : A) := by
      exact congrArg (fun y : C => ((y.1 : Z) : A)) hx
    have hxcorner := (Subsemigroup.mem_corner_iff heZ).mp x.property
    have hxfactor : ((x.1 : Z) : A) * e = ((x.1 : Z) : A) := by
      exact congrArg (fun y : Z => (y : A)) hxcorner.2
    have hxe : ((x.1 : Z) : A) = e :=
      he.2.2.2 ((x.1 : Z) : A) x.1.property hxidem hxfactor hxzero
    apply Subtype.ext
    apply Subtype.ext
    exact hxe

/-- In a finite ring, an element in a centrally primitive corner that is
killed by a unital map to a nontrivial commutative ring is nilpotent. -/
public theorem isNilpotent_of_centrallyPrimitive_of_map_eq_zero
    {A : Type u} [Ring A] [Finite A]
    {K : Type v} [CommRing K] [Nontrivial K]
    (eps : A →+* K) (e a : A)
    (he : IsCentrallyPrimitive e)
    (haCenter : a ∈ Set.center A)
    (hfactor : a * e = a)
    (hepsE : eps e = 1)
    (hepsA : eps a = 0) :
    IsNilpotent a := by
  let Z := Subring.center A
  let eZ : Z := ⟨e, he.1⟩
  have heZ : IsIdempotentElem eZ := by
    exact Subtype.ext he.2.1.eq
  let C := heZ.Corner
  let : Finite Z :=
    Finite.of_injective (fun z : Z => (z : A)) Subtype.val_injective
  let : Finite C :=
    Finite.of_injective (fun x : C => ((x.1 : Z) : A)) (by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      exact h)
  have hne : (1 : C) ≠ 0 := by
    intro h
    apply he.2.2.1
    have h' := congrArg (fun x : C => ((x.1 : Z) : A)) h
    change e = 0 at h'
    exact h'
  let : Nontrivial C := ⟨⟨1, 0, hne⟩⟩
  let : IsLocalRing C :=
    centrallyPrimitive_centerCorner_isLocalRing e he
  let aZ : Z := ⟨a, haCenter⟩
  have hea : e * a = a := by
    exact (Semigroup.mem_center_iff.mp he.1 a).symm.trans hfactor
  have haCorner : aZ ∈ Subsemigroup.corner eZ := by
    exact (Subsemigroup.mem_corner_iff heZ).2
      ⟨Subtype.ext hea, Subtype.ext hfactor⟩
  let aC : C := ⟨aZ, haCorner⟩
  let epsC : C →+* K :=
    { toFun := fun x => eps ((x.1 : Z) : A)
      map_one' := by
        change eps e = 1
        exact hepsE
      map_mul' := by
        intro x y
        exact map_mul eps ((x.1 : Z) : A) ((y.1 : Z) : A)
      map_zero' := map_zero eps
      map_add' := by
        intro x y
        exact map_add eps ((x.1 : Z) : A) ((y.1 : Z) : A) }
  have haCnonunit : ¬ IsUnit aC := by
    intro haUnit
    have hmapUnit : IsUnit (epsC aC) := haUnit.map epsC
    have hzero : epsC aC = 0 := by
      exact hepsA
    rw [hzero] at hmapUnit
    exact not_isUnit_zero hmapUnit
  have hnilC : IsNilpotent aC :=
    (isNilpotent_iff_not_isUnit_of_finite_local C aC).2 haCnonunit
  rcases hnilC with ⟨n, hn⟩
  rcases n with _ | n
  · simp at hn
  refine ⟨n + 1, ?_⟩
  have hcoe_pow_succ : ∀ m : ℕ,
      ((((aC ^ Nat.succ m).1 : Z) : A)) = a ^ Nat.succ m := by
    intro m
    induction m with
    | zero =>
        simp only [pow_one]
        rfl
    | succ m ih =>
        calc
          ((((aC ^ Nat.succ (Nat.succ m)).1 : Z) : A)) =
              ((((aC ^ Nat.succ m * aC).1 : Z) : A)) := by rw [pow_succ]
          _ = ((((aC ^ Nat.succ m).1 : Z) : A)) * a := rfl
          _ = a ^ Nat.succ m * a := by rw [ih]
          _ = a ^ Nat.succ (Nat.succ m) := by
            simp only [pow_succ]
  calc
    a ^ (n + 1) = ((((aC ^ (n + 1)).1 : Z) : A)) :=
      (hcoe_pow_succ n).symm
    _ = (((0 : C).1 : Z) : A) :=
      congrArg (fun x : C => ((x.1 : Z) : A)) hn
    _ = 0 := rfl


end PrimitiveCorner
end ModularBlock

