module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.Swapping

/-!
# The eight marked matrices in the four-pair actor

The even products of four disjoint transpositions are identified with eight
explicit natural matrices. Their exterior-square actions agree, modulo the
constant word, with the deleted eight-point action defining the published
exceptional equivalence. Small kernel-checked binary calculations then give
the common fixed line, the fixed hyperplanes of the distinguished transvection,
and the containment of every nontrivial inner fixed space in those hyperplanes.

Source: Aschbacher--Smith, H.9.3(5), printed p.391, PDF p.402. The comparison
uses the attributed ATLAS construction in Order20160A8; the matrices below
are obtained by evaluating that existing comparison.
-/

@[expose] public section
namespace BinaryNaturalDual.FourActors.A1Module
open BinaryNaturalDual BinaryNaturalDual.FourActors BinaryLinear.OuterCyclic
open Atlas.Order20160A8
open scoped MatrixGroups

-- Link an explicit matrix to the specified exceptional equivalence.
private theorem matrix_marking (g : SL(4, ZMod 2)) (p : Equiv.Perm (Fin 8))
    (h : DeletedEight.orthogonalHom p = Exterior.toOrthogonal g) :
    (linearAlternatingEquiv (slEquivLinear 4 g)).val = p := by
  apply DeletedEight.orthogonalHom_injective
  rw [h]
  have he : linearAlternatingEquiv (slEquivLinear 4 g) =
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8 (sl4TwoEquivPSL g) := by
    change Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
      ((projectiveEquivLinear (by decide : 0 < 4)).symm (slEquivLinear 4 g)) = _
    apply congrArg Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    apply (projectiveEquivLinear (by decide : 0 < 4)).injective
    rw [MulEquiv.apply_symm_apply]
    exact (projectiveEquivLinear_mk (by decide) g).symm
  rw [he, Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal]

private theorem raw_marking (g : SL(4, ZMod 2)) (p : Equiv.Perm (Fin 8))
    (h : ∀ x : DeletedEight.D,
      (fun i => DeletedEight.raw x (p.symm i)) - DeletedEight.raw (Exterior.onD g x) =
        (fun _ => DeletedEight.raw x (p.symm 7))) :
    DeletedEight.orthogonalHom p = Exterior.toOrthogonal g := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  apply DeletedEight.splitEquiv.injective
  change DeletedEight.splitEquiv
    (DeletedEight.splitEquiv.symm (DeletedEight.quotientPerm p (DeletedEight.splitEquiv x))) =
    DeletedEight.splitEquiv (Exterior.onD g x)
  rw [LinearEquiv.apply_symm_apply]
  change Submodule.Quotient.mk (DeletedEight.evenPerm p (DeletedEight.intoEven x)) =
    Submodule.Quotient.mk (DeletedEight.intoEven (Exterior.onD g x))
  apply (Submodule.Quotient.eq _).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨DeletedEight.raw x (p.symm 7), ?_⟩
  apply Subtype.ext
  ext i
  change DeletedEight.raw x (p.symm 7) * 1 =
    DeletedEight.raw x (p.symm i) - DeletedEight.raw (Exterior.onD g x) i
  simpa only [mul_one, Pi.sub_apply] using congrFun (h x).symm i

abbrev Bits := Fin 4 → ZMod 2

def pairPerm (v : Bits) : Equiv.Perm (Fin 8) :=
  Equiv.swap 0 1 ^ (v 0).val * Equiv.swap 2 3 ^ (v 1).val *
  Equiv.swap 4 5 ^ (v 2).val * Equiv.swap 6 7 ^ (v 3).val

def pairHom : Multiplicative Bits →* Equiv.Perm (Fin 8) where
  toFun v := pairPerm v.toAdd
  map_one' := by decide +kernel
  map_mul' v w := (by decide +kernel : ∀ v w : Bits, pairPerm (v + w) = pairPerm v * pairPerm w) v w

theorem pairs_range : permutationA1 = pairHom.range := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact ⟨Multiplicative.ofAdd ![1,0,0,0], by decide +kernel⟩
    · exact ⟨Multiplicative.ofAdd ![0,1,0,0], by decide +kernel⟩
    · exact ⟨Multiplicative.ofAdd ![0,0,1,0], by decide +kernel⟩
    · exact ⟨Multiplicative.ofAdd ![0,0,0,1], by decide +kernel⟩
  · rintro p ⟨v, rfl⟩
    change pairPerm v.toAdd ∈ permutationA1
    unfold pairPerm
    repeat apply Subgroup.mul_mem
    all_goals apply Subgroup.pow_mem
    all_goals apply Subgroup.subset_closure
    all_goals simp

def evenBits : Fin 8 → Bits :=
  ![![0,0,0,0], ![1,1,0,0], ![1,0,1,0], ![0,1,1,0],
    ![1,0,0,1], ![0,1,0,1], ![0,0,1,1], ![1,1,1,1]]
def evenPerm (t : Fin 8) : Equiv.Perm (Fin 8) := pairPerm (evenBits t)

theorem even_cover (v : Bits) (h : (pairPerm v).sign = 1) :
    ∃ t, evenPerm t = pairPerm v :=
  (by decide +kernel : ∀ v : Bits, (pairPerm v).sign = 1 → ∃ t, evenPerm t = pairPerm v) v h

def matrix (t : Fin 8) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  ![!![1,0,0,0; 0,1,0,0; 0,0,1,0; 0,0,0,1],
    !![1,0,0,1; 0,1,1,0; 0,0,1,0; 0,0,0,1],
    !![0,1,0,1; 1,0,1,0; 0,0,0,1; 0,0,1,0],
    !![0,1,1,1; 1,0,1,1; 0,0,0,1; 0,0,1,0],
    !![0,1,0,0; 1,0,0,0; 0,0,0,1; 0,0,1,0],
    !![0,1,1,0; 1,0,0,1; 0,0,0,1; 0,0,1,0],
    !![1,0,1,0; 0,1,0,1; 0,0,1,0; 0,0,0,1],
    !![1,0,1,1; 0,1,1,1; 0,0,1,0; 0,0,0,1]] t

def matrixSL (t : Fin 8) : SL(4, ZMod 2) :=
  ⟨matrix t, (by decide +kernel : ∀ t, (matrix t).det = 1) t⟩
noncomputable def linear (t : Fin 8) : G := slEquivLinear 4 (matrixSL t)

@[simp] theorem linear_apply (t : Fin 8) (x : X) : linear t x = (matrix t).mulVec x := rfl

theorem marking (t : Fin 8) : (linearAlternatingEquiv (linear t)).val = evenPerm t := by
  apply matrix_marking
  apply raw_marking
  exact (by decide +kernel : ∀ t : Fin 8, ∀ x : DeletedEight.D,
    (fun i => DeletedEight.raw x ((evenPerm t).symm i)) -
      DeletedEight.raw (Exterior.onD (matrixSL t) x) =
        fun _ => DeletedEight.raw x ((evenPerm t).symm 7)) t

theorem conj_linear_mem (t : Fin 8) : MulAut.conj (linear t) ∈ B1 := by
  constructor
  · change permutationEquiv (MulAut.conj (linear t)) ∈ permutationA1
    rw [permutationEquiv_inner, marking, pairs_range]
    exact ⟨Multiplicative.ofAdd (evenBits t), rfl⟩
  · exact ⟨linear t, rfl⟩

theorem inner_cover (b : M) (hb : b ∈ B1) : ∃ t : Fin 8, b = MulAut.conj (linear t) := by
  have hp : permutationEquiv b ∈ pairHom.range := pairs_range ▸ hb.1
  obtain ⟨v, hv⟩ := hp
  have hs : (pairPerm v.toAdd).sign = 1 := by
    rw [← Equiv.Perm.mem_alternatingGroup]
    change pairHom v ∈ alternatingGroup (Fin 8)
    rw [hv]
    exact (permutationEquiv_mem_alternating b).mpr hb.2
  obtain ⟨t, ht⟩ := even_cover v.toAdd hs
  refine ⟨t, permutationEquiv.injective ?_⟩
  rw [permutationEquiv_inner, marking, ht]
  exact hv.symm

theorem linear_zero : linear 0 = 1 := by
  ext x i
  change (matrix 0).mulVec x i = x i
  exact congrFun ((by decide +kernel : ∀ x : X, (matrix 0).mulVec x = x) x) i

theorem r_eq : r = MulAut.conj (linear 7) := by
  apply permutationEquiv.injective
  rw [permutationEquiv_r, permutationEquiv_inner, marking]
  decide +kernel

theorem linear_involutive (t : Fin 8) : Function.Involutive (linear t) :=
  (by decide +kernel : ∀ t : Fin 8, ∀ x : X, (matrix t).mulVec ((matrix t).mulVec x) = x) t

theorem linear_symm (t : Fin 8) : (linear t).symm = linear t := by
  apply LinearEquiv.ext
  intro x
  apply (linear t).injective
  rw [LinearEquiv.apply_symm_apply, linear_involutive]

noncomputable def dualCoordinates : X ≃ₗ[ZMod 2] Module.Dual (ZMod 2) X :=
  dotProductEquiv (ZMod 2) (Fin 4)

theorem dual_apply (t : Fin 8) (y : X) :
    (linear t).symm.dualMap (dualCoordinates y) = dualCoordinates ((matrix t).transpose.mulVec y) := by
  rw [linear_symm]
  apply LinearMap.ext
  intro x
  change dotProduct y ((matrix t).mulVec x) = dotProduct ((matrix t).transpose.mulVec y) x
  exact (Matrix.dotProduct_transpose_mulVec (matrix t) x y).symm.trans (dotProduct_comm _ _)

theorem natural_fixed_iff (x : X) :
    x ∈ naturalFixed B1 ↔ ∃ c : ZMod 2, x = c • (![1,1,0,0] : X) := by
  have h : (∀ t : Fin 8, (matrix t).mulVec x = x) ↔
      ∃ c : ZMod 2, x = c • (![1,1,0,0] : X) :=
    (by decide +kernel : ∀ x : X, (∀ t : Fin 8, (matrix t).mulVec x = x) ↔
      ∃ c : ZMod 2, x = c • (![1,1,0,0] : X)) x
  rw [← h, mem_naturalFixed]
  constructor
  · intro hx t
    exact hx (linear t) (conj_linear_mem t)
  · intro hx g hg
    obtain ⟨t, ht⟩ := inner_cover (MulAut.conj g) hg
    have he : g = linear t := MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot ht
    rw [he]
    exact hx t

theorem natural_fixed_line : naturalFixed B1 = Submodule.span (ZMod 2) {(![1,1,0,0] : X)} := by
  ext x
  rw [natural_fixed_iff, Submodule.mem_span_singleton]
  exact exists_congr fun c => eq_comm

theorem natural_fixed_finrank : Module.finrank (ZMod 2) (naturalFixed B1) = 1 := by
  rw [natural_fixed_line]
  exact finrank_span_singleton (by decide +kernel)

theorem natural_r_fixed (x : X) : linear 7 x = x ↔ x 2 = x 3 :=
  (by decide +kernel : ∀ x : X, (matrix 7).mulVec x = x ↔ x 2 = x 3) x

theorem dual_r_fixed (y : X) :
    (linear 7).symm.dualMap (dualCoordinates y) = dualCoordinates y ↔ y 0 = y 1 := by
  rw [dual_apply, (dualCoordinates).injective.eq_iff]
  exact (by decide +kernel : ∀ y : X, (matrix 7).transpose.mulVec y = y ↔ y 0 = y 1) y

theorem natural_fixed_le_r (t : Fin 8) (ht : t ≠ 0) (x : X) (hx : linear t x = x) :
    linear 7 x = x := by
  rw [natural_r_fixed]
  exact (by decide +kernel : ∀ t : Fin 8, t ≠ 0 → ∀ x : X,
    (matrix t).mulVec x = x → x 2 = x 3) t ht x hx

theorem dual_fixed_le_r (t : Fin 8) (ht : t ≠ 0) (f : Module.Dual (ZMod 2) X)
    (hf : (linear t).symm.dualMap f = f) : (linear 7).symm.dualMap f = f := by
  obtain ⟨y, rfl⟩ := dualCoordinates.surjective f
  rw [dual_apply, dualCoordinates.injective.eq_iff] at hf
  rw [dual_r_fixed]
  exact (by decide +kernel : ∀ t : Fin 8, t ≠ 0 → ∀ y : X,
    (matrix t).transpose.mulVec y = y → y 0 = y 1) t ht y hf

theorem conj_linear_injective : Function.Injective (fun t => MulAut.conj (linear t)) := by
  intro s t h
  have he := congrArg permutationEquiv h
  simp only [permutationEquiv_inner, marking] at he
  exact (by decide +kernel : Function.Injective evenPerm) he


end BinaryNaturalDual.FourActors.A1Module
