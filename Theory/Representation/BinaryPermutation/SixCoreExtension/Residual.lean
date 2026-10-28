module

public import Theory.Representation.BinaryPermutation.SixCoreExtension

/-!
# Coordinate subgroups in the six-letter binary extension

The centralizer of the weight-two vector consists precisely of the elements
whose permutation part preserves its two-point support. We define the concrete
subgroups W:A4 and W:V4, where W vanishes on that support and V4 is generated
by the two displayed double transpositions on the remaining four letters.
The displayed square root belongs to W:V4.

The two residual identifications remain explicit in the conditional square
calculation. In particular the definitions below do not assert these identities.

Source: Aschbacher–Smith, I.2.2(6b), printed pp.410 and 412, combined
manuscript of 1 March 2004.
-/

@[expose] public section

open Subgroup
namespace BinaryPermutation.SixCoreExtension
noncomputable section

instance : Finite Model :=
  Finite.of_equiv (Multiplicative V × A) SemidirectProduct.equivProd.symm

/-- The permutation actors fixing a specified core vector. -/
def actorStabilizer (v : V) : Subgroup A where
  carrier := {g | coreRepresentation (Fin 6) g.val v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change coreRepresentation (Fin 6) (a.val * b.val) v = v
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    apply ((coreRepresentation (Fin 6)).apply_bijective a.val).injective
    change coreRepresentation (Fin 6) a.val
      (coreRepresentation (Fin 6) a.val⁻¹ v) = coreRepresentation (Fin 6) a.val v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    exact ha.symm

theorem mem_centralizer_vector (x : Model) (v : V) :
    x ∈ centralizer ({vector (Multiplicative.ofAdd v)} : Set Model) ↔
      coreRepresentation (Fin 6) x.right.val v = v := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have hh := congrArg (fun z : Model => z.left) h.symm
    change Multiplicative.ofAdd v * x.left =
      x.left * action x.right (Multiplicative.ofAdd v) at hh
    rw [mul_comm] at hh
    exact (mul_left_cancel hh).symm
  · intro h
    symm
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd v * x.left =
        x.left * action x.right (Multiplicative.ofAdd v)
      change Multiplicative.ofAdd v * x.left =
        x.left * Multiplicative.ofAdd (coreRepresentation (Fin 6) x.right.val v)
      rw [h, mul_comm]
    · simp [vector]

/-- The entire vector subgroup centralizes a vector; only the actor is restricted. -/
theorem centralizer_vector (v : V) :
    centralizer ({vector (Multiplicative.ofAdd v)} : Set Model) =
      (actorStabilizer v).comap SemidirectProduct.rightHom := by
  ext x
  exact mem_centralizer_vector x v

/-- For the marked pair the actor condition is literal preservation of its support. -/
theorem action_pair_iff (g : A) :
    coreRepresentation (Fin 6) g.val pair = pair ↔
      ∀ i : Fin 6, (g.val i = 0 ∨ g.val i = 1) ↔ (i = 0 ∨ i = 1) := by
  have hpair (i : Fin 6) : pair.val i = if i = 0 ∨ i = 1 then 1 else 0 := by
    fin_cases i <;> rfl
  constructor
  · intro h i
    have hh := congrArg (fun v : V => v.val (g.val i)) h
    change pair.val (g.val.symm (g.val i)) = pair.val (g.val i) at hh
    rw [g.val.symm_apply_apply, hpair, hpair] at hh
    split_ifs at hh <;> simp_all
  · intro h
    apply Subtype.ext
    funext i
    change pair.val (g.val.symm i) = pair.val i
    simp only [hpair, ← h (g.val.symm i), g.val.apply_symm_apply]

/-- W:A4: the vector vanishes at 0 and 1, and the actor fixes them individually. -/
def pairResidual : Subgroup Model where
  carrier := {x | x.left.toAdd.val 0 = 0 ∧ x.left.toAdd.val 1 = 0 ∧
    x.right.val 0 = 0 ∧ x.right.val 1 = 1}
  one_mem' := by exact ⟨rfl, rfl, rfl, rfl⟩
  mul_mem' := by
    intro x y hx hy
    have hi (i : Fin 6) (h : x.right.val i = i) : x.right.val.symm i = i := by
      apply x.right.val.injective
      rw [Equiv.apply_symm_apply, h]
    refine ⟨?_, ?_, ?_, ?_⟩
    · change x.left.toAdd.val 0 + y.left.toAdd.val (x.right.val.symm 0) = 0
      rw [hi 0 hx.2.2.1, hx.1, hy.1, add_zero]
    · change x.left.toAdd.val 1 + y.left.toAdd.val (x.right.val.symm 1) = 0
      rw [hi 1 hx.2.2.2, hx.2.1, hy.2.1, add_zero]
    · change x.right.val (y.right.val 0) = 0
      rw [hy.2.2.1, hx.2.2.1]
    · change x.right.val (y.right.val 1) = 1
      rw [hy.2.2.2, hx.2.2.2]
  inv_mem' := by
    intro x hx
    refine ⟨?_, ?_, ?_, ?_⟩
    · change -x.left.toAdd.val (x.right.val 0) = 0
      rw [hx.2.2.1, hx.1, neg_zero]
    · change -x.left.toAdd.val (x.right.val 1) = 0
      rw [hx.2.2.2, hx.2.1, neg_zero]
    · change x.right.val.symm 0 = 0
      apply x.right.val.injective
      rw [Equiv.apply_symm_apply, hx.2.2.1]
    · change x.right.val.symm 1 = 1
      apply x.right.val.injective
      rw [Equiv.apply_symm_apply, hx.2.2.2]

def kleinFirst : A :=
  ⟨Equiv.swap 2 3 * Equiv.swap 4 5, by simp [Equiv.Perm.mem_alternatingGroup]⟩
def kleinSecond : A :=
  ⟨Equiv.swap 2 4 * Equiv.swap 3 5, by simp [Equiv.Perm.mem_alternatingGroup]⟩
/-- The double-transposition group on the four complementary letters. -/
def pairKlein : Subgroup A := closure ({kleinFirst, kleinSecond} : Set A)
/-- W:V4, embedded in the original semidirect product. -/
def pairCore : Subgroup Model := pairResidual ⊓ pairKlein.comap SemidirectProduct.rightHom

theorem root_mem_pairCore : root ∈ pairCore := by
  refine ⟨⟨rfl, rfl, rfl, rfl⟩, ?_⟩
  exact subset_closure (Set.mem_insert _ _)

/-- A coordinate description of the actual marked centralizer. -/
theorem mem_centralizer_pair (x : Model) :
    x ∈ centralizer ({vector (Multiplicative.ofAdd pair)} : Set Model) ↔
      ∀ i : Fin 6, (x.right.val i = 0 ∨ x.right.val i = 1) ↔ (i = 0 ∨ i = 1) :=
  (mem_centralizer_vector x pair).trans (action_pair_iff x.right)

/-- The coordinate residual candidate is a subgroup of the actual centralizer. -/
theorem pairResidual_le_centralizer_pair :
    pairResidual ≤ centralizer ({vector (Multiplicative.ofAdd pair)} : Set Model) := by
  intro x hx
  apply (mem_centralizer_pair x).mpr
  intro i
  constructor
  · rintro (h | h)
    · exact Or.inl (x.right.val.injective (h.trans hx.2.2.1.symm))
    · exact Or.inr (x.right.val.injective (h.trans hx.2.2.2.symm))
  · rintro (rfl | rfl)
    · exact Or.inl hx.2.2.1
    · exact Or.inr hx.2.2.2

/-- The two subgroup identities supply the literal embedded residual core. -/
theorem residualCore_pair_of_identities
    (hres : Theory.GroupTheory.centralizerTwoResidual
      (vector (Multiplicative.ofAdd pair)) = pairResidual)
    (hcore : pairResidual.pCoreIn 2 = pairCore) :
    Theory.GroupTheory.centralizerResidualCore (vector (Multiplicative.ofAdd pair)) =
      pairCore := by
  change (Theory.GroupTheory.centralizerTwoResidual
    (vector (Multiplicative.ofAdd pair))).pCoreIn 2 = pairCore
  rw [hres, hcore]

/-- Consumer of the residual and two-core identities: the marked unique square. -/
theorem unique_square_pair_of_identities
    (hres : Theory.GroupTheory.centralizerTwoResidual
      (vector (Multiplicative.ofAdd pair)) = pairResidual)
    (hcore : pairResidual.pCoreIn 2 = pairCore) :
    ∃! w : Model, (vector (Multiplicative.ofAdd pair))⁻¹ * w ∈ centralLine ∧
      ∃ x ∈ Theory.GroupTheory.centralizerResidualCore (vector (Multiplicative.ofAdd pair)),
        x ^ 2 = w := by
  have he := residualCore_pair_of_identities hres hcore
  apply unique_square_fiber_pair
  · intro x hx
    rw [he] at hx
    exact hx.1.2.2.1
  · rw [he]
    exact root_mem_pairCore

end
end BinaryPermutation.SixCoreExtension
