module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.SignedAction.Identities
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Quotients
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Frattini
public import Theory.Representation.BinaryPermutationSixCover.Facts
import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Abel

/-!
# The intrinsic signed A₆ action

Permuting the six generators and collecting them in increasing order adds
the inversion correction to the sign coordinate. The reordering identities
prove that this formula is multiplicative and composes, giving an actual
symmetric-group action and its restriction to A₆. The sign kernel is fixed
pointwise. The volume correction is a homomorphism to the binary sign group,
so perfectness of A₆ forces the volume to be fixed as well.

The action displacements project to the generating differences in the literal
augmentation module. The Frattini lifting theorem therefore makes them generate
the whole coordinate group. All quotient equations and generation survive
explicit precomposition by an automorphism of the A₆ actor.

This is the intrinsic action input for the quartic radical in
Aschbacher–Smith, combined manuscript (1 March 2004), I.2.2(6), printed
pp.410 and 412. Recognition of the original radical is a separate assembly.
-/

@[expose] public section

namespace EvenCliffordSix
open BinaryPermutation

@[simp] theorem signedCorrection_one (v : V) : signedCorrection 1 v = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  exact if_neg (fun h => lt_asymm h.1 h.2)

@[simp] theorem signedCorrection_zero (p : Equiv.Perm (Fin 6)) :
    signedCorrection p 0 = 0 := by simp [signedCorrection]

@[simp] theorem signedTo_one (p : Equiv.Perm (Fin 6)) : signedTo p 1 = 1 := by
  apply Model.ext
  · simp [signedTo]
  · exact map_zero (coreRepresentation (Fin 6) p)

@[simp] theorem signedTo_id (x : Model) : signedTo 1 x = x := by
  apply Model.ext
  · simp [signedTo]
  · exact congrArg (fun f => f x.vector) (map_one (coreRepresentation (Fin 6)))

theorem signedTo_mul (p : Equiv.Perm (Fin 6)) (x y : Model) :
    signedTo p (x * y) = signedTo p x * signedTo p y := by
  apply Model.ext
  · change x.sign + y.sign + cocycle x.vector.val y.vector.val +
      signedCorrection p (x.vector + y.vector) =
      (x.sign + signedCorrection p x.vector) + (y.sign + signedCorrection p y.vector) +
        cocycle (permuteVector p x.vector).val (permuteVector p y.vector).val
    rw [signedCorrection_add]
    calc
      _ = (x.sign + signedCorrection p x.vector) +
          (y.sign + signedCorrection p y.vector) +
          cocycle (permuteVector p x.vector).val (permuteVector p y.vector).val +
          (cocycle x.vector.val y.vector.val + cocycle x.vector.val y.vector.val) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero, add_zero]
  · exact map_add (coreRepresentation (Fin 6) p) x.vector y.vector

theorem signedTo_comp (p q : Equiv.Perm (Fin 6)) (x : Model) :
    signedTo (p * q) x = signedTo p (signedTo q x) := by
  apply Model.ext
  · change x.sign + signedCorrection (p * q) x.vector =
      (x.sign + signedCorrection q x.vector) + signedCorrection p (permuteVector q x.vector)
    rw [signedCorrection_comp, add_assoc]
  · exact congrArg (fun f => f x.vector) (map_mul (coreRepresentation (Fin 6)) p q)

/-- The signed permutation formula defines the full symmetric-group action. -/
def symmetricAction : Equiv.Perm (Fin 6) →* MulAut Model where
  toFun p :=
    { toFun := signedTo p
      invFun := signedTo p⁻¹
      left_inv x := by rw [← signedTo_comp, inv_mul_cancel, signedTo_id]
      right_inv x := by rw [← signedTo_comp, mul_inv_cancel, signedTo_id]
      map_mul' := signedTo_mul p }
  map_one' := MulEquiv.ext signedTo_id
  map_mul' p q := MulEquiv.ext (signedTo_comp p q)

/-- The intrinsic A₆ action on the even signed monomials. -/
def action : A →* MulAut Model := symmetricAction.comp (alternatingGroup (Fin 6)).subtype

@[simp] theorem action_apply (a : A) (x : Model) : action a x = signedTo a.val x := rfl

@[simp] theorem symmetricAction_centralSign (p : Equiv.Perm (Fin 6)) (c : F) :
    symmetricAction p (centralSign c) = centralSign c := by
  apply Model.ext
  · change c + signedCorrection p 0 = c
    simp
  · exact map_zero (coreRepresentation (Fin 6) p)

@[simp] theorem action_centralSign (a : A) (c : F) :
    action a (centralSign c) = centralSign c := symmetricAction_centralSign a.val c

theorem action_signKernel (a : A) (x : Model) (hx : x ∈ signKernel) :
    action a x = x := by
  have he : x = centralSign x.sign := Model.ext rfl ((mem_signKernel x).mp hx)
  rw [he, action_centralSign]

@[simp] theorem volumeVector_apply (i : Fin 6) : volumeVector.val i = 1 := by
  fin_cases i <;> rfl

@[simp] theorem permuteVector_volumeVector (p : Equiv.Perm (Fin 6)) :
    permuteVector p volumeVector = volumeVector := by
  apply Subtype.ext
  funext i
  change volumeVector.val (p.symm i) = volumeVector.val i
  simp only [volumeVector_apply]

theorem signedCorrection_volumeVector (a : A) : signedCorrection a.val volumeVector = 0 := by
  let f : A →* Multiplicative F :=
    { toFun a := Multiplicative.ofAdd (signedCorrection a.val volumeVector)
      map_one' := by change signedCorrection 1 volumeVector = 0; exact signedCorrection_one _
      map_mul' a b := by
        change signedCorrection (a.val * b.val) volumeVector =
          signedCorrection a.val volumeVector + signedCorrection b.val volumeVector
        rw [signedCorrection_comp, permuteVector_volumeVector, add_comm] }
  have hc : commutator A = ⊤ := commutator_alternatingGroup_eq_top (by simp)
  have ha : a ∈ commutator A := by rw [hc]; exact Subgroup.mem_top a
  exact Abelianization.commutator_subset_ker f ha

@[simp] theorem action_volume (a : A) : action a volume = volume := by
  apply Model.ext
  · change 0 + signedCorrection a.val volumeVector = 0
    rw [signedCorrection_volumeVector, zero_add]
  · exact permuteVector_volumeVector a.val

theorem action_projection (a : A) (x : Model) :
    projection (action a x) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) a.val (projection x).toAdd) := rfl

theorem action_naturalProjection (a : A) (x : Model) :
    (naturalProjection (action a x)).toAdd =
      naturalRepresentation (Fin 6) a.val (naturalProjection x).toAdd :=
  signedTo_naturalProjection a.val x

/-- The subgroup generated by the literal action displacements. -/
def displacements : Subgroup Model :=
  Subgroup.closure {y | ∃ a : A, ∃ x : Model, y = action a x * x⁻¹}

theorem displacements_eq_top : displacements = ⊤ := by
  apply eq_top_of_projection
  let H := displacements.map projection
  let W : Submodule F V :=
    { carrier := {v | Multiplicative.ofAdd v ∈ H}
      zero_mem' := H.one_mem
      add_mem' := fun hx hy => H.mul_mem hx hy
      smul_mem' := by
        intro c v hv
        change Multiplicative.ofAdd (c • v) ∈ H
        have hc : ∀ c : F, c = 0 ∨ c = 1 := by decide
        rcases hc c with rfl | rfl
        · rw [zero_smul]
          exact H.one_mem
        · rw [one_smul]
          exact hv }
  have hw : Representation.Coinvariants.ker (alternatingCoreRepresentation (Fin 6)) ≤ W := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a, v⟩, rfl⟩
    change Multiplicative.ofAdd (alternatingCoreRepresentation (Fin 6) a v - v) ∈ H
    refine ⟨action a ⟨0, v⟩ * (⟨0, v⟩ : Model)⁻¹,
      Subgroup.subset_closure ⟨a, ⟨0, v⟩, rfl⟩, ?_⟩
    rw [map_mul, map_inv, action_projection]
    change Multiplicative.ofAdd (coreRepresentation (Fin 6) a.val v + -v) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) a.val v - v)
    rw [sub_eq_add_neg]
  rw [alternatingSix_core_generated] at hw
  apply top_unique
  intro v _
  exact hw (Submodule.mem_top : v.toAdd ∈ (⊤ : Submodule F V))

/-- Precomposition retains the chosen automorphism of the actor explicitly. -/
def precomposedAction (e : MulAut A) : A →* MulAut Model := action.comp e.toMonoidHom

@[simp] theorem precomposedAction_apply (e : MulAut A) (a : A) (x : Model) :
    precomposedAction e a x = action (e a) x := rfl

theorem precomposedAction_projection (e : MulAut A) (a : A) (x : Model) :
    projection (precomposedAction e a x) =
      Multiplicative.ofAdd (coreRepresentation (Fin 6) (e a).val (projection x).toAdd) := rfl

theorem precomposedAction_naturalProjection (e : MulAut A) (a : A) (x : Model) :
    (naturalProjection (precomposedAction e a x)).toAdd =
      naturalRepresentation (Fin 6) (e a).val (naturalProjection x).toAdd :=
  action_naturalProjection (e a) x

@[simp] theorem precomposedAction_volume (e : MulAut A) (a : A) :
    precomposedAction e a volume = volume := action_volume (e a)

theorem precomposedAction_signKernel (e : MulAut A) (a : A) (x : Model)
    (hx : x ∈ signKernel) : precomposedAction e a x = x := action_signKernel (e a) x hx

theorem precomposedAction_displacements_eq_top (e : MulAut A) :
    Subgroup.closure {y | ∃ a : A, ∃ x : Model, y = precomposedAction e a x * x⁻¹} = ⊤ := by
  have hs : {y | ∃ a : A, ∃ x : Model, y = precomposedAction e a x * x⁻¹} =
      {y | ∃ a : A, ∃ x : Model, y = action a x * x⁻¹} := by
    ext y
    constructor
    · rintro ⟨a, x, rfl⟩
      exact ⟨e a, x, rfl⟩
    · rintro ⟨a, x, rfl⟩
      exact ⟨e.symm a, x, by simp⟩
  rw [hs]
  exact displacements_eq_top

end EvenCliffordSix
