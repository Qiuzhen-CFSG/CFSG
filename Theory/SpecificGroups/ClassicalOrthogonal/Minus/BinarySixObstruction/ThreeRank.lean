module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.BinarySixObstruction.Basic
public import Theory.Representation.OrthogonalFourMinusHermitianEquiv.Transport
public import Theory.Representation.OrthogonalNatural
public import Theory.GroupTheory.PrimeRankWitness

/-!
# Three independent rotations in the binary six-dimensional minus group

An explicit isometry writes the defining space as three anisotropic binary
planes. Each plane rotation has order three and is a commutator with a
reflection. Thus independent rotations embed `(C₃)³` in the actual commutator
subgroup. The characteristic-two scalar-kernel theorem shows that the literal
projective quotient preserves this embedding. A three-cycle of the planes,
also a commutator, gives an explicit noncommuting pair.

The finite checks concern at most 64 vectors or three rotations of a four-element
plane; they do not enumerate the ambient isometry group.

Source: the intrinsic rank obstruction for the orthogonal section in
Aschbacher--Smith A.2.15(2), A.2.19 (`refs/quasithin.pdf`, printed pp.37--41),
and GLS3 Table 5.3o. No exceptional unitary identification is used.
-/

@[expose] public noncomputable section

open scoped commutatorElement CharTwo

namespace ClassicalOrthogonal.Minus.BinarySixObstruction

abbrev Plane := F × F
abbrev V := Fin 3 → Plane
def threePlaneForm : QuadraticForm F V := QuadraticMap.pi (fun _ : Fin 3 => plane F 1)

/-- An explicit change from three anisotropic planes to two hyperbolic planes and one anisotropic plane. -/
def coordinates : V ≃ₗ[F] Space F 2 where
  toFun v := (![ ((v 0).1 + (v 0).2 + (v 1).2, (v 0).1 + (v 1).2),
                 ((v 0).2 + (v 1).1, (v 0).2 + (v 1).1 + (v 1).2)], v 2)
  invFun w := ![((w.1 0).2 + (w.1 1).1 + (w.1 1).2,
                (w.1 0).1 + (w.1 0).2),
               ((w.1 0).1 + (w.1 0).2 + (w.1 1).1,
                (w.1 1).1 + (w.1 1).2), w.2]
  left_inv v := by
    ext i <;> fin_cases i <;> simp [add_assoc, add_comm, add_left_comm]
  right_inv w := by
    apply Prod.ext
    · ext i <;> fin_cases i <;> simp [add_assoc, add_comm, add_left_comm]
    · rfl
  map_add' v w := by
    apply Prod.ext
    · ext i <;> fin_cases i <;> simp <;> ring
    · rfl
  map_smul' c v := by
    apply Prod.ext
    · ext i <;> fin_cases i <;> simp [smul_eq_mul] <;> ring
    · rfl

theorem coordinates_form (v : V) : quadraticForm F 3 (coordinates v) = threePlaneForm v := by
  simp only [quadraticForm, parameter_binary]
  exact (by decide : ∀ v : V, form F 2 1 (coordinates v) = threePlaneForm v) v

def coordinateIsometry : threePlaneForm.IsometryEquiv (quadraticForm F 3) where
  toLinearEquiv := coordinates
  map_app' := coordinates_form

def rotate (a : ZMod 3) (v : Plane) : Plane :=
  if a = 0 then v else if a = 1 then (v.2, v.1 + v.2) else (v.1 + v.2, v.1)

def rotation (a : ZMod 3) : Plane ≃ₗ[F] Plane where
  toFun := rotate a
  invFun := rotate (-a)
  left_inv := (by decide : ∀ a v, rotate (-a) (rotate a v) = v) a
  right_inv := (by decide : ∀ a v, rotate a (rotate (-a) v) = v) a
  map_add' := (by decide : ∀ a v w, rotate a (v + w) = rotate a v + rotate a w) a
  map_smul' := (by decide : ∀ a c v, rotate a (c • v) = c • rotate a v) a

theorem rotation_form (a : ZMod 3) (v : Plane) : plane F 1 (rotation a v) = plane F 1 v :=
  (by decide : ∀ a v, plane F 1 (rotation a v) = plane F 1 v) a v

def rotations : (Fin 3 → Multiplicative (ZMod 3)) →* Orthogonal F V threePlaneForm where
  toFun a := ⟨LinearEquiv.piCongrRight (fun i => rotation (a i).toAdd), by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    change (∑ i, plane F 1 (rotation (a i).toAdd (v i))) = ∑ i, plane F 1 (v i)
    simp only [rotation_form]⟩
  map_one' := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    funext i
    rfl
  map_mul' a b := by
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    funext i
    exact (by decide : ∀ a b v, rotate (a+b) v = rotate a (rotate b v)) _ _ _

def reflection : Orthogonal F V threePlaneForm :=
  ⟨LinearEquiv.piCongrRight (fun _ => LinearEquiv.prodComm F F F), by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    change (∑ i, plane F 1 ((v i).2, (v i).1)) = ∑ i, plane F 1 (v i)
    apply Finset.sum_congr rfl
    intro i _
    exact (by decide : ∀ v : Plane, plane F 1 (v.2, v.1) = plane F 1 v) (v i)⟩

theorem rotations_commutator (a : Fin 3 → Multiplicative (ZMod 3)) :
    ⁅reflection, rotations a⁆ = rotations a := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  funext i
  change Prod.swap (rotate (a i).toAdd (Prod.swap (rotate (-(a i).toAdd) (v i)))) =
    rotate (a i).toAdd (v i)
  exact (by decide : ∀ a v, Prod.swap (rotate a (Prod.swap (rotate (-a) v))) = rotate a v) _ _

/-- Every independent rotation is a commutator with the simultaneous reflection. -/
def rotationsOmega : (Fin 3 → Multiplicative (ZMod 3)) →* Omega F V threePlaneForm :=
  rotations.codRestrict _ (fun a => by
    rw [← rotations_commutator a]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem rotationsOmega_injective : Function.Injective rotationsOmega := by
  intro a b h
  funext i
  have hv := congrArg (fun g : Omega F V threePlaneForm => g.val.val (fun _ => (1,0)) i) h
  change rotate (a i).toAdd (1,0) = rotate (b i).toAdd (1,0) at hv
  exact congrArg Multiplicative.ofAdd
    ((by decide : Function.Injective (fun a : ZMod 3 => rotate a (1,0))) hv)

/-- The elementary abelian group of order 27 in the literal orthogonal commutator group. -/
def embedding : (Fin 3 → Multiplicative (ZMod 3)) →*
    Omega F (Space F 2) (quadraticForm F 3) :=
  (Representation.OrthogonalFourMinus.HermitianEquiv.omegaCongr coordinateIsometry).toMonoidHom.comp
    rotationsOmega

theorem embedding_injective : Function.Injective embedding :=
  (Representation.OrthogonalFourMinus.HermitianEquiv.omegaCongr coordinateIsometry).injective.comp
    rotationsOmega_injective

def projectiveEmbedding : (Fin 3 → Multiplicative (ZMod 3)) →*
    ClassicalGroup.POmegaMinus 3 F :=
  (minusProjectiveEquiv (F := F) 3).toMonoidHom.comp embedding

/-- This is the literal scalar quotient map on the constructed subgroup. -/
theorem projectiveEmbedding_apply (a : Fin 3 → Multiplicative (ZMod 3)) :
    projectiveEmbedding a =
      QuotientGroup.mk' (scalarSubgroup F NaturalSpace naturalForm) (embedding a) := rfl

/-- No element of the elementary abelian subgroup is lost in the scalar quotient. -/
theorem projectiveEmbedding_injective : Function.Injective projectiveEmbedding :=
  (minusProjectiveEquiv (F := F) 3).injective.comp embedding_injective

/-- The actual scalar quotient has 3-rank at least three. -/
theorem primeRank_three_ge : 3 ≤ primeRank 3 (ClassicalGroup.POmegaMinus 3 F) := by
  have hp : ∀ a : Fin 3 → Multiplicative (ZMod 3), a ^ 3 = 1 := by
    intro a
    funext i
    change Multiplicative.ofAdd (3 • (a i).toAdd) = Multiplicative.ofAdd 0
    exact congrArg Multiplicative.ofAdd (ZModModule.char_nsmul_eq_zero 3 (a i).toAdd)
  exact primeRank_ge_of_elementary_embedding hp (by simp [Nat.card_eq_fintype_card])
    projectiveEmbedding projectiveEmbedding_injective

def permute (p : Equiv.Perm (Fin 3)) : Orthogonal F V threePlaneForm :=
  ⟨LinearEquiv.piCongrLeft' F (fun _ : Fin 3 => Plane) p, by
    apply (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup _ _).mpr
    intro v
    change (∑ i, plane F 1 (v (p.symm i))) = ∑ i, plane F 1 (v i)
    exact Equiv.sum_comp p.symm (fun i => plane F 1 (v i))⟩

/-- A three-cycle of the anisotropic planes, expressed as a commutator of swaps. -/
def cycleOmega : Omega F V threePlaneForm :=
  ⟨⁅permute (Equiv.swap 0 1), permute (Equiv.swap 1 2)⁆,
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)⟩

/-- A plane rotation and a cyclic permutation of the planes do not commute. -/
theorem omega_not_isMulCommutative : ¬ IsMulCommutative (Omega F V threePlaneForm) := by
  intro h
  let := h
  open scoped IsMulCommutative in
    have he := mul_comm (rotationsOmega ![Multiplicative.ofAdd 1, 1, 1]) cycleOmega
  have hv := congrArg (fun g : Omega F V threePlaneForm => g.val.val (fun _ => (1,0)) 0) he
  have hn : (rotationsOmega ![Multiplicative.ofAdd 1, 1, 1] * cycleOmega).val.val
      (fun _ => (1,0)) 0 ≠
      (cycleOmega * rotationsOmega ![Multiplicative.ofAdd 1, 1, 1]).val.val
      (fun _ => (1,0)) 0 := by decide
  exact hn hv

/-- Noncommutativity survives the literal scalar quotient. -/
theorem not_isMulCommutative : ¬ IsMulCommutative (ClassicalGroup.POmegaMinus 3 F) := by
  intro h
  let e := (Representation.OrthogonalFourMinus.HermitianEquiv.omegaCongr coordinateIsometry).trans
    (minusProjectiveEquiv (F := F) 3)
  apply omega_not_isMulCommutative
  exact IsMulCommutative.of_comm (fun a b => e.injective (by
    rw [e.map_mul, e.map_mul]
    exact (isMulCommutative_iff.mp h) _ _))
/-- The lower bound needed in the quasithin section obstruction. -/
theorem two_lt_primeRank_three : 2 < primeRank 3 (ClassicalGroup.POmegaMinus 3 F) :=
  lt_of_lt_of_le (by decide) primeRank_three_ge

end ClassicalOrthogonal.Minus.BinarySixObstruction
