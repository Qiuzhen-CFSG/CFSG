module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.Quasithin
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Fixed radicals of two-subgroups in Hermitian four-space

For a nonidentity two-subgroup R, faithfulness makes its common fixed space
proper. Its Hermitian perpendicular is therefore nonzero and R-invariant.
A two-group in characteristic two fixes a nonzero vector on that perpendicular,
so W = C_V(R) ∩ C_V(R)^⊥ is nonzero. The whole normalizer stabilizes W,
which is totally isotropic and hence has dimension one or two.

The pairing uses the stored involution and Gram matrix of an arbitrary
nondegenerate Hermitian four-space. We also identify the exact stabilizers
with the coordinate parabolics in `UnitaryFourFlag` and prove their conjugacy
under actual special-unitary matrices. Existence of a matrix moving an
arbitrary isotropic line or plane to coordinates is a separate obligation.

Source: GLS3, chapter 3, printed p.115, the classical fixed-space proof of
Borel–Tits 3.1.3(a), in `refs/KGroup/GLS3/chapter3.tex`. The implementation
adapts `FiveIsotropicGeometry` to arbitrary four-dimensional Gram matrices.
-/

open BenderSuzuki.MatrixGroups Matrix
open scoped Pointwise
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
variable {F : Type*} [Field F] (J : HermitianForm 4 F)

/-- The natural matrix action of SU on the vector space. -/
def linearAction : J.specialSubgroup →*
    ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 4 → F)).toMonoidHom.comp
    Matrix.GeneralLinearGroup.toLin.toMonoidHom).comp J.specialSubgroup.subtype

/-- Exact stabilizer of a subspace inside the special unitary group. -/
def specialStabilizer (W : Submodule F (Fin 4 → F)) :
    Subgroup J.specialSubgroup :=
  (MulAction.stabilizer ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) W).comap (linearAction J)

/-- Stabilizer membership is the usual preservation condition on matrix vectors. -/
theorem mem_specialStabilizer_iff
    (W : Submodule F (Fin 4 → F)) (A : J.specialSubgroup) :
    A ∈ specialStabilizer J W ↔
      ∀ v, (A.val : Matrix (Fin 4) (Fin 4) F) *ᵥ v ∈ W ↔ v ∈ W := by
  change linearAction J A ∈ MulAction.stabilizer _ W ↔ _
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set]
  rfl

private theorem conj_conj (x : F) : J.conj (J.conj x) = x := J.conj_involutive x

/-- The pairing for the actual stored involution and Gram matrix. -/
def pairing (v w : Fin 4 → F) : F := (fun i => J.conj (v i)) ⬝ᵥ (J.form *ᵥ w)

lemma pairing_add_left (u v w : Fin 4 → F) :
    pairing J (u + v) w = pairing J u w + pairing J v w := by
  simp only [pairing, Pi.add_apply, map_add, ← Pi.add_def, add_dotProduct]

lemma pairing_add_right (u v w : Fin 4 → F) :
    pairing J u (v + w) = pairing J u v + pairing J u w := by
  simp only [pairing, mulVec_add, dotProduct_add]

lemma pairing_smul_left (a : F) (v w : Fin 4 → F) :
    pairing J (a • v) w = J.conj a * pairing J v w := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, map_mul]
  exact smul_dotProduct (J.conj a) (fun i => J.conj (v i)) _

lemma pairing_smul_right (a : F) (v w : Fin 4 → F) :
    pairing J v (a • w) = a * pairing J v w := by
  simp only [pairing, mulVec_smul, dotProduct_smul, smul_eq_mul]

@[simp] lemma pairing_zero_left (w : Fin 4 → F) : pairing J 0 w = 0 := by
  simp [pairing]

@[simp] lemma pairing_zero_right (w : Fin 4 → F) : pairing J w 0 = 0 := by
  simp [pairing]

lemma pairing_conj (v w : Fin 4 → F) : J.conj (pairing J v w) = pairing J w v := by
  simp only [pairing, dotProduct, mulVec, map_sum, map_mul,
    J.form_hermitian, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [J.conj_involutive (v j)]
  ring

lemma pairing_nondegenerate (v : Fin 4 → F) (h : ∀ w, pairing J w v = 0) : v = 0 := by
  have hv : J.form *ᵥ v = 0 := by
    ext i
    have hi := h (Pi.single i 1)
    simpa [pairing, dotProduct, Pi.single_apply, apply_ite] using hi
  exact Matrix.eq_zero_of_mulVec_eq_zero J.form_nondegenerate hv

/-- The functional defined by the second argument of the stored Hermitian form. -/
def pairingMap (v : Fin 4 → F) : (Fin 4 → F) →ₗ[F] F where
  toFun := pairing J v
  map_add' := pairing_add_right J v
  map_smul' a w := pairing_smul_right J a v w

/-- Right Hermitian perpendicular for the stored Hermitian pairing. -/
def orthogonal (W : Submodule F (Fin 4 → F)) : Submodule F (Fin 4 → F) where
  carrier := {v | ∀ w ∈ W, pairing J w v = 0}
  zero_mem' := by simp [pairing]
  add_mem' := by
    intro v w hv hw x hx
    change (fun i => J.conj (x i)) ⬝ᵥ (J.form *ᵥ (v + w)) = 0
    rw [mulVec_add, dotProduct_add, show (fun i => J.conj (x i)) ⬝ᵥ (J.form *ᵥ v) = 0 from hv x hx,
      show (fun i => J.conj (x i)) ⬝ᵥ (J.form *ᵥ w) = 0 from hw x hx, add_zero]
  smul_mem' := by
    intro c v hv w hw
    change (fun i => J.conj (w i)) ⬝ᵥ (J.form *ᵥ (c • v)) = 0
    rw [mulVec_smul, dotProduct_smul, show (fun i => J.conj (w i)) ⬝ᵥ (J.form *ᵥ v) = 0 from hv w hw, smul_zero]

private def conjugateSpace (W : Submodule F (Fin 4 → F)) :
    Submodule F (Fin 4 → F) where
  carrier := {v | (fun i => J.conj (v i)) ∈ W}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, Pi.zero_apply, map_zero]
    exact W.zero_mem
  add_mem' := by
    intro v w hv hw
    simpa only [Set.mem_ofPred_eq, Pi.add_apply, map_add, Pi.add_def] using W.add_mem hv hw
  smul_mem' := by
    intro c v hv
    simpa only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_def] using W.smul_mem (J.conj c) hv

private def conjugateSpaceEquiv (W : Submodule F (Fin 4 → F)) :
    W ≃ conjugateSpace J W where
  toFun v := ⟨fun i => J.conj (v.val i), by
    change (fun i => J.conj (J.conj (v.val i))) ∈ W
    simpa only [conj_conj] using v.property⟩
  invFun v := ⟨fun i => J.conj (v.val i), v.property⟩
  left_inv v := Subtype.ext (funext fun i => J.conj_involutive (v.val i))
  right_inv v := Subtype.ext (funext fun i => J.conj_involutive (v.val i))

private theorem finrank_conjugateSpace [Finite F] (W : Submodule F (Fin 4 → F)) :
    Module.finrank F (conjugateSpace J W) = Module.finrank F W := by
  have h := Nat.card_congr (conjugateSpaceEquiv J W)
  rw [Module.natCard_eq_pow_finrank (K := F) (V := W),
    Module.natCard_eq_pow_finrank (K := F) (V := conjugateSpace J W)] at h
  let : Fintype F := Fintype.ofFinite F
  have hc : 1 < Nat.card F := by simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
  exact (Nat.pow_right_injective hc h).symm

private theorem orthogonal_eq (W : Submodule F (Fin 4 → F)) :
    orthogonal J W = LinearMap.BilinForm.orthogonal
      J.form.toBilin' (conjugateSpace J W) := by
  ext v
  constructor
  · intro hv w hw
    have h := hv (fun i => J.conj (w i)) hw
    rw [Matrix.toBilin'_apply']
    simpa only [pairing, conj_conj] using h
  · intro hv w hw
    have h := hv (fun i => J.conj (w i)) (by
      change (fun i => J.conj (J.conj (w i))) ∈ W
      simpa only [conj_conj] using hw)
    simpa only [Matrix.toBilin'_apply', pairing] using h

/-- Perpendicular dimension for the actual stored involution. -/
theorem finrank_orthogonal [Finite F] (W : Submodule F (Fin 4 → F)) :
    Module.finrank F (orthogonal J W) = 4 - Module.finrank F W := by
  rw [orthogonal_eq, LinearMap.BilinForm.finrank_orthogonal
      (LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' J.form J.form_nondegenerate),
    finrank_conjugateSpace]
  simp

/-- In dimension four every nonzero totally isotropic subspace is a line or a plane. -/
theorem finrank_one_or_two [Finite F] (W : Submodule F (Fin 4 → F))
    (hne : W ≠ ⊥) (hW : W ≤ orthogonal J W) :
    Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by
  have h := Submodule.finrank_mono hW
  rw [finrank_orthogonal] at h
  have hn : Module.finrank F W ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
  omega

/-- SU preserves the pairing for its stored Hermitian form. -/
theorem pairing_action (g : J.specialSubgroup) (v w : Fin 4 → F) :
    pairing J (linearAction J g v) (linearAction J g w) = pairing J v w := by
  have hg := (J.mem_specialSubgroup_iff g.val).mp g.property |>.1
  change (fun i => J.conj ((g.val.val *ᵥ v) i)) ⬝ᵥ (J.form *ᵥ (g.val.val *ᵥ w)) = _
  rw [show (fun i => J.conj ((g.val.val *ᵥ v) i)) =
    (g.val.val.map J.conj) *ᵥ (fun i => J.conj (v i)) from
      funext (RingHom.map_mulVec J.conj.toRingHom g.val.val v)]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  change (fun i => J.conj (v i)) ⬝ᵥ (J.conjTranspose g.val.val * J.form * g.val.val) *ᵥ w = _
  rw [hg]
  rfl

/-- Forward preservation suffices for membership in the exact SU stabilizer. -/
theorem mem_specialStabilizer_of_preserves [Finite F]
    (W : Submodule F (Fin 4 → F)) (g : J.specialSubgroup)
    (h : ∀ v ∈ W, linearAction J g v ∈ W) : g ∈ specialStabilizer J W := by
  change linearAction J g ∈ MulAction.stabilizer _ W
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set_iff_smul_set_subset
    (Set.toFinite (W : Set (Fin 4 → F)))]
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

/-- A stabilizer also preserves the Hermitian perpendicular. -/
theorem specialStabilizer_le_orthogonal [Finite F]
    (W : Submodule F (Fin 4 → F)) :
    specialStabilizer J W ≤ specialStabilizer J (orthogonal J W) := by
  intro g hg
  apply mem_specialStabilizer_of_preserves
  intro v hv w hw
  have hi := (mem_specialStabilizer_iff J W (g⁻¹)).mp ((specialStabilizer J W).inv_mem hg)
  have hw' := hv _ ((hi w).mpr hw)
  have he := pairing_action J g (linearAction J (g⁻¹) w) v
  have hew : linearAction J g (linearAction J (g⁻¹) w) = w := by
    rw [map_inv]
    exact (linearAction J g).apply_symm_apply w
  rw [hew] at he
  exact he.trans hw'

/-- The common fixed space of a matrix subgroup. -/
def fixedSpace (Q : Subgroup J.specialSubgroup) : Submodule F (Fin 4 → F) where
  carrier := {v | ∀ q ∈ Q, linearAction J q v = v}
  zero_mem' := by intro q hq; exact map_zero _
  add_mem' := by intro v w hv hw q hq; rw [map_add, hv q hq, hw q hq]
  smul_mem' := by intro c v hv q hq; rw [map_smul, hv q hq]

/-- The radical of the restriction to the common fixed space. -/
def fixedRadical (Q : Subgroup J.specialSubgroup) : Submodule F (Fin 4 → F) :=
  fixedSpace J Q ⊓ orthogonal J (fixedSpace J Q)

/-- The normalizer preserves the common fixed space. -/
theorem normalizer_le_fixedSpace_stabilizer [Finite F] (Q : Subgroup J.specialSubgroup) :
    Subgroup.normalizer (Q : Set J.specialSubgroup) ≤ specialStabilizer J (fixedSpace J Q) := by
  intro g hg
  apply mem_specialStabilizer_of_preserves
  intro v hv q hq
  have hq' : g⁻¹ * q * g ∈ Q := (Subgroup.mem_normalizer_iff''.mp hg q).mp hq
  have h := congrArg (linearAction J g) (hv _ hq')
  simpa only [map_mul, map_inv, LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using h

/-- The full normalizer preserves the fixed radical. -/
theorem normalizer_le_fixedRadical_stabilizer [Finite F]
    (Q : Subgroup J.specialSubgroup) :
    Subgroup.normalizer (Q : Set J.specialSubgroup) ≤ specialStabilizer J (fixedRadical J Q) := by
  intro g hg
  have hf := normalizer_le_fixedSpace_stabilizer J Q hg
  have ho := specialStabilizer_le_orthogonal J (fixedSpace J Q) hf
  apply mem_specialStabilizer_of_preserves
  intro v hv
  exact ⟨((mem_specialStabilizer_iff J _ g).mp hf v).mpr hv.1,
    ((mem_specialStabilizer_iff J _ g).mp ho v).mpr hv.2⟩

private theorem fixedSpace_ne_top (Q : Subgroup J.specialSubgroup) (hQ : Q ≠ ⊥) :
    fixedSpace J Q ≠ ⊤ := by
  intro h
  apply hQ
  apply le_antisymm _ bot_le
  change ∀ q ∈ Q, q = 1
  intro q hq
  apply Subtype.ext
  apply Units.ext
  apply Matrix.ext
  intro i j
  have hx : Pi.single j (1 : F) ∈ fixedSpace J Q := by rw [h]; trivial
  have he := congrFun (hx q hq) i
  change (q.val.val *ᵥ Pi.single j 1) i = (Pi.single j (1 : F) : Fin 4 → F) i at he
  simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using he

/-- The radical is totally isotropic. -/
theorem fixedRadical_isotropic (Q : Subgroup J.specialSubgroup) :
    fixedRadical J Q ≤ orthogonal J (fixedRadical J Q) := by
  intro v hv w hw
  exact hv.2 w hw.1

/-- A nonidentity two-subgroup has a nonzero fixed radical. -/
theorem fixedRadical_ne_bot [Finite F] [CharP F 2]
    (Q : Subgroup J.specialSubgroup) (hQ : Q ≠ ⊥) (hp : IsPGroup 2 Q) :
    fixedRadical J Q ≠ ⊥ := by
  let : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
  let W := orthogonal J (fixedSpace J Q)
  have hd : 0 < Module.finrank F W := by
    rw [finrank_orthogonal]
    have h := Submodule.finrank_lt (fixedSpace_ne_top J Q hQ)
    simpa using Nat.sub_pos_of_lt h
  let : Nontrivial W := Module.nontrivial_of_finrank_pos hd
  let ρ : Representation F Q (Fin 4 → F) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linearAction J)).comp Q.subtype
  have hW : ∀ q : Q, W ≤ W.comap (ρ q) := by
    intro q x hx
    have hn : (q : J.specialSubgroup) ∈ Subgroup.normalizer (Q : Set J.specialSubgroup) :=
      Subgroup.le_normalizer q.property
    have hs := specialStabilizer_le_orthogonal J (fixedSpace J Q)
      (normalizer_le_fixedSpace_stabilizer J Q hn)
    exact ((mem_specialStabilizer_iff J W q).mp hs x).mpr hx
  have hc : ringChar F = 2 := ringChar.eq F 2
  obtain ⟨v, hv, hfix⟩ := Representation.pGroup_fix_nonzero_vector
    (F := F) (by omega) (by rwa [hc]) (ρ.subrepresentation W hW)
  have hvfix : v.val ∈ fixedSpace J Q := by
    intro q hq
    exact congrArg Subtype.val (hfix ⟨q, hq⟩)
  intro hbot
  have hvzero : v.val = 0 := by
    have hm : v.val ∈ fixedRadical J Q := ⟨hvfix, v.property⟩
    rwa [hbot, Submodule.mem_bot] at hm
  exact hv (Subtype.ext hvzero)

/-- Every SU two-local stabilizes a nonzero totally isotropic line or plane. -/
theorem twoLocal_stabilizes_isotropic [Finite F] [CharP F 2]
    (M : Subgroup J.specialSubgroup) (hM : IsTwoLocal M) :
    ∃ W : Submodule F (Fin 4 → F), W ≠ ⊥ ∧ W ≤ orthogonal J W ∧
      (Module.finrank F W = 1 ∨ Module.finrank F W = 2) ∧ M ≤ specialStabilizer J W := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  have hn := fixedRadical_ne_bot J Q hQ hp
  have hi := fixedRadical_isotropic J Q
  exact ⟨fixedRadical J Q, hn, hi, finrank_one_or_two J _ hn hi,
    normalizer_le_fixedRadical_stabilizer J Q⟩

/-- Moving a subspace by an SU matrix conjugates its exact stabilizer. -/
theorem specialStabilizer_map_action (g : J.specialSubgroup) (W : Submodule F (Fin 4 → F)) :
    specialStabilizer J (W.map (linearAction J g).toLinearMap) =
      (specialStabilizer J W).map (MulAut.conj g).toMonoidHom := by
  change (MulAction.stabilizer ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F))
    (linearAction J g • W)).comap (linearAction J) = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext a
  simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv]
  change (linearAction J g)⁻¹ * linearAction J a * linearAction J g ∈
      MulAction.stabilizer _ W ↔
    linearAction J (g⁻¹ * a * g) ∈ MulAction.stabilizer _ W
  rw [map_mul, map_mul, map_inv]


/-- The abstract stabilizer agrees with the existing full coordinate point parabolic. -/
theorem specialStabilizer_point [Finite F] [CharP F 2] :
    specialStabilizer J (UnitaryFourFlag.pointSpace F) =
      UnitaryFourFlag.pointParabolicSU F J := by
  ext g
  rw [mem_specialStabilizer_iff]
  change _ ↔ g.val ∈ MulAction.stabilizer (GL (Fin 4) F)
    (UnitaryFourFlag.pointSpace F : Set (Fin 4 → F))
  rw [MulAction.mem_stabilizer_set]
  rfl

/-- The abstract stabilizer agrees with the existing full coordinate plane parabolic. -/
theorem specialStabilizer_plane [Finite F] [CharP F 2] :
    specialStabilizer J (UnitaryFourFlag.planeSpace F) =
      UnitaryFourFlag.planeParabolicSU F J := by
  ext g
  rw [mem_specialStabilizer_iff]
  change _ ↔ g.val ∈ MulAction.stabilizer (GL (Fin 4) F)
    (UnitaryFourFlag.planeSpace F : Set (Fin 4 → F))
  rw [MulAction.mem_stabilizer_set]
  rfl

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourConverse.TwoLocalCover
