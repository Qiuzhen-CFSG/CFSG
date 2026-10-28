module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Theory.Representation.TwoDimensionalOddOrder
public import Theory.GroupTheory.TwoLocalSurjective
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Isotropic stabilizers containing the two-locals of unitary five-space

For a nonidentity two-subgroup in characteristic two, the radical of its
common fixed space is nonzero. Indeed, faithfulness makes the fixed space
proper, so its Hermitian perpendicular is nonzero; a two-group fixes a
nonzero vector on that invariant perpendicular. The radical is totally
isotropic and invariant under the entire normalizer. Perpendicular dimensions
show that it is a line or a plane.

The general Sylow lifting theorem for finite-group surjections transfers
this placement from SU to its actual image in PGL. An exact stabilizer
conjugacy formula then reduces standard-parabolic coverage to SU
transitivity on isotropic subspaces. Transitivity and two-locality of the
standard parabolics are separate obligations, not asserted here.

The pairing uses the stored involution and the identity Gram matrix. These
results hold over every finite field of characteristic two; no cardinality
or fixed-field hypothesis is needed for this part of the argument.

Source: the standard defining-characteristic fixed-space argument for
classical groups, applied to Aschbacher--Smith, Theorem 0.1.2(1), printed
p.4 (Theorem 0.1.1(1), p.482), and the unitary-five parabolics of F.1.12(7),
pp.263--264, in `refs/quasithin.pdf`.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
open scoped Pointwise
namespace Theory.SpecificGroups.UnitaryFive.IsotropicGeometry
variable {F : Type*} [Field F] (J : HermitianForm 5 F)

private theorem conj_conj (x : F) : J.conj (J.conj x) = x := J.conj_involutive x

/-- The identity-Gram pairing for the stored field involution. -/
def pairing (v w : Fin 5 → F) : F := (fun i => J.conj (v i)) ⬝ᵥ w

/-- Right Hermitian perpendicular for the identity-Gram pairing. -/
def orthogonal (W : Submodule F (Fin 5 → F)) : Submodule F (Fin 5 → F) where
  carrier := {v | ∀ w ∈ W, pairing J w v = 0}
  zero_mem' := by simp [pairing]
  add_mem' := by
    intro v w hv hw x hx
    change (fun i => J.conj (x i)) ⬝ᵥ (v + w) = 0
    rw [dotProduct_add, show (fun i => J.conj (x i)) ⬝ᵥ v = 0 from hv x hx,
      show (fun i => J.conj (x i)) ⬝ᵥ w = 0 from hw x hx, add_zero]
  smul_mem' := by
    intro c v hv w hw
    change (fun i => J.conj (w i)) ⬝ᵥ (c • v) = 0
    rw [dotProduct_smul, show (fun i => J.conj (w i)) ⬝ᵥ v = 0 from hv w hw, smul_zero]

private def conjugateSpace (W : Submodule F (Fin 5 → F)) :
    Submodule F (Fin 5 → F) where
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

private def conjugateSpaceEquiv (W : Submodule F (Fin 5 → F)) :
    W ≃ conjugateSpace J W where
  toFun v := ⟨fun i => J.conj (v.val i), by
    change (fun i => J.conj (J.conj (v.val i))) ∈ W
    simpa only [conj_conj] using v.property⟩
  invFun v := ⟨fun i => J.conj (v.val i), v.property⟩
  left_inv v := Subtype.ext (funext fun i => J.conj_involutive (v.val i))
  right_inv v := Subtype.ext (funext fun i => J.conj_involutive (v.val i))

private theorem finrank_conjugateSpace [Finite F] (W : Submodule F (Fin 5 → F)) :
    Module.finrank F (conjugateSpace J W) = Module.finrank F W := by
  have h := Nat.card_congr (conjugateSpaceEquiv J W)
  rw [Module.natCard_eq_pow_finrank (K := F) (V := W),
    Module.natCard_eq_pow_finrank (K := F) (V := conjugateSpace J W)] at h
  let : Fintype F := Fintype.ofFinite F
  have hc : 1 < Nat.card F := by simpa only [Nat.card_eq_fintype_card] using Fintype.one_lt_card (α := F)
  exact (Nat.pow_right_injective hc h).symm

private theorem dotProduct_nondegenerate :
    (dotProductBilin F F : LinearMap.BilinForm F (Fin 5 → F)).Nondegenerate := by
  constructor
  · intro v hv
    exact dotProduct_eq_zero v hv
  · intro v hv
    exact dotProduct_eq_zero v (fun w => by
      simpa only [dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_comm] using hv w)

private theorem orthogonal_eq (W : Submodule F (Fin 5 → F)) :
    orthogonal J W = LinearMap.BilinForm.orthogonal
      (dotProductBilin F F : LinearMap.BilinForm F (Fin 5 → F)) (conjugateSpace J W) := by
  ext v
  constructor
  · intro hv w hw
    have h := hv (fun i => J.conj (w i)) hw
    change w ⬝ᵥ v = 0
    simpa only [pairing, conj_conj] using h
  · intro hv w hw
    exact hv (fun i => J.conj (w i)) (by
      change (fun i => J.conj (J.conj (w i))) ∈ W
      simpa only [conj_conj] using hw)

/-- Perpendicular dimension for the actual stored involution. -/
theorem finrank_orthogonal [Finite F] (W : Submodule F (Fin 5 → F)) :
    Module.finrank F (orthogonal J W) = 5 - Module.finrank F W := by
  rw [orthogonal_eq, LinearMap.BilinForm.finrank_orthogonal dotProduct_nondegenerate,
    finrank_conjugateSpace]
  simp

/-- In dimension five every nonzero totally isotropic subspace is a line or a plane. -/
theorem finrank_one_or_two [Finite F] (W : Submodule F (Fin 5 → F))
    (hne : W ≠ ⊥) (hW : W ≤ orthogonal J W) :
    Module.finrank F W = 1 ∨ Module.finrank F W = 2 := by
  have h := Submodule.finrank_mono hW
  rw [finrank_orthogonal] at h
  have hn : Module.finrank F W ≠ 0 := fun h => hne (Submodule.finrank_eq_zero.mp h)
  omega

/-- SU preserves the pairing when the stored matrix is the identity. -/
theorem pairing_action (hJ : J.form = 1) (g : J.specialSubgroup) (v w : Fin 5 → F) :
    pairing J (linearAction J g v) (linearAction J g w) = pairing J v w := by
  have hg := (J.mem_specialSubgroup_iff g.val).mp g.property |>.1
  rw [hJ, mul_one] at hg
  change (fun i => J.conj ((g.val.val *ᵥ v) i)) ⬝ᵥ (g.val.val *ᵥ w) = _
  rw [show (fun i => J.conj ((g.val.val *ᵥ v) i)) =
    (g.val.val.map J.conj) *ᵥ (fun i => J.conj (v i)) from
      funext (RingHom.map_mulVec J.conj.toRingHom g.val.val v)]
  rw [← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec]
  change (fun i => J.conj (v i)) ⬝ᵥ (J.conjTranspose g.val.val * g.val.val) *ᵥ w = _
  rw [hg, one_mulVec]
  rfl

/-- Forward preservation suffices for membership in the exact SU stabilizer. -/
theorem mem_specialStabilizer_of_preserves [Finite F]
    (W : Submodule F (Fin 5 → F)) (g : J.specialSubgroup)
    (h : ∀ v ∈ W, linearAction J g v ∈ W) : g ∈ specialStabilizer J W := by
  change linearAction J g ∈ MulAction.stabilizer _ W
  rw [Submodule.stabilizer_coe, MulAction.mem_stabilizer_set_iff_smul_set_subset
    (Set.toFinite (W : Set (Fin 5 → F)))]
  rintro _ ⟨v, hv, rfl⟩
  exact h v hv

/-- A stabilizer also preserves the Hermitian perpendicular. -/
theorem specialStabilizer_le_orthogonal [Finite F] (hJ : J.form = 1)
    (W : Submodule F (Fin 5 → F)) :
    specialStabilizer J W ≤ specialStabilizer J (orthogonal J W) := by
  intro g hg
  apply mem_specialStabilizer_of_preserves
  intro v hv w hw
  have hi := (mem_specialStabilizer_iff J W (g⁻¹)).mp ((specialStabilizer J W).inv_mem hg)
  have hw' := hv _ ((hi w).mpr hw)
  have he := pairing_action J hJ g (linearAction J (g⁻¹) w) v
  have hew : linearAction J g (linearAction J (g⁻¹) w) = w := by
    rw [map_inv]
    exact (linearAction J g).apply_symm_apply w
  rw [hew] at he
  exact he.trans hw'

/-- The common fixed space of a matrix subgroup. -/
def fixedSpace (Q : Subgroup J.specialSubgroup) : Submodule F (Fin 5 → F) where
  carrier := {v | ∀ q ∈ Q, linearAction J q v = v}
  zero_mem' := by intro q hq; exact map_zero _
  add_mem' := by intro v w hv hw q hq; rw [map_add, hv q hq, hw q hq]
  smul_mem' := by intro c v hv q hq; rw [map_smul, hv q hq]

/-- The radical of the restriction to the common fixed space. -/
def fixedRadical (Q : Subgroup J.specialSubgroup) : Submodule F (Fin 5 → F) :=
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
theorem normalizer_le_fixedRadical_stabilizer [Finite F] (hJ : J.form = 1)
    (Q : Subgroup J.specialSubgroup) :
    Subgroup.normalizer (Q : Set J.specialSubgroup) ≤ specialStabilizer J (fixedRadical J Q) := by
  intro g hg
  have hf := normalizer_le_fixedSpace_stabilizer J Q hg
  have ho := specialStabilizer_le_orthogonal J hJ (fixedSpace J Q) hf
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
  change (q.val.val *ᵥ Pi.single j 1) i = (Pi.single j (1 : F) : Fin 5 → F) i at he
  simpa [Matrix.mulVec_single, Pi.single_apply, Matrix.one_apply] using he

/-- The radical is totally isotropic. -/
theorem fixedRadical_isotropic (Q : Subgroup J.specialSubgroup) :
    fixedRadical J Q ≤ orthogonal J (fixedRadical J Q) := by
  intro v hv w hw
  exact hv.2 w hw.1

/-- A nonidentity two-subgroup has a nonzero fixed radical. -/
theorem fixedRadical_ne_bot [Finite F] [CharP F 2] (hJ : J.form = 1)
    (Q : Subgroup J.specialSubgroup) (hQ : Q ≠ ⊥) (hp : IsPGroup 2 Q) :
    fixedRadical J Q ≠ ⊥ := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  let W := orthogonal J (fixedSpace J Q)
  have hd : 0 < Module.finrank F W := by
    rw [finrank_orthogonal]
    have h := Submodule.finrank_lt (fixedSpace_ne_top J Q hQ)
    simpa using Nat.sub_pos_of_lt h
  let : Nontrivial W := Module.nontrivial_of_finrank_pos hd
  let ρ : Representation F Q (Fin 5 → F) :=
    (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (linearAction J)).comp Q.subtype
  have hW : ∀ q : Q, W ≤ W.comap (ρ q) := by
    intro q x hx
    have hn : (q : J.specialSubgroup) ∈ Subgroup.normalizer (Q : Set J.specialSubgroup) :=
      Subgroup.le_normalizer q.property
    have hs := specialStabilizer_le_orthogonal J hJ (fixedSpace J Q)
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
theorem twoLocal_stabilizes_isotropic [Finite F] [CharP F 2] (hJ : J.form = 1)
    (M : Subgroup J.specialSubgroup) (hM : IsTwoLocal M) :
    ∃ W : Submodule F (Fin 5 → F), W ≠ ⊥ ∧ W ≤ orthogonal J W ∧
      (Module.finrank F W = 1 ∨ Module.finrank F W = 2) ∧ M ≤ specialStabilizer J W := by
  obtain ⟨Q, hQ, hp, rfl⟩ := hM
  have hn := fixedRadical_ne_bot J hJ Q hQ hp
  have hi := fixedRadical_isotropic J Q
  exact ⟨fixedRadical J Q, hn, hi, finrank_one_or_two J _ hn hi,
    normalizer_le_fixedRadical_stabilizer J hJ Q⟩

/-- Projective two-locals lie in actual isotropic stabilizers. The lift uses
Sylow conjugacy through the surjection, so no splitting assumption is needed. -/
theorem projective_twoLocal_stabilizes_isotropic [Finite F] [CharP F 2] (hJ : J.form = 1)
    (M : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hM : IsTwoLocal M) :
    ∃ W : Submodule F (Fin 5 → F), W ≠ ⊥ ∧ W ≤ orthogonal J W ∧
      (Module.finrank F W = 1 ∨ Module.finrank F W = 2) ∧ M ≤ parabolic J W := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  obtain ⟨L, hL, hLM⟩ := hM.exists_map_eq_of_surjective (project J) (project_surjective J)
  obtain ⟨W, hn, hi, hd, hL⟩ := twoLocal_stabilizes_isotropic J hJ L hL
  exact ⟨W, hn, hi, hd, hLM ▸ Subgroup.map_mono hL⟩
/-- Moving a subspace by an SU matrix conjugates its exact stabilizer. -/
theorem specialStabilizer_map_action (g : J.specialSubgroup) (W : Submodule F (Fin 5 → F)) :
    specialStabilizer J (W.map (linearAction J g).toLinearMap) =
      (specialStabilizer J W).map (MulAut.conj g).toMonoidHom := by
  change (MulAction.stabilizer ((Fin 5 → F) ≃ₗ[F] (Fin 5 → F))
    (linearAction J g • W)).comap (linearAction J) = _
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  ext a
  simp only [Subgroup.mem_comap, Subgroup.mem_map_equiv]
  change (linearAction J g)⁻¹ * linearAction J a * linearAction J g ∈
      MulAction.stabilizer _ W ↔
    linearAction J (g⁻¹ * a * g) ∈ MulAction.stabilizer _ W
  rw [map_mul, map_mul, map_inv]

/-- The conjugacy of stabilizers descends to their actual images in PGL. -/
theorem parabolic_map_action (g : J.specialSubgroup) (W : Submodule F (Fin 5 → F)) :
    parabolic J (W.map (linearAction J g).toLinearMap) =
      (parabolic J W).map (MulAut.conj (project J g)).toMonoidHom := by
  have hcomm : (project J).comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (project J g)).toMonoidHom.comp (project J) := by
    ext a
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      MulAut.conj_apply, map_mul, map_inv]
  rw [parabolic, specialStabilizer_map_action, Subgroup.map_map, hcomm,
    ← Subgroup.map_map]
  rfl

end Theory.SpecificGroups.UnitaryFive.IsotropicGeometry
