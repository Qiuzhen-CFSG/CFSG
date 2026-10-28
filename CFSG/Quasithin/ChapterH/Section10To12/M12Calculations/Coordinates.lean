module

public import CFSG.Quasithin.ChapterH.Section10To12.Defs
public import Theory.Representation.BinaryPermutation.OffenderFixedSpace
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Tactic.Ring

/-!
# Coordinates on the ten-dimensional M₁₂ permutation heart

An even word modulo constants has a unique representative whose coordinate 10
is zero. Its first ten coordinates determine coordinate 11 by augmentation.
This gives a linear equivalence with ten binary coordinates and explicit
matrices for the native permutation action. Their ranks are the actual fixed
codimensions on the quotient heart.

These coordinates support the module calculations in Aschbacher–Smith H.11.1,
printed pp.392–393, combined manuscript of 1 March 2004. Only the residual M₁₂
acts by twelve-letter permutations; no outer action is asserted here.
-/

@[expose] public section
open BinaryPermutation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

abbrev Coordinates := Fin 10 → ZMod 2

def lift : Coordinates →ₗ[ZMod 2] Full (Fin 12) where
  toFun v := Fin.snoc (Fin.snoc v 0) (-∑ i, v i)
  map_add' u v := by
    ext i
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Pi.add_apply, Finset.sum_add_distrib,
        neg_add, add_zero]
  map_smul' c v := by
    ext i
    refine Fin.lastCases ?_ (fun j => Fin.lastCases ?_ (fun k => ?_) j) i <;>
      simp only [Fin.snoc_last, Fin.snoc_castSucc, Pi.smul_apply, smul_eq_mul,
        Finset.mul_sum, mul_neg, mul_zero, RingHom.id_apply]

theorem lift_mem_core (v : Coordinates) : lift v ∈ core (Fin 12) := by
  rw [mem_core]
  change (∑ i, Fin.snoc (Fin.snoc v 0) (-∑ j, v j) i) = 0
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, add_zero, add_neg_cancel]

def toHeart : Coordinates →ₗ[ZMod 2] M12Heart where
  toFun v := ⟨(constants (Fin 12)).mkQ (lift v), ⟨lift v, lift_mem_core v, rfl⟩⟩
  map_add' u v := by apply Subtype.ext; simp
  map_smul' c v := by apply Subtype.ext; simp

def projectFull : Full (Fin 12) →ₗ[ZMod 2] Coordinates where
  toFun v i := v i.castSucc.castSucc - v 10
  map_add' u v := by ext i; simp; ring
  map_smul' c v := by ext i; simp [mul_sub]

theorem constants_le_projectFull_ker : constants (Fin 12) ≤ projectFull.ker := by
  intro v hv
  obtain ⟨c, hc⟩ := (mem_constants_iff v).mp hv
  ext i
  simp [projectFull, hc]

def coordinates : M12Heart →ₗ[ZMod 2] Coordinates :=
  ((constants (Fin 12)).liftQ projectFull constants_le_projectFull_ker).comp
    (natural (Fin 12)).subtype

@[simp] theorem coordinates_toHeart (v : Coordinates) : coordinates (toHeart v) = v := by
  ext i
  change projectFull (lift v) i = v i
  change (lift v) i.castSucc.castSucc - (lift v) (Fin.last 10).castSucc = v i
  simp only [lift, LinearMap.coe_mk, AddHom.coe_mk, Fin.snoc_castSucc, Fin.snoc_last, sub_zero]

theorem toHeart_injective : Function.Injective toHeart :=
  Function.LeftInverse.injective coordinates_toHeart

noncomputable def heartEquiv : Coordinates ≃ₗ[ZMod 2] M12Heart :=
  LinearMap.linearEquivOfInjective toHeart toHeart_injective
    (by simpa using finrank_m12Heart.symm)

@[simp] theorem heartEquiv_apply (v : Coordinates) : heartEquiv v = toHeart v := rfl

@[simp] theorem heartEquiv_symm_apply (v : M12Heart) : heartEquiv.symm v = coordinates v := by
  obtain ⟨u, rfl⟩ := heartEquiv.surjective v
  rw [LinearEquiv.symm_apply_apply, heartEquiv_apply, coordinates_toHeart]

def action (g : Equiv.Perm (Fin 12)) : Coordinates →ₗ[ZMod 2] Coordinates :=
  projectFull.comp ((representation (Fin 12) g).comp lift)

theorem coordinates_action (g : Equiv.Perm (Fin 12)) (v : Coordinates) :
    coordinates (naturalRepresentation (Fin 12) g (toHeart v)) = action g v := rfl

theorem heartEquiv_action (g : Equiv.Perm (Fin 12)) (v : Coordinates) :
    heartEquiv (action g v) = naturalRepresentation (Fin 12) g (heartEquiv v) := by
  apply heartEquiv.symm.injective
  rw [LinearEquiv.symm_apply_apply, heartEquiv_symm_apply, heartEquiv_apply,
    coordinates_action]

def permutationRepresentation : Representation (ZMod 2) (Equiv.Perm (Fin 12)) Coordinates where
  toFun := action
  map_one' := by
    apply LinearMap.ext
    intro v
    apply heartEquiv.injective
    rw [heartEquiv_action]
    simp
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    apply heartEquiv.injective
    simp only [Module.End.mul_apply, heartEquiv_action, map_mul]

noncomputable def coordinateRepresentation : Representation (ZMod 2) Sporadic.Mathieu.M12 Coordinates :=
  permutationRepresentation.comp Sporadic.Mathieu.M12.subtype

def displacementMatrix (g : Equiv.Perm (Fin 12)) : Matrix (Fin 10) (Fin 10) (ZMod 2) :=
  fun i j => action g (Pi.single j 1) i - (Pi.single j 1 : Coordinates) i

theorem displacementMatrix_eq (g : Equiv.Perm (Fin 12)) :
    displacementMatrix g = LinearMap.toMatrix' (action g - LinearMap.id) := by
  ext i j
  simp [displacementMatrix, LinearMap.toMatrix'_apply]

theorem fixedCodim_eq_matrix_rank (g : Sporadic.Mathieu.M12) :
    fixedCodim m12HeartRepresentation (Subgroup.zpowers g) =
      (displacementMatrix g.val).rank := by
  have he := fixedCodim_map_equivariant coordinateRepresentation m12HeartRepresentation
    (MonoidHom.id _) heartEquiv (fun a v => heartEquiv_action a.val v)
    (Subgroup.zpowers g)
  simp only [Subgroup.map_id] at he
  rw [← he, fixedCodim_zpowers_eq_displacement_rank, Matrix.rank, displacementMatrix_eq]
  change Module.finrank (ZMod 2) (LinearMap.range (action g.val - LinearMap.id)) = _
  rw [← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']
  rfl

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
