module
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Multiplicity.Chapter15Exchange
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.Automizers.Models.Actions
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.SpecificGroups.KleinFourAut

/-!
# Comparing the two natural binary plane models

The augmentation core of the three-letter permutation module is the natural
binary plane. The comparison here respects any specified isomorphism
SL₂(2) ≃ S₃: the two faithful full actions differ by an inner automorphism,
which is absorbed into the vector coordinates. At multiplicity one this
identifies the two ordered natural sums with the final direct-sum action.

Right multiplication by the alternating matrix converts the determinant
convention AXB⁻¹ to the tensor convention AXBᵀ, preserving the determinant.
These are the finite coordinate changes used in Aschbacher–Smith 15.3.54(4),
15.3.58(2), and 15.3.59, printed pp.1146, 1148, and 1150.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
open Subgroup Matrix BinaryPermutation
open scoped IsMulCommutative
abbrev PlaneActor := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev Plane := Multiplicative (Fin 2 → ZMod 2)
abbrev ThreeCore := BinaryPermutation.core (Fin 3)
abbrev S3 := Equiv.Perm (Fin 3)

def coreCoordinates : ThreeCore ≃ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun v := ![v.val 0, v.val 1]
  invFun v := ⟨![v 0, v 1, -v 0 - v 1], by
    rw [BinaryPermutation.mem_core, Fin.sum_univ_three]
    change v 0 + v 1 + (-v 0 - v 1) = 0
    ring⟩
  left_inv v := by
    apply Subtype.ext
    have hv := v.property
    rw [BinaryPermutation.mem_core, Fin.sum_univ_three] at hv
    ext i
    fin_cases i
    · rfl
    · rfl
    · change -v.val 0 - v.val 1 = v.val 2
      linear_combination -hv
  right_inv v := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' a v := by ext i; fin_cases i <;> rfl

def coreActor : S3 →* MulAut (Multiplicative ThreeCore) :=
  { toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv
        ((BinaryPermutation.coreRepresentation (Fin 3)).asGroupHom g)).toAddEquiv.toMultiplicative
    map_one' := by
      apply MulEquiv.ext
      intro v
      apply Multiplicative.toAdd.injective
      exact LinearMap.congr_fun (map_one (BinaryPermutation.coreRepresentation (Fin 3))) v.toAdd
    map_mul' a b := by
      apply MulEquiv.ext
      intro v
      apply Multiplicative.toAdd.injective
      exact LinearMap.congr_fun ((BinaryPermutation.coreRepresentation (Fin 3)).map_mul a b) v.toAdd }

theorem coreActor_injective : Function.Injective coreActor := by
  have h : ∀ a b : S3,
      (∀ v : Fin 3 → ZMod 2, (∑ i, v i) = 0 →
        BinaryPermutation.representation (Fin 3) a v =
          BinaryPermutation.representation (Fin 3) b v) → a = b := by
    decide +kernel
  intro a b hab
  apply h a b
  intro v hv
  let w : ThreeCore := ⟨v, (BinaryPermutation.mem_core _ _).mpr hv⟩
  exact congrArg (fun x : Multiplicative ThreeCore => x.toAdd.val)
    (MulEquiv.congr_fun hab (Multiplicative.ofAdd w))

local instance : IsKleinFour Plane :=
  ⟨by norm_num [Plane, Nat.card_eq_fintype_card],
    (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr (by
      intro v hv
      apply orderOf_eq_prime _ hv
      have h : ∀ w : Plane, w ^ 2 = 1 := by decide +kernel
      exact h v)⟩

def planeCoreActor : S3 →* MulAut Plane :=
  (MulAut.congr coreCoordinates.toAddEquiv.toMultiplicative).toMonoidHom.comp coreActor

def planeCoreEquiv : S3 ≃* MulAut Plane :=
  MulEquiv.ofBijective planeCoreActor ((Nat.bijective_iff_injective_and_card _).mpr
    ⟨(MulAut.congr coreCoordinates.toAddEquiv.toMultiplicative).injective.comp coreActor_injective,
      by rw [IsKleinFour.card_mulAut, Nat.card_perm, Nat.card_fin]; norm_num [Nat.factorial]⟩)

local instance : MulDistribMulAction PlaneActor Plane := FourGroupMatrixCoordinates.naturalAction

def naturalEquiv : PlaneActor ≃* MulAut Plane := by
  refine MulEquiv.ofBijective (MulDistribMulAction.toMulAut PlaneActor Plane) ⟨?_, ?_⟩
  · intro a b hab
    let := FourGroupMatrixCoordinates.naturalAction_faithful
    exact FaithfulSMul.eq_of_smul_eq_smul (fun v => MulEquiv.congr_fun hab v)
  · intro f
    obtain ⟨a, ha⟩ := FourGroupMatrixCoordinates.naturalAction_surjective f
    exact ⟨a, MulEquiv.ext ha⟩

theorem exists_coreCoordinates (e : PlaneActor ≃* S3) :
    ∃ c : Multiplicative ThreeCore ≃* Plane,
      ∀ (a : PlaneActor) (v : ThreeCore),
        c (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 3) (e a) v)) =
          a • c (Multiplicative.ofAdd v) := by
  let e' : S3 ≃* MulAut Plane := e.symm.trans naturalEquiv
  obtain ⟨k, hk⟩ := Theory.GroupTheory.NormalSymmetricThreePairRank.symmetricThree_aut_inner
    (planeCoreEquiv.trans e'.symm)
  let c : Multiplicative ThreeCore ≃* Plane :=
    coreCoordinates.toAddEquiv.toMultiplicative.trans (e' k)⁻¹
  refine ⟨c, ?_⟩
  intro a v
  have he (g : S3) : planeCoreEquiv g = e' k * e' g * (e' k)⁻¹ := by
    have h := MulEquiv.congr_fun hk g
    apply e'.symm.injective
    change (planeCoreEquiv.trans e'.symm) g = _
    rw [h]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
    rfl
  have hg := MulEquiv.congr_fun (he (e a))
    (coreCoordinates.toAddEquiv.toMultiplicative (Multiplicative.ofAdd v))
  let c₀ := coreCoordinates.toAddEquiv.toMultiplicative
  have hleft : planeCoreEquiv (e a) (c₀ (Multiplicative.ofAdd v)) =
      c₀ (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 3) (e a) v)) := by
    change c₀ (coreActor (e a) (c₀.symm (c₀ (Multiplicative.ofAdd v)))) = _
    rw [c₀.symm_apply_apply]
    rfl
  rw [hleft] at hg
  change (e' k).symm (c₀ (Multiplicative.ofAdd
    (BinaryPermutation.coreRepresentation (Fin 3) (e a) v))) = _
  rw [hg]
  change (e' k).symm ((e' k) ((e' (e a)) ((e' k).symm (c₀ (Multiplicative.ofAdd v))))) = _
  rw [MulEquiv.symm_apply_apply]
  change naturalEquiv (e.symm (e a)) _ = naturalEquiv a _
  rw [e.symm_apply_apply]
  rfl

open Core.Automizers.Models ClassicalOrthogonal.FourPlusMatrix

def determinantToTensor : Multiplicative (Mat (F := ZMod 2)) ≃* TensorVector where
  toFun x := Multiplicative.ofAdd (x.toAdd * !![0, 1; 1, 0])
  invFun x := Multiplicative.ofAdd (x.toAdd * !![0, 1; 1, 0])
  left_inv := by
    have h : ∀ x : Mat (F := ZMod 2), (x * !![0, 1; 1, 0]) * !![0, 1; 1, 0] = x := by
      decide +kernel
    intro x
    exact congrArg Multiplicative.ofAdd (h x.toAdd)
  right_inv := by
    have h : ∀ x : Mat (F := ZMod 2), (x * !![0, 1; 1, 0]) * !![0, 1; 1, 0] = x := by
      decide +kernel
    intro x
    exact congrArg Multiplicative.ofAdd (h x.toAdd)
  map_mul' x y := by
    change Multiplicative.ofAdd ((x.toAdd + y.toAdd) * _) = _
    rw [Matrix.add_mul]
    rfl

theorem determinantToTensor_compatible (a : Actor) (v : Mat (F := ZMod 2)) :
    determinantToTensor (Multiplicative.ofAdd (matrixAction a v)) =
      tensorAction a (determinantToTensor (Multiplicative.ofAdd v)) := by
  have h : ∀ b : PlaneActor,
      (b⁻¹).val * !![0, 1; 1, 0] = !![0, 1; 1, 0] * b.val.transpose := by
    decide +kernel
  change Multiplicative.ofAdd ((a.1.val * v * (a.2⁻¹).val) * _) = _
  change Multiplicative.ofAdd ((a.1.val * v * (a.2⁻¹).val) * _) =
    Multiplicative.ofAdd (a.1.val * (v * !![0,1;1,0]) * a.2.val.transpose)
  simp only [Matrix.mul_assoc, h]

theorem determinantToTensor_determinant (v : Multiplicative (Mat (F := ZMod 2))) :
    determinantForm (determinantToTensor v).toAdd = determinantForm v.toAdd := by
  rw [determinantForm_apply, determinantForm_apply]
  change (v.toAdd * !![0, 1; 1, 0]).det = v.toAdd.det
  rw [Matrix.det_mul]
  have hj : (!![0, 1; 1, 0] : Mat (F := ZMod 2)).det = 1 := by decide +kernel
  rw [hj, mul_one]

theorem cubic_iff_cube (a : PlaneActor) : a ∈ cubic ↔ a ^ 3 = 1 := by
  change a ∈ zpowers rotation ↔ _
  rw [mem_zpowers_iff_mem_range_orderOf, rotation_order]
  have h : ∀ a : PlaneActor, a ∈ (Finset.range 3).image (fun n => rotation ^ n) ↔ a ^ 3 = 1 := by
    decide +kernel
  exact h a

theorem alternating_iff_cube (a : S3) : a ∈ alternatingGroup (Fin 3) ↔ a ^ 3 = 1 := by
  have h : ∀ a : S3, a ∈ alternatingGroup (Fin 3) ↔ a ^ 3 = 1 := by
    simp only [Equiv.Perm.mem_alternatingGroup]
    decide +kernel
  exact h a

theorem map_alternating_eq_cubic (e : S3 ≃* PlaneActor) :
    (alternatingGroup (Fin 3)).map e.toMonoidHom = cubic := by
  ext a
  rw [mem_map_equiv, alternating_iff_cube, cubic_iff_cube]
  rw [← map_pow, e.symm.map_eq_one_iff]

theorem map_alternating_pair_eq_nine (e : PlaneActor ≃* S3) :
    ((alternatingGroup (Fin 3)).prod (alternatingGroup (Fin 3))).map
      (e.symm.prodCongr e.symm).toMonoidHom = nine := by
  ext a
  rw [mem_map_equiv]
  change (e a.1 ∈ alternatingGroup (Fin 3) ∧ e a.2 ∈ alternatingGroup (Fin 3)) ↔
    (a.1 ∈ cubic ∧ a.2 ∈ cubic)
  simp only [alternating_iff_cube, cubic_iff_cube, ← map_pow, e.map_eq_one_iff]

def oneCopyCoordinates (c : Multiplicative ThreeCore ≃* Plane) :
    Multiplicative (Fin 2 → Fin 1 → ThreeCore) ≃* SumVector where
  toFun v := (c (Multiplicative.ofAdd (v.toAdd 0 0)),
    c (Multiplicative.ofAdd (v.toAdd 1 0)))
  invFun v := Multiplicative.ofAdd fun i _ =>
    (c.symm (if i = 0 then v.1 else v.2)).toAdd
  left_inv v := by
    apply Multiplicative.toAdd.injective
    funext i j
    fin_cases i <;> fin_cases j <;> simp
  right_inv v := by
    apply Prod.ext <;>
      simp only [ofAdd_toAdd, toAdd_ofAdd, ite_true, show (1 : Fin 2) ≠ 0 by decide,
        ite_false, MulEquiv.apply_symm_apply]
  map_mul' v w := by
    apply Prod.ext <;> exact c.map_mul _ _

theorem oneCopyCoordinates_compatible (e : PlaneActor ≃* S3)
    (c : Multiplicative ThreeCore ≃* Plane)
    (hc : ∀ (a : PlaneActor) (v : ThreeCore),
      c (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 3) (e a) v)) =
        a • c (Multiplicative.ofAdd v))
    (a : Actor) (v : Fin 2 → Fin 1 → ThreeCore) :
    oneCopyCoordinates c (Multiplicative.ofAdd (fun i j =>
      BinaryPermutation.coreRepresentation (Fin 3)
        (if i = 0 then e a.1 else e a.2) (v i j))) =
      sumAction a (oneCopyCoordinates c (Multiplicative.ofAdd v)) := by
  apply Prod.ext
  · exact hc a.1 (v 0 0)
  · exact hc a.2 (v 1 0)

def multiplicityOneCoordinates {n : ℕ} (hn : n = 1)
    (c : Multiplicative ThreeCore ≃* Plane) :
    Multiplicative (Fin 2 → Fin n → ThreeCore) ≃* SumVector := by
  subst n
  exact oneCopyCoordinates c

theorem multiplicityOneCoordinates_compatible {n : ℕ} (hn : n = 1)
    (e : PlaneActor ≃* S3) (c : Multiplicative ThreeCore ≃* Plane)
    (hc : ∀ (a : PlaneActor) (v : ThreeCore),
      c (Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 3) (e a) v)) =
        a • c (Multiplicative.ofAdd v))
    (a : Actor) (v : Fin 2 → Fin n → ThreeCore) :
    multiplicityOneCoordinates hn c (Multiplicative.ofAdd (fun i j =>
      BinaryPermutation.coreRepresentation (Fin 3)
        (if i = 0 then e a.1 else e a.2) (v i j))) =
      sumAction a (multiplicityOneCoordinates hn c (Multiplicative.ofAdd v)) := by
  subst n
  exact oneCopyCoordinates_compatible e c hc a v

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PairGeometry.LayerAdapters
