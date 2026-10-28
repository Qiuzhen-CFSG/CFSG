module

public import Theory.SpecificGroups.LinearHigher.Presentation
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Mathlib.Algebra.CharP.Two

/-!
# Elementary roots in an odd central extension of PSL

In characteristic two each elementary root has a unique lift of square one
through an odd central kernel. Uniqueness gives additivity and distant
commutation. For a three-index pair its commutator centralizes the first
root; the commutator-of-a-square identity makes that commutator square one,
so uniqueness also gives the exact chain relation.

Consequently the elementary presented group maps onto any perfect central
extension with odd kernel. If its matrix map is faithful, this descends to
a surjection from the actual SL with central kernel and the prescribed
commuting projection. Faithfulness is retained as an explicit premise.

Source: Steinberg, *Lectures on Chevalley Groups*, Theorems 9 and 11,
Sections 6–7; `refs/KGroup/GLS3/Chapter2St1.tex`, printed pp.74 and 86–88.
-/

@[expose] public section

namespace Theory.SpecificGroups.LinearHigher

open scoped MatrixGroups commutatorElement

universe u v
variable {n : ℕ} {F : Type u} [Field F] [CharP F 2]
variable {E : Type v} [Group E]

/-- Elementary roots have square one in characteristic two, including zero. -/
theorem projectiveRoot_pow_two (r : Root n) (a : F) : projectiveRoot r a ^ 2 = 1 := by
  rw [pow_two, projectiveRoot_relations.add, CharTwo.add_self_eq_zero]
  simp only [projectiveRoot, matrixRoot, Matrix.SpecialLinearGroup.transvection_coeff_zero,
    QuotientGroup.mk_one]

variable (f : E →* PSL(n, F)) (hf : Function.Surjective f)
  (hcenter : f.ker ≤ Subgroup.center E) (hcop : (Nat.card f.ker).Coprime 2)

/-- The unique root preimage whose square is one. -/
noncomputable def rootLift (r : Root n) (a : F) : E :=
  Classical.choose (f.exists_pow_eq_one_lift_of_central_coprime_ker hf hcenter hcop
    (projectiveRoot r a) (projectiveRoot_pow_two r a))

@[simp] theorem rootLift_map (r : Root n) (a : F) :
    f (rootLift f hf hcenter hcop r a) = projectiveRoot r a :=
  (Classical.choose_spec
    (f.exists_pow_eq_one_lift_of_central_coprime_ker hf hcenter hcop
      (projectiveRoot r a) (projectiveRoot_pow_two r a))).1

@[simp] theorem rootLift_pow_two (r : Root n) (a : F) :
    rootLift f hf hcenter hcop r a ^ 2 = 1 :=
  (Classical.choose_spec
    (f.exists_pow_eq_one_lift_of_central_coprime_ker hf hcenter hcop
      (projectiveRoot r a) (projectiveRoot_pow_two r a))).2

/-- No central errors remain in any of the elementary defining relations. -/
theorem rootLift_relations : Relations (rootLift f hf hcenter hcop) where
  add r a b := by
    apply f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hcenter hcop
    · rw [map_mul, rootLift_map, rootLift_map, rootLift_map]
      exact projectiveRoot_relations.add r a b
    · have hc : Commute (rootLift f hf hcenter hcop r a)
          (rootLift f hf hcenter hcop r b) := by
        apply f.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
          hcenter hcop (rootLift_pow_two _ _ _ _ _ _)
        rw [rootLift_map, rootLift_map]
        exact commutatorElement_eq_one_iff_commute.mp
          (projectiveRoot_relations.distant r r a b r.property.symm r.property.symm)
      rw [hc.mul_pow, rootLift_pow_two, rootLift_pow_two, one_mul]
    · exact rootLift_pow_two _ _ _ _ _ _
  distant r s a b hrs hsr := by
    apply Commute.commutator_eq
    apply f.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
      hcenter hcop (rootLift_pow_two _ _ _ _ _ _)
    rw [rootLift_map, rootLift_map]
    exact commutatorElement_eq_one_iff_commute.mp
      (projectiveRoot_relations.distant r s a b hrs hsr)
  chain i j k hij hjk hik a b := by
    let x := rootLift f hf hcenter hcop (root i j hij) a
    let y := rootLift f hf hcenter hcop (root j k hjk) b
    have hx : x ^ 2 = 1 := rootLift_pow_two _ _ _ _ _ _
    have hm : f ⁅x, y⁆ = projectiveRoot (root i k hik) (a * b) := by
      rw [map_commutatorElement, rootLift_map, rootLift_map]
      exact projectiveRoot_relations.chain i j k hij hjk hik a b
    have hc : Commute x ⁅x, y⁆ := by
      apply f.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker hcenter hcop hx
      rw [rootLift_map, hm]
      exact commutatorElement_eq_one_iff_commute.mp
        (projectiveRoot_relations.distant (root i j hij) (root i k hik) a (a * b)
          hij.symm hik.symm)
    have hs : ⁅x, y⁆ ^ 2 = 1 := by
      have h := commutatorElement_mul_left_eq_conj_mul x x y
      have hxx : x * x = 1 := by simpa only [pow_two] using hx
      rw [hxx, commutatorElement_one_left, hc.eq] at h
      simpa only [mul_inv_cancel_right, pow_two] using h.symm
    exact f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hcenter hcop
      (hm.trans (rootLift_map _ _ _ _ _ _).symm) hs (rootLift_pow_two _ _ _ _ _ _)

/-- The literal projection square for the lifted elementary presentation. -/
theorem lift_rootLift_fac :
    f.comp (lift (rootLift_relations f hf hcenter hcop)) = projectiveMap := by
  apply PresentedGroup.ext
  rintro ⟨r, a⟩
  change f (lift (rootLift_relations f hf hcenter hcop) (generator r a)) =
    projectiveMap (generator r a)
  rw [lift_generator, projectiveMap_generator, rootLift_map]

include hf hcenter hcop in
/-- A faithful elementary presentation produces an actual central covering
from SL, retaining the field, dimension and the original projective marking. -/
theorem exists_covering_of_matrixMap_injective [Group.IsPerfect E] (hn : 2 ≤ n)
    (hinj : Function.Injective (matrixMap (n := n) (F := F))) :
    ∃ s : SL(n, F) →* E, Function.Surjective s ∧
      f.comp s = QuotientGroup.mk' (Subgroup.center SL(n, F)) ∧
      s.ker ≤ Subgroup.center SL(n, F) := by
  let e : SteinbergGroup n F ≃* SL(n, F) :=
    MulEquiv.ofBijective matrixMap ⟨hinj, matrixMap_surjective hn⟩
  let s := (lift (rootLift_relations f hf hcenter hcop)).comp e.symm.toMonoidHom
  have hfac : f.comp s = QuotientGroup.mk' (Subgroup.center SL(n, F)) := by
    ext g
    change f (lift (rootLift_relations f hf hcenter hcop) (e.symm g)) = QuotientGroup.mk g
    rw [← MonoidHom.comp_apply, lift_rootLift_fac, projectiveMap_eq]
    change QuotientGroup.mk (e (e.symm g)) = QuotientGroup.mk g
    rw [e.apply_symm_apply]
  have hsurj : Function.Surjective s :=
    PerfectCentralCovering.surjective_of_comp_surjective_of_ker_le_center_of_isPerfect
      f s (by rw [hfac]; exact QuotientGroup.mk'_surjective _) hcenter
  refine ⟨s, hsurj, hfac, ?_⟩
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  have h := DFunLike.congr_fun hfac x
  rw [MonoidHom.comp_apply, show s x = 1 from hx, map_one] at h
  exact h.symm

end Theory.SpecificGroups.LinearHigher
