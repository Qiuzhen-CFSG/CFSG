module

public import Theory.SpecificGroups.LinearHigher.RootCalculus
public import Theory.GroupTheory.CentralCoprimeCardLift
public import Theory.GroupTheory.PerfectCentralCoverExistence

/-!
# Elementary roots in a central extension coprime to the characteristic

A root has a unique lift whose p-th power is one when the central kernel
has order prime to the characteristic p. Uniqueness gives additivity and
distant commutation. The three-index commutator commutes with its first
argument, so its p-th power is the commutator of a p-th power and is one.
This gives the exact chain relation, including in odd characteristic.

The resulting map from the actual Steinberg presentation descends to SL
if its matrix map is injective. This last premise is retained explicitly.
Source: Steinberg, Lectures on Chevalley Groups, §7, Theorem 11,
printed pp.86–88, refs/KGroup/GLS3/Chapter2St1.tex. The degree-four
application is in the parent TwoPrimary module.
-/

@[expose] public section

namespace Theory.SpecificGroups.LinearHigher.CoprimeRootLifts

open scoped MatrixGroups commutatorElement
universe u v
variable {n p : ℕ} {F : Type u} [Field F] [CharP F p]
variable {E : Type v} [Group E]

/-- Elementary roots have p-th power one in characteristic p. -/
theorem projectiveRoot_pow_char (r : Root n) (a : F) : projectiveRoot r a ^ p = 1 := by
  have hpow (m : ℕ) : projectiveRoot r a ^ m = projectiveRoot r (m • a) := by
    induction m with
    | zero => simp [projectiveRoot_relations.zero]
    | succ m ih => rw [pow_succ, ih, projectiveRoot_relations.add, succ_nsmul]
  rw [hpow]
  simp [nsmul_eq_mul, projectiveRoot_relations.zero]

private theorem commutator_pow_left_of_commute {x y : E} (h : Commute x ⁅x, y⁆)
    (m : ℕ) : ⁅x ^ m, y⁆ = ⁅x, y⁆ ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, commutatorElement_mul_left_eq_conj_mul,
      (h.pow_left m).eq, mul_inv_cancel_right, ih, ← pow_succ']

variable (f : E →* PSL(n, F)) (hf : Function.Surjective f)
  (hcenter : f.ker ≤ Subgroup.center E) (hcop : (Nat.card f.ker).Coprime p)

/-- The unique root preimage with p-th power one. -/
noncomputable def rootLift (r : Root n) (a : F) : E :=
  Classical.choose (f.exists_pow_eq_one_lift_of_central_coprime_ker hf hcenter hcop
    (projectiveRoot r a) (projectiveRoot_pow_char r a))

@[simp] theorem rootLift_map (r : Root n) (a : F) :
    f (rootLift f hf hcenter hcop r a) = projectiveRoot r a :=
  (Classical.choose_spec
    (f.exists_pow_eq_one_lift_of_central_coprime_ker hf hcenter hcop
      (projectiveRoot r a) (projectiveRoot_pow_char r a))).1

@[simp] theorem rootLift_pow_char (r : Root n) (a : F) :
    rootLift f hf hcenter hcop r a ^ p = 1 :=
  (Classical.choose_spec
    (f.exists_pow_eq_one_lift_of_central_coprime_ker hf hcenter hcop
      (projectiveRoot r a) (projectiveRoot_pow_char r a))).2

/-- All elementary defining relations lift with no central errors. -/
theorem rootLift_relations : Relations (rootLift f hf hcenter hcop) where
  add r a b := by
    apply f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hcenter hcop
    · rw [map_mul, rootLift_map, rootLift_map, rootLift_map]
      exact projectiveRoot_relations.add r a b
    · have hc : Commute (rootLift f hf hcenter hcop r a)
          (rootLift f hf hcenter hcop r b) := by
        apply f.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
          hcenter hcop (rootLift_pow_char _ _ _ _ _ _)
        rw [rootLift_map, rootLift_map]
        exact commutatorElement_eq_one_iff_commute.mp
          (projectiveRoot_relations.distant r r a b r.property.symm r.property.symm)
      rw [hc.mul_pow, rootLift_pow_char, rootLift_pow_char, one_mul]
    · exact rootLift_pow_char _ _ _ _ _ _
  distant r s a b hrs hsr := by
    apply Commute.commutator_eq
    apply f.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker
      hcenter hcop (rootLift_pow_char _ _ _ _ _ _)
    rw [rootLift_map, rootLift_map]
    exact commutatorElement_eq_one_iff_commute.mp
      (projectiveRoot_relations.distant r s a b hrs hsr)
  chain i j k hij hjk hik a b := by
    let x := rootLift f hf hcenter hcop (root i j hij) a
    let y := rootLift f hf hcenter hcop (root j k hjk) b
    have hx : x ^ p = 1 := rootLift_pow_char _ _ _ _ _ _
    have hm : f ⁅x, y⁆ = projectiveRoot (root i k hik) (a * b) := by
      rw [map_commutatorElement, rootLift_map, rootLift_map]
      exact projectiveRoot_relations.chain i j k hij hjk hik a b
    have hc : Commute x ⁅x, y⁆ := by
      apply f.commute_of_map_commute_of_pow_eq_one_of_central_coprime_ker hcenter hcop hx
      rw [rootLift_map, hm]
      exact commutatorElement_eq_one_iff_commute.mp
        (projectiveRoot_relations.distant (root i j hij) (root i k hik) a (a * b)
          hij.symm hik.symm)
    have hs : ⁅x, y⁆ ^ p = 1 := by
      rw [← commutator_pow_left_of_commute hc p, hx, commutatorElement_one_left]
    exact f.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker hcenter hcop
      (hm.trans (rootLift_map _ _ _ _ _ _).symm) hs (rootLift_pow_char _ _ _ _ _ _)

/-- The lifted presentation retains the original projective marking. -/
theorem lift_rootLift_fac :
    f.comp (lift (rootLift_relations f hf hcenter hcop)) = projectiveMap := by
  apply PresentedGroup.ext
  rintro ⟨r, a⟩
  change f (lift (rootLift_relations f hf hcenter hcop) (generator r a)) =
    projectiveMap (generator r a)
  rw [lift_generator, projectiveMap_generator, rootLift_map]

include hf hcenter hcop in
/-- A faithful elementary presentation gives a surjective lift from the
literal SL to any perfect central extension of prime-to-characteristic kernel. -/
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

end Theory.SpecificGroups.LinearHigher.CoprimeRootLifts
