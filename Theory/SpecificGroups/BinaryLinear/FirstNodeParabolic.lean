module
public import Theory.SpecificGroups.BinaryLinear.OrderedResidualConjugators.FirstPlane
public import Theory.SpecificGroups.BinaryLinear.CubicSylowGeneration
public import Theory.SpecificGroups.BinaryLinear.EndpointParabolic
public import Theory.GroupTheory.SubgroupPartitionCounting

/-!
# The first minimal parabolic in a binary flag

Restriction to the first two-space identifies the literal two-core
quotient with S₃. Its two-residual contains the sixteen distinct root
rectangles on coordinates 0,1 against 2,3. The Sylow index of three
also excludes divisibility of its order by nine. These are the quotient
and block-size inputs for the ordinary binary-linear source parabolics
in Aschbacher--Smith 15.1.22(7), printed pp.1099--1100 of refs/quasithin.pdf.
-/

public section
open Subgroup
namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions

private noncomputable def rootChoice {m : ℕ} (b : Basis m)
    (r s : Fin (m+1)) (hrs : r ≠ s) (a : ZMod 2) : LinearGroup (m+1) :=
  if a = 0 then 1 else root b r s hrs

private theorem rootChoice_apply {m : ℕ} (b : Basis m)
    (r s : Fin (m+1)) (hrs : r ≠ s) (a : ZMod 2) (v : Space (m+1)) :
    rootChoice b r s hrs a v = v + (a * b.coord s v) • b r := by
  have hroot : root b r s hrs v = v + b.coord s v • b r := by
    have he : root b r s hrs = transvection (b r) (b.coord s) (by simp [hrs]) := by
      apply b.ext'
      intro j
      rw [root_basis]
      change (if j = s then b j + b r else b j) = b j + b.coord s (b j) • b r
      by_cases hj : j = s <;> simp [hj,Module.Basis.coord_apply]
    rw [he]
    rfl
  by_cases ha : a = 0
  · simp [rootChoice,ha]
  · have ha1 : a = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x=1) _ ha
    simp [rootChoice,ha1,hroot]

private noncomputable def rootRectangle {m : ℕ} (hm : 3 ≤ m) (b : Basis m)
    (a : Fin 2 → Fin 2 → ZMod 2) : LinearGroup (m+1) :=
  rootChoice b ⟨0,by omega⟩ ⟨2,by omega⟩ (by simp) (a 0 0) *
  rootChoice b ⟨0,by omega⟩ ⟨3,by omega⟩ (by simp) (a 0 1) *
  rootChoice b ⟨1,by omega⟩ ⟨2,by omega⟩ (by simp) (a 1 0) *
  rootChoice b ⟨1,by omega⟩ ⟨3,by omega⟩ (by simp) (a 1 1)

private theorem rootRectangle_entry {m : ℕ} (hm : 3 ≤ m) (b : Basis m)
    (a : Fin 2 → Fin 2 → ZMod 2) (i j : Fin 2) :
    b.coord ⟨i.val,by omega⟩ (rootRectangle hm b a (b ⟨j.val+2,by omega⟩)) = a i j := by
  fin_cases i <;> fin_cases j <;>
    simp [rootRectangle,LinearEquiv.mul_apply,rootChoice_apply,map_add,map_smul,
      Module.Basis.coord_apply]

theorem first_node_residual_card_ge_sixteen {m : ℕ} (hm : 3 ≤ m) (b : Basis m) :
    16 ≤ Nat.card (nodeResidual b ⟨0,by omega⟩) := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  have hmem (a : Fin 2 → Fin 2 → ZMod 2) :
      rootRectangle hm b a ∈ nodeResidual b ⟨0,by omega⟩ := by
    have hroot (i j : Fin (m+1)) (hij : i ≠ j) (hi : i.val=0 ∨ i.val=1) (hj : 1 < j.val)
        (c : ZMod 2) : rootChoice b i j hij c ∈ nodeResidual b ⟨0,by omega⟩ := by
      unfold rootChoice
      split
      · exact one_mem _
      · apply incident_root_mem_nodeResidual
        exact .inr ⟨hi.imp (fun he => Fin.ext he) (fun he => Fin.ext he),hj⟩
    apply mul_mem
    · apply mul_mem
      · apply mul_mem <;> apply hroot <;> simp
      · apply hroot <;> simp
    · apply hroot <;> simp
  let f : (Fin 2 → Fin 2 → ZMod 2) → nodeResidual b ⟨0,by omega⟩ :=
    fun a => ⟨rootRectangle hm b a,hmem a⟩
  have hf : Function.Injective f := by
    intro a c he
    ext i j
    have hh := congrArg (fun g : nodeResidual b ⟨0,by omega⟩ =>
      b.coord ⟨i.val,by omega⟩ ((g : LinearGroup (m+1)) (b ⟨j.val+2,by omega⟩))) he
    exact (rootRectangle_entry hm b a i j).symm.trans
      (hh.trans (rootRectangle_entry hm b c i j))
  simpa [Nat.card_fun,Nat.card_fin,Nat.card_zmod] using Nat.card_le_card_of_injective f hf

end BinaryLinear.OrderedResidualConjugators

namespace BinaryLinear.OrderedResidualConjugators
open OuterCyclic InvariantNodeActions

/-- The literal first-node two-core quotient is S₃. -/
noncomputable def first_node_quotient {m : ℕ} (hm : 3 ≤ m) (b : Basis m) :
    (minimalParabolic b ⟨0,by omega⟩ ⧸ pCore 2 (minimalParabolic b ⟨0,by omega⟩)) ≃*
      Equiv.Perm (Fin 3) := by
  let W := cutSpace b (⟨1,by omega⟩ : Fin m)
  let eW : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _
    (by rw [cutSpace_finrank]; simp [Space])
  exact (QuotientGroup.quotientMulEquivOfEq (ker_firstPlaneAction (by omega) b).symm).trans
    ((QuotientGroup.quotientKerEquivOfSurjective _ (firstPlaneAction_surjective (by omega) b)).trans
      ((SmallParabolicLevi.linearGroupCongr eW).trans
        SmallParabolicLevi.linearTwoEquivSymmetricThree))

/-- A binary minimal parabolic has exactly one factor of three in its order. -/
theorem node_card_not_nine {m : ℕ} (b : Basis m) (i : Fin m) :
    ¬ 9 ∣ Nat.card (minimalParabolic b i) := by
  let : Finite (LinearGroup (m+1)) := Finite.of_injective
    (fun g : LinearGroup (m+1) => (g : Space (m+1) → Space (m+1))) DFunLike.coe_injective
  let P := minimalParabolic b i
  let U := cutStabilizer b Set.univ
  have hUP : U ≤ P := (cutStabilizer_le_iff _ _ _).mpr (Set.subset_univ _)
  have he := relIndex_mul_card_of_le hUP
  change (cutStabilizer b Set.univ).relIndex P * Nat.card (cutStabilizer b Set.univ) = Nat.card P at he
  rw [CubicSylowGeneration.minimalParabolic_index] at he
  obtain ⟨k,hk⟩ := (fullFlag_isPGroup b).exists_card_eq
  rw [hk] at he
  intro h9
  have h3 : 3 ∣ 2^k := by
    have hd : 3*3 ∣ 3*2^k := he.symm ▸ h9
    exact Nat.dvd_of_mul_dvd_mul_left (by decide) hd
  exact (by decide : ¬3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow h3)
end BinaryLinear.OrderedResidualConjugators
