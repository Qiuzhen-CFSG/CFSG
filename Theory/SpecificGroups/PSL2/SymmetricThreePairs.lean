module

public import Theory.GroupTheory.SymmetricThreePairs
public import Theory.SpecificGroups.PSL2.RankOneRoots
public import Theory.SpecificGroups.SL2.SylowConsequences
public import Theory.SpecificGroups.PSL2.InvolutionFusion

/-!
# The binary field forced by conjugate root pairs in PSL₂

For a nonzero upper root parameter t and any nonzero r, the lower root
with parameter r/t is conjugate to it. The pair is not a two-group because
Sylow two-subgroups of SL₂ are abelian and these matrices do not commute.
The S₃ cube relation forces r²=1 and hence r=1 in characteristic two.
Involution conjugacy derives the root marking for an arbitrary involution.

Source: Aschbacher–Smith, 13.5.21, printed p.924, the inference from (iv)
that the defining field is binary. The actual SL₂ and PSL₂ carriers are used.
-/

public section
open Subgroup
namespace Theory.PSL2
open BenderSuzuki.Converse BenderSuzuki.MatrixGroups Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem two_subgroup_commute (P : Subgroup (SL2 F)) (hp : IsPGroup 2 P)
    (a b : SL2 F) (ha : a ∈ P) (hb : b ∈ P) : a * b = b * a := by
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 S
  have he : (⟨a, hS ha⟩ : S) * ⟨b, hS hb⟩ = ⟨b, hS hb⟩ * ⟨a, hS ha⟩ := by
    apply e.symm.injective
    simp only [map_mul, mul_comm]
  exact congrArg Subtype.val he

private def lower (t : F) : SL2 F := ⟨!![1,0;t,1], by simp [Matrix.det_fin_two]⟩

omit [Finite F] in
private theorem upper_order {t : F} (ht : t ≠ 0) : orderOf (uni t) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]
  · intro he
    apply ht
    have hh := congrArg (fun a : SL2 F => a.val 0 1) he
    simpa using hh

omit [Finite F] in
private theorem lower_order {t : F} (ht : t ≠ 0) : orderOf (lower t) = 2 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    change (!![1,0;t,1] : Matrix (Fin 2) (Fin 2) F) ^ 2 = 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.add_self_eq_zero]
  · intro he
    apply ht
    have hh := congrArg (fun a : SL2 F => a.val 1 0) he
    simpa [lower] using hh

theorem field_card_le_two_of_root_pairs {t : F} (ht : t ≠ 0)
    (h : SymmetricThreePairs (uni t)) : Nat.card F ≤ 2 := by
  classical
  have all (r : F) : r = 0 ∨ r = 1 := by
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    let u := r / t
    have hu : u ≠ 0 := div_ne_zero hr ht
    have hconj : IsConj (uni t) (lower u) := by
      have hp := involutions_isConj (pi F (uni t)) (pi F (lower u))
        ((orderOf_injective (pi F) pi_injective _).trans (upper_order ht))
        ((orderOf_injective (pi F) pi_injective _).trans (lower_order hu))
      obtain ⟨g, hg⟩ := isConj_iff.mp hp
      obtain ⟨x, rfl⟩ := pi_surjective g
      exact isConj_iff.mpr ⟨x, pi_injective (by simpa only [map_mul, map_inv] using hg)⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp hconj
    have hnot : ¬ IsPGroup 2 (zpowers (uni t) ⊔ zpowers (MulAut.conj g (uni t)) : Subgroup (SL2 F)) := by
      intro hp
      have he := two_subgroup_commute _ hp (uni t) (MulAut.conj g (uni t))
        (mem_sup_left (mem_zpowers _)) (mem_sup_right (mem_zpowers _))
      change g * uni t * g⁻¹ = lower u at hg
      change uni t * (g * uni t * g⁻¹) = (g * uni t * g⁻¹) * uni t at he
      rw [hg] at he
      have he00 := congrArg (fun a : SL2 F => a.val 0 0) he
      change ((!![1,t;0,1] : Matrix (Fin 2) (Fin 2) F) * !![1,0;u,1]) 0 0 =
        (!![1,0;u,1] * !![1,t;0,1]) 0 0 at he00
      have hz : t * u = 0 := by
        simpa [Matrix.mul_apply, Fin.sum_univ_two] using he00
      exact mul_ne_zero ht hu hz
    have he := h.cube (upper_order ht) g hnot
    change (uni t * (g * uni t * g⁻¹)) ^ 3 = 1 at he
    rw [hg] at he
    have he01 := congrArg (fun a : SL2 F => a.val 0 1) he
    change (((!![1,t;0,1] : Matrix (Fin 2) (Fin 2) F) * !![1,0;u,1]) ^ 3) 0 1 = 0 at he01
    have heq : t * ((t * u) ^ 2 + 1) = 0 := by
      simpa [pow_succ, pow_zero, Matrix.mul_apply, Fin.sum_univ_two,
        CharTwo.add_self_eq_zero, CharTwo.add_cancel_left, mul_add, add_mul, mul_assoc, mul_left_comm,
        mul_comm, add_assoc, add_comm, add_left_comm] using he01
    have hrsq : r ^ 2 = 1 := by
      have hz := (mul_eq_zero.mp heq).resolve_left ht
      have htu : t * u = r := by dsimp [u]; field_simp
      rw [htu] at hz
      exact (eq_neg_of_add_eq_zero_left hz).trans (CharTwo.neg_eq _)
    exact CharTwo.sq_injective (hrsq.trans (one_pow 2).symm)
  let f : F → Bool := fun x => decide (x = 1)
  have hf : Function.Injective f := by
    intro x y hxy
    rcases all x with rfl | rfl <;> rcases all y with rfl | rfl
    all_goals simp_all [f]
  simpa using Nat.card_le_card_of_injective f hf
end Theory.PSL2
namespace Theory.PSL2
open BenderSuzuki.Converse BenderSuzuki.MatrixGroups Theory.GroupTheory
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- Every marked involution with the S₃ pair condition forces the binary field.
Root marking is derived from the actual involution, not assumed. -/
theorem field_card_le_two_of_involution_pairs (v : PSL2MatrixGroup F)
    (hv : orderOf v = 2) (h : SymmetricThreePairs v) : Nat.card F ≤ 2 := by
  obtain ⟨g, t, ht, hg, _, _⟩ := involution_root_geometry v hv
  have hp : SymmetricThreePairs (pi F (uni t)) := hg ▸ h.map_equiv (MulAut.conj g)
  exact field_card_le_two_of_root_pairs ht
    (hp.of_injective (pi F) pi_injective)
end Theory.PSL2
