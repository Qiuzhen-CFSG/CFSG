module
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.PSL2.OddPerfectCore
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension.SolvableKernel

/-!
# A linear-three section in prime-field SL₂

A perfect group with simple two-core quotient of order 168 can map to
prime-field SL₂ through a solvable kernel only in characteristic seven.
The map to PSL₂ preserves its simple two-core quotient. Dickson's theorem
excludes a proper image, which would have order 60. The full image has order
168, so the defining prime divides 336 and is seven.

Source: Aschbacher--Smith A.3.12 and the nonquasisimple branch of 12.5.3,
printed pp.47--48 and817--818. All maps retain the original two-core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SL2
variable {B : Type*} [Group B] [Finite B] [Group.IsPerfect B]
  [IsSimpleGroup (B ⧸ pCore 2 B)]

/-- A simple two-core section of order 168 forces prime characteristic seven. -/
theorem prime_seven_and_projective_surjective_of_solvable_kernel
    (hB : Nat.card (B ⧸ pCore 2 B) = 168)
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hF : Nat.card F = p)
    (f : B →* SL(2,F)) [Group.IsSolvable f.ker] :
    p = 7 ∧ Function.Surjective ((QuotientGroup.mk' (center SL(2,F))).comp f) := by
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  let : Group.IsSolvable (center SL(2,F)) := Group.isSolvable_of_comm (fun a b =>
    Subtype.ext (mem_center_iff.mp a.property b).symm)
  let q := QuotientGroup.mk' (center SL(2,F))
  let π : B →* PSL(2,F) := q.comp f
  let : Group.IsSolvable π.ker := by
    change Group.IsSolvable (q.comp f).ker
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact isSolvable_comap_of_solvable_ker f _
  let E := π.range
  let : Group.IsPerfect E := Group.IsPerfect.range π
  let : Group.IsSolvable π.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    infer_instance
  let e : (B ⧸ pCore 2 B) ≃* E :=
    (PerfectCoreTwoExtension.solvableKernelQuotientEquiv π.rangeRestrict
      π.rangeRestrict_surjective).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (Theory.PSL2.odd_perfect_subgroup_twoCore_eq_bot (hF ▸ ho) E)).trans
          QuotientGroup.quotientBot)
  have hc : Nat.card E = 168 := (Nat.card_congr e.toEquiv).symm.trans hB
  have ht : E = ⊤ := by
    by_contra ht
    have hns : ¬ Group.IsSolvable E := by
      let : Nontrivial E := e.symm.surjective.nontrivial
      exact Group.IsPerfect.not_isSolvable E
    obtain ⟨_,_,⟨a⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five ho hF E ht hns
    have hh := Nat.card_congr a.toEquiv
    rw [hc, nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
  have hcard : Nat.card PSL(2,F) = 168 := by simpa only [ht, card_top] using hc
  have hh := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF ▸ ho)
  rw [hcard,hF] at hh
  have hd : p ∣ 336 := by
    rw [show 336 = 168 * 2 from rfl, hh]
    exact dvd_mul_right _ _
  have hfactor : p ∣ 2 ∨ p ∣ 3 ∨ p ∣ 7 := by
    have hd' : p ∣ 2^4 * 3 * 7 := by norm_num; exact hd
    rcases hp.dvd_mul.mp hd' with hd' | hd'
    · rcases hp.dvd_mul.mp hd' with hd' | hd'
      · exact .inl (hp.dvd_of_dvd_pow hd')
      · exact .inr (.inl hd')
    · exact .inr (.inr hd')
  have he : p = 7 := by
    rcases hfactor with h | h | h
    · have := Nat.le_of_dvd (by decide : 0 < 2) h; omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) h; omega
    · exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h
  exact ⟨he, MonoidHom.range_eq_top.mp ht⟩

/-- The defining-prime consequence, without any surjectivity premise. -/
theorem prime_eq_seven_of_solvable_kernel
    (hB : Nat.card (B ⧸ pCore 2 B) = 168)
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hF : Nat.card F = p)
    (f : B →* SL(2,F)) [Group.IsSolvable f.ker] : p = 7 :=
  (prime_seven_and_projective_surjective_of_solvable_kernel hB hp hp3 hF f).1
end Theory.SL2
