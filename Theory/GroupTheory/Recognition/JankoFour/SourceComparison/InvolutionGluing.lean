module
public import Theory.GroupTheory.NormalSupplementGluing
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Extension across an involutory supplement

An equivalence on a normal subgroup extends over a specified involution
when its conjugation action agrees. The proof applies normal-supplement
gluing to the two-element cyclic subgroup and retains both restrictions.
This is used for the original plane-group comparison in AS91 (8.3), p.606.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.InvolutionGluing
open Subgroup
variable {G H : Type*} [Group G] [Group H]

private theorem power_cases (s : G) (hs : s * s = 1) (hs1 : s ≠ 1)
    (x : zpowers s) : x = 1 ∨ x = ⟨s,mem_zpowers s⟩ := by
  have ho : orderOf s = 2 := orderOf_eq_prime (by simpa [pow_two] using hs) hs1
  have hc : Nat.card (zpowers s) = 2 := (Nat.card_zpowers s).trans ho
  by_cases hx : x=1
  · exact Or.inl hx
  obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (1 : zpowers s)).mp hc
  exact Or.inr ((ha x hx).trans (ha _ (fun he => hs1 (congrArg Subtype.val he))).symm)

private theorem cyclic_generator (s : G) :
    ∀ x : zpowers s, x ∈ zpowers (⟨s,mem_zpowers s⟩ : zpowers s) := by
  intro x
  obtain ⟨n,hn⟩ := x.property
  exact mem_zpowers_iff.mpr ⟨n,Subtype.ext hn⟩

/-- Extend a given normal-subgroup equivalence over its actual involutory
supplement, retaining the specified generator and conjugation action. -/
theorem exists_equiv (N : Subgroup G) [N.Normal] (R : Subgroup H)
    (e : N ≃* R) (s : G) (t : H)
    (hs : s*s=1) (ht : t*t=1) (hsN : s ∉ N) (htR : t ∉ R)
    (hg : N ⊔ zpowers s = ⊤) (hg' : R ⊔ zpowers t = ⊤)
    (hconj : ∀ n : N, (e (MulAut.conjNormal s n) : H) = t * e n * t⁻¹) :
    ∃ E : G ≃* H, (∀ n : N, E n = e n) ∧ E s = t := by
  have hs1 : s ≠ 1 := fun he => hsN (he ▸ N.one_mem)
  have ho : orderOf s = 2 := orderOf_eq_prime (by simpa [pow_two] using hs) hs1
  let sg : zpowers s := ⟨s,mem_zpowers s⟩
  have hd : orderOf t ∣ orderOf sg := by
    rw [←orderOf_coe sg]
    change orderOf t ∣ orderOf s
    rw [ho]
    exact orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using ht)
  let v := monoidHomOfForallMemZpowers (cyclic_generator s) hd
  have hv : v sg = t := monoidHomOfForallMemZpowers_apply_gen _ _
  have hr : v.range = zpowers t := by
    apply le_antisymm
    · rintro y ⟨x,rfl⟩
      rcases power_cases s hs hs1 x with rfl | he
      · rw [map_one]; exact one_mem _
      · change x=sg at he
        rw [he,hv]; exact mem_zpowers t
    · exact zpowers_le.mpr ⟨sg,hv⟩
  obtain ⟨E,hEn,hEv⟩ := NormalSupplementGluing.exists_equiv N (zpowers s) R e v hg
    (by rw [hr]; exact hg')
    (fun m => by
      rcases power_cases s hs hs1 m with rfl | he
      · simp only [map_one,Subgroup.coe_one,one_mem]
      · change m=sg at he
        rw [he,hv]
        exact iff_of_false htR hsN)
    (fun m hm => by
      rcases power_cases s hs hs1 m with rfl | he
      · simp only [map_one,Subgroup.coe_one]
        exact congrArg Subtype.val (map_one e)
      · have hm' : s ∈ N := by simpa only [he] using hm
        exact (hsN hm').elim)
    (fun m n => by
      rcases power_cases s hs hs1 m with rfl | he
      · simp
      · change m=sg at he
        rw [he,hv]
        exact hconj n)
  exact ⟨E,hEn,hEv sg |>.trans hv⟩
end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.InvolutionGluing
