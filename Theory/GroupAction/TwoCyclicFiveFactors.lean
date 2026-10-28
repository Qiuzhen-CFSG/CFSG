module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.GroupTheory.PGroup
public import Theory.GroupTheory.PGroup.FrattiniAutomorphismKernel

/-!
# Automorphisms preserving two generating subgroups of order five

The stabilizer of either subgroup has index at most two. Restriction embeds
it in the product of the two cyclic automorphism groups, each of order four.
Consequently the given automorphism subgroup has order dividing 32. The
subgroups need not be assumed independent or commuting: generation suffices
for injectivity of restriction.

This is the terminal factor-permutation argument in Aschbacher--Smith,
3.2.13, printed pp.584--585. The source application must first produce the
two actual factors and prove that its normalizer action preserves them.
-/

public section
namespace Subgroup
open scoped Pointwise
variable {P : Type*} [Group P] [Finite P]

/-- An automorphism group preserving two distinct generating order-five
subgroups has order dividing 32, using the actual restriction actions. -/
theorem card_dvd_thirtyTwo_of_permutes_order_five_pair
    (A : Subgroup (MulAut P)) (B C : Subgroup P)
    (hB : Nat.card B = 5) (hC : Nat.card C = 5) (hne : B ≠ C)
    (hgen : B ⊔ C = ⊤)
    (hperm : ∀ a : A,
      (B.map a.val.toMonoidHom = B ∧ C.map a.val.toMonoidHom = C) ∨
      (B.map a.val.toMonoidHom = C ∧ C.map a.val.toMonoidHom = B)) :
    Nat.card A ∣ 32 := by
  classical
  let S := MulAction.stabilizer A B
  have hfixB (a : S) : B.map a.val.val.toMonoidHom = B := a.property
  have hfixC (a : S) : C.map a.val.val.toMonoidHom = C := by
    rcases hperm a.val with hh | hh
    · exact hh.2
    · exact (hne ((hfixB a).symm.trans hh.1)).elim
  let restrict (D : Subgroup P) (hD : ∀ a : S, D.map a.val.val.toMonoidHom = D) :
      S →* MulAut D :=
    { toFun := fun a => (a.val.val.subgroupMap D).trans (MulEquiv.subgroupCongr (hD a))
      map_one' := by ext x; rfl
      map_mul' := by intro a b; ext x; rfl }
  let f : S →* MulAut B × MulAut C := (restrict B hfixB).prod (restrict C hfixC)
  have hf : Function.Injective f := by
    intro a b hab
    have hBF : ∀ x ∈ B, a.val.val x = b.val.val x := by
      intro x hx
      exact congrArg (fun z : MulAut B × MulAut C => ((z.1 ⟨x, hx⟩ : B) : P)) hab
    have hCF : ∀ x ∈ C, a.val.val x = b.val.val x := by
      intro x hx
      exact congrArg (fun z : MulAut B × MulAut C => ((z.2 ⟨x, hx⟩ : C) : P)) hab
    apply Subtype.ext
    apply Subtype.ext
    apply MulEquiv.ext
    intro x
    have hx : x ∈ B ⊔ C := by rw [hgen]; exact mem_top x
    exact (show B ⊔ C ≤ a.val.val.toMonoidHom.eqLocus b.val.val.toMonoidHom from
      sup_le hBF hCF) hx
  have hcS : Nat.card S ∣ 16 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    let : IsCyclic B := isCyclic_of_prime_card hB
    let : IsCyclic C := isCyclic_of_prime_card hC
    have hd := card_dvd_of_injective f hf
    rw [Nat.card_prod, IsCyclic.card_mulAut, IsCyclic.card_mulAut, hB, hC] at hd
    exact hd
  have hi : S.index ≤ 2 := by
    rw [MulAction.index_stabilizer]
    have ho : MulAction.orbit A B ⊆ {B, C} := by
      rintro D ⟨a, rfl⟩
      rcases hperm a with ha | ha
      · exact Or.inl ha.1
      · exact Or.inr ha.1
    exact (Set.ncard_le_ncard ho).trans_eq (Set.ncard_pair hne)
  have hd : S.index ∣ 2 := by
    have hp := S.index_ne_zero_of_finite
    have hh : S.index = 1 ∨ S.index = 2 := by omega
    rcases hh with hh | hh <;> simp [hh]
  have hc := Nat.mul_dvd_mul hcS hd
  rwa [S.card_mul_index] at hc

/-- The same literal automorphism subgroup is a two-group. -/
theorem isPGroup_two_of_permutes_order_five_pair
    (A : Subgroup (MulAut P)) (B C : Subgroup P)
    (hB : Nat.card B = 5) (hC : Nat.card C = 5) (hne : B ≠ C)
    (hgen : B ⊔ C = ⊤)
    (hperm : ∀ a : A,
      (B.map a.val.toMonoidHom = B ∧ C.map a.val.toMonoidHom = C) ∨
      (B.map a.val.toMonoidHom = C ∧ C.map a.val.toMonoidHom = B)) :
    IsPGroup 2 A :=
  IsPGroup.of_card_dvd_pow (n := 5)
    (card_dvd_thirtyTwo_of_permutes_order_five_pair A B C hB hC hne hgen hperm)

/-- Preserve the original automorphism subgroup when lifting a two-factor
action through a five-group's genuine Frattini quotient. The discarded
kernel is a five-group by Burnside's Frattini automorphism theorem. -/
theorem prime_divisors_of_permutes_frattini_order_five_pair
    (hP : IsPGroup 5 P) (A : Subgroup (MulAut P))
    (B C : Subgroup (P ⧸ frattini P))
    (hB : Nat.card B = 5) (hC : Nat.card C = 5) (hne : B ≠ C)
    (hgen : B ⊔ C = ⊤)
    (hperm : ∀ a : A,
      let f := quotientAut (frattini P) a.val
      (B.map f.toMonoidHom = B ∧ C.map f.toMonoidHom = C) ∨
      (B.map f.toMonoidHom = C ∧ C.map f.toMonoidHom = B)) :
    ∀ q : ℕ, q.Prime → q ∣ Nat.card A → q = 2 ∨ q = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let f := (quotientAut (frattini P)).comp A.subtype
  have hi : IsPGroup 2 f.range := by
    apply isPGroup_two_of_permutes_order_five_pair f.range B C hB hC hne hgen
    intro a
    obtain ⟨b, hb⟩ := a.property
    change _ = _ at hb
    simpa only [← hb, f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hperm b
  have hk : IsPGroup 5 f.ker :=
    (isPGroup_quotientAut_frattini_kernel hP).comap_subtype
  obtain ⟨i, hi⟩ := hi.exists_card_eq
  obtain ⟨k, hk⟩ := hk.exists_card_eq
  have hc : Nat.card A = 5 ^ k * 2 ^ i := by
    rw [← hi, ← hk, ← index_ker]
    exact f.ker.card_mul_index.symm
  intro q hq hd
  rw [hc] at hd
  rcases hq.dvd_mul.mp hd with hd | hd
  · exact Or.inr ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp
      (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (hq.dvd_of_dvd_pow hd) |>.resolve_left hq.ne_one)

end Subgroup
