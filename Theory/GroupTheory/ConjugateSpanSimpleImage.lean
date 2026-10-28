module
public import Theory.GroupTheory.PerfectSimpleImage
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Simple sections retained by conjugate-span images

A perfect group with a soluble-kernel simple quotient has no nontrivial
image in a target whose order omits a divisor of that simple quotient.
A homomorphism from a conjugate span is trivial as soon as every homomorphism
from its seed is trivial: restrict it to each literal conjugate and use
closure generation. No extension of the action to the conjugating group
is required.

These are the group-theoretic image steps for the SL₃(2) branch of the
original A₅ configuration in Aschbacher–Smith C.4.5–8, pp.152–154.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {F S D : Type*} [Group F] [Group S] [Group D]
  [IsSimpleGroup S] [Group.IsPerfect F]
theorem hom_eq_one_of_simple_quotient_card_dvd
    (q : F →* S) (hq : Function.Surjective q) [Group.IsSolvable q.ker]
    {p : ℕ} (hp : p ∣ Nat.card S) (hd : ¬ p ∣ Nat.card D) (f : F →* D) : f = 1 := by
  apply hom_eq_one_of_no_simple_section q hq ?_ f
  intro U g hg
  exact hd (hp.trans ((card_dvd_of_surjective g hg).trans U.card_subgroup_dvd_card))
end Theory.GroupTheory
namespace Subgroup
variable {G D : Type*} [Group G] [Group D]
theorem conjugateSpanBy_hom_eq_one (L M : Subgroup G)
    (hf : ∀ f : L →* D, f = 1) (f : conjugateSpanBy L M →* D) : f = 1 := by
  let X := conjugateSpanBy L M
  have hle : X ≤ f.ker.map X.subtype := by
    apply (closure_le _).mpr
    rintro x ⟨m,hm,l,hl,rfl⟩
    let c : L →* X :=
      { toFun := fun l => ⟨m * l * m⁻¹,subset_closure ⟨m,hm,l,l.property,rfl⟩⟩
        map_one' := by apply Subtype.ext; simp
        map_mul' := by intros; apply Subtype.ext; simp }
    have hh := DFunLike.congr_fun (hf (f.comp c)) (⟨l,hl⟩ : L)
    exact ⟨c ⟨l,hl⟩,hh,rfl⟩
  ext x
  obtain ⟨y,hy,he⟩ := hle x.property
  have hxy : y = x := Subtype.ext he
  exact hxy ▸ hy
end Subgroup
