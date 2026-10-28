module
public import Theory.GroupTheory.PGroup.SupercriticalAutomorphisms

/-!
# Nontrivial coprime actions on supercritical subgroups

Restriction to a supercritical subgroup has p-group kernel. A nontrivial
finite actor of order prime to p cannot have its whole image in that
kernel, so its restriction remains nontrivial. Faithfulness of the actor
on the ambient p-group is unnecessary.

Source application: Aschbacher--Smith A.1.21(3), printed pp.24--25,
applied to the five-core in the proof of 12.6.26, printed p.832.
-/

public section
open Subgroup
namespace IsSupercriticalPSubgroup
variable {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
  {X : Subgroup P}

/-- A coprime action detected on P remains nontrivial on its supercritical subgroup. -/
theorem coprime_action_ne_one (hX : IsSupercriticalPSubgroup p X)
    (hP : IsPGroup p P) (hp : Odd p)
    {A : Type*} [Group A] [Finite A] (a : A →* MulAut P)
    (ha : a ≠ 1) (hcop : Nat.Coprime (Nat.card A) p) :
    letI : X.Characteristic := hX.characteristic
    (MulAut.characteristic X).comp a ≠ 1 := by
  let : X.Characteristic := hX.characteristic
  intro hz
  have hle : a.range ≤ (MulAut.characteristic X).ker := by
    rintro _ ⟨x,rfl⟩
    exact DFunLike.congr_fun hz x
  have hpow := (hX.isPGroup_restriction_kernel hP hp).to_le hle
  obtain ⟨n,hn⟩ := hpow.exists_card_eq
  have hc : Nat.card a.range = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_right n)
    (card_dvd_of_surjective a.rangeRestrict a.rangeRestrict_surjective) (hn ▸ dvd_rfl)
  have he := card_eq_one.mp hc
  apply ha
  apply MonoidHom.ext
  intro x
  exact mem_bot.mp (he ▸ (show a x ∈ a.range from ⟨x,rfl⟩))
end IsSupercriticalPSubgroup
