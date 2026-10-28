module
public import Theory.GroupTheory.PerfectCentralCoverOddPart
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.GroupTheory.SpecificGroups.ZGroup
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Odd kernels of perfect binary actors of degree four

Let a finite perfect group act faithfully on a binary four-space and map
onto a group of order sixty with odd nilpotent kernel. The kernel is trivial.
Faithfulness bounds the group order by divisibility into |GL₄(2)| = 20160;
therefore the kernel order divides 21. A nilpotent group of this squarefree
order is cyclic. The perfect source centralizes its cyclic normal subgroup,
and cyclic-Sylow transfer excludes both possible kernel primes, three and seven.

This supplies the odd action-kernel step in the alternating-five case of
Niles, “Pushing-up in finite groups”, Lemmas 2.8–2.9, printed pp. 32–33.
The theorem retains the actual quotient map and assumes perfection only of
the faithful actor. Deriving that actor from the original group, together
with the degree-four bound, belongs to the source application.
-/

public section
noncomputable section
open Subgroup
namespace Representation.BinaryFourOddKernel

private theorem cyclic_normal_le_center {G : Type*} [Group G] [Group.IsPerfect G]
    (N : Subgroup G) [N.Normal] [IsCyclic N] : N ≤ center G := by
  let e := IsCyclic.mulAutMulEquiv N
  let : CommGroup (MulAut N) := e.toMonoidHom.commGroupOfInjective e.injective
  let a : G →* MulAut N := MulAut.conjNormal
  have ha (g : G) : a g = 1 :=
    Abelianization.commutator_subset_ker a Group.IsPerfect.mem_commutator
  intro x hx
  rw [mem_center_iff]
  intro g
  have hh := congrArg (fun t : MulAut N => (t ⟨x,hx⟩ : G)) (ha g)
  change g*x*g⁻¹=x at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

private theorem injective_of_card_dvd
    {G J : Type*} [Group G] [Finite G] [Group.IsPerfect G] [Group J] [Finite J]
    (hG : Nat.card G ∣ 20160) (f : G →* J) (hf : Function.Surjective f)
    (hJ : Nat.card J = 60) (ho : Odd (Nat.card f.ker)) [Group.IsNilpotent f.ker] :
    Function.Injective f := by
  have hc : Nat.card f.ker * 60 = Nat.card G := by
    have hh := f.ker.card_mul_index
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf] at hh
    have ht : Nat.card (⊤ : Subgroup J) = Nat.card J :=
      Nat.card_congr Subgroup.topEquiv.toEquiv
    simpa only [ht, hJ] using hh
  have hd336 : Nat.card f.ker ∣ 336 := by
    apply (Nat.mul_dvd_mul_iff_right (by decide : 0<60)).mp
    exact hc ▸ hG
  have hd21 : Nat.card f.ker ∣ 21 := by
    have hcop : (Nat.card f.ker).Coprime 16 := by
      exact (Nat.coprime_two_right.mpr ho).pow_right 4
    exact hcop.dvd_of_dvd_mul_left hd336
  have hs21 : Squarefree (21 : ℕ) := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hd
    have hh := Nat.le_of_dvd (by decide : 0 < 21) hd
    have : p ≤ 4 := by nlinarith
    have hlo := hp.two_le
    interval_cases p <;> norm_num at *
  let : IsZGroup f.ker := IsZGroup.of_squarefree (hs21.squarefree_of_dvd hd21)
  let : IsCyclic f.ker := inferInstance
  let c : PerfectCentralCovering.Cover G J :=
    { toMonoidHom := f
      surjective := hf
      isPerfect := inferInstance
      ker_le_center := cyclic_normal_le_center f.ker }
  apply f.ker_eq_bot_iff.mp
  apply Subgroup.eq_bot_of_card_eq
  by_contra hn
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hn
  let : Fact p.Prime := ⟨hp⟩
  have hp37 : p=3 ∨ p=7 := by
    rcases hp.dvd_mul.mp (show p ∣ 3*7 from hd.trans hd21) with hh | hh
    · exact Or.inl (((Nat.dvd_prime Nat.prime_three).mp hh).resolve_left hp.ne_one)
    · exact Or.inr (((Nat.dvd_prime (by decide : Nat.Prime 7)).mp hh).resolve_left hp.ne_one)
  apply c.not_dvd_card_kernel_of_square_not_dvd (p:=p) ?_ hd
  rcases hp37 with rfl | rfl <;> norm_num [hJ]

/-- The actual quotient map with odd nilpotent kernel is injective when its
perfect source has a faithful binary action of degree four and its target
has order sixty. -/
theorem injective_of_odd_nilpotent_kernel_card_sixty
    {G J W : Type*} [Group G] [Finite G] [Group.IsPerfect G] [Group J] [Finite J]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W=4)
    (f : G →* J) (hf : Function.Surjective f) (hJ : Nat.card J=60)
    (ho : Odd (Nat.card f.ker)) [Group.IsNilpotent f.ker] :
    Function.Injective f := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) W hdim
  let φ : G →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφ : Function.Injective φ := by
    apply (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp
    intro g h he
    exact hρ (congrArg Units.val he)
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2))=20160 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  apply injective_of_card_dvd (hGL ▸ Subgroup.card_dvd_of_injective φ hφ) f hf hJ ho

/-- In particular, an alternating-five quotient of such a faithful perfect
binary actor has trivial odd nilpotent kernel, with its original map retained. -/
theorem injective_alternatingFive_of_odd_nilpotent_kernel
    {G W : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) (hρ : Function.Injective ρ)
    (hdim : Module.finrank (ZMod 2) W=4)
    (f : G →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (ho : Odd (Nat.card f.ker)) [Group.IsNilpotent f.ker] :
    Function.Injective f := by
  apply injective_of_odd_nilpotent_kernel_card_sixty ρ hρ hdim f hf ?_ ho
  rw [nat_card_alternatingGroup]
  norm_num [Nat.factorial]
end Representation.BinaryFourOddKernel
