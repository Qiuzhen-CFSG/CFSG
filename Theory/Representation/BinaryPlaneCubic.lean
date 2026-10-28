module
public import Theory.Representation.BinaryPlaneSolvable
public import Theory.GroupTheory.SymmetricThreePairCubic

/-!
# Subgroups acting faithfully on a binary plane

The binary plane linear group is the literal symmetric group on three
points. Its two-subgroups have order at most two; a nontrivial subgroup
with trivial two-core has a normal cubic. These are the only finite facts
needed in the degree-two branch of original 14.3.13.
-/

public section
open Subgroup Module
namespace Representation.BinaryPlane
open BinaryLinear.SmallParabolicLevi
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

noncomputable def symmetricThreeHom (ρ : Representation (ZMod 2) G V)
    (hd : finrank (ZMod 2) V = 2) : G →* Equiv.Perm (Fin 3) :=
  let e : V ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  (((linearGroupCongr e).trans linearTwoEquivSymmetricThree).toMonoidHom.comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom).comp ρ.asGroupHom

omit [Finite G] in
theorem symmetricThreeHom_injective (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 2) :
    Function.Injective (symmetricThreeHom ρ hd) := by
  intro a b he
  let e : V ≃ₗ[ZMod 2] BinaryLinear.OuterCyclic.Space 2 :=
    LinearEquiv.ofFinrankEq _ _ (by simpa using hd)
  have he' := ((linearGroupCongr e).trans linearTwoEquivSymmetricThree).injective he
  apply hf
  exact congrArg Units.val
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).injective he')

theorem two_subgroup_card_le_two (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 2)
    (A : Subgroup G) (hA : IsPGroup 2 A) : Nat.card A ≤ 2 := by
  have hc : Nat.card A ∣ 6 := by
    have hh := card_dvd_of_injective ((symmetricThreeHom ρ hd).comp A.subtype)
      ((symmetricThreeHom_injective ρ hf hd).comp A.subtype_injective)
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using hh
  obtain ⟨n,hn⟩ := hA.exists_card_eq
  have hn1 : n ≤ 1 := by
    by_contra hh
    have hbad : 4 ∣ 6 := (pow_dvd_pow 2 (by omega : 2 ≤ n)).trans (hn ▸ hc)
    norm_num at hbad
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hn1

theorem exists_normal_cubic (ρ : Representation (ZMod 2) G V)
    (hf : Function.Injective ρ) (hd : finrank (ZMod 2) V = 2)
    [Nontrivial G] (hcore : pCore 2 G = ⊥) :
    ∃ C : Subgroup G, C.Normal ∧ Nat.card C = 3 := by
  let f := (symmetricThreeHom ρ hd).prod (1 : G →* Equiv.Perm (Fin 3))
  have hi : Function.Injective f := by
    intro a b he
    exact symmetricThreeHom_injective ρ hf hd (congrArg Prod.fst he)
  exact Theory.GroupTheory.SymmetricThreePair.exists_normal_cubic_of_injective f hi hcore

end Representation.BinaryPlane
