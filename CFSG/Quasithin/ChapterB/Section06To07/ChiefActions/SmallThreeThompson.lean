module
public import CFSG.Quasithin.ChapterB.Section06To07.ChiefActions.SmallThompson
public import Theory.GroupTheory.SpecificGroups.PermThreeNormalKernel

/-!
# The original Thompson image on a symmetric-three chief factor

A normal subgroup of S₃ containing a nontrivial two-subgroup is all of S₃.
The maximum elementary actor from the source belongs to the original global
Thompson subgroup. Its nontrivial chief image therefore proves that the
literal Thompson image is the whole symmetric-three actor.

Source: Aschbacher–Smith, 3.1.9(5) and15.1.12(3), pp.577,1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.ChapterB

theorem normal_three_eq_top_of_contains_two
    (N A : Subgroup (Equiv.Perm (Fin 3))) [N.Normal]
    (hA : IsPGroup 2 A) (hAN : A ≤ N) (hne : A ≠ ⊥) : N = ⊤ := by
  have hq : IsPGroup 2 (Equiv.Perm (Fin 3) ⧸ N) :=
    quotient_isPGroup_two_of_perm_three_normal_kernel ⊥ N A IsPGroup.of_bot
      (MonoidHom.id _) Function.surjective_id (by simp) hA hAN
      (fun h => hne (le_bot_iff.mp h))
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd : N.index ∣ 6 := by rw [←hc]; exact N.index_dvd_card
  have hcop : Nat.Coprime N.index 3 := by
    obtain ⟨n,hn⟩ := hq.exists_card_eq
    change Nat.card (Equiv.Perm (Fin 3) ⧸ N) = _ at hn
    change Nat.Coprime (Nat.card (Equiv.Perm (Fin 3) ⧸ N)) 3
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hd2 : N.index ∣ 2 := hcop.dvd_mul_right.mp hd
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with hi | hi
  · exact index_eq_one.mp hi
  · have hNc : Nat.card N = 3 := by have hh := N.index_mul_card; rw [hi,hc] at hh; omega
    have hAc : Nat.card A ∣ 3 := by simpa only [hNc] using card_dvd_of_le hAN
    have hodd : Nat.Coprime (Nat.card A) 3 := by
      obtain ⟨n,hn⟩ := hA.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    exact (hne (card_eq_one.mp (hodd.eq_one_of_dvd hAc))).elim

variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
theorem chief_three_thompson_image
    (ρ : Representation (ZMod 2) G W) (S : Sylow 2 G)
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G))
    (hoff : IsOffender (imageRepresentation ρ) (actionSubgroup ρ A))
    (e : actionImage ρ ≃* Equiv.Perm (Fin 3)) :
    (elementaryAbelianMaxJ (⊤ : Subgroup G)).map (actionHom ρ) = ⊤ := by
  let J := elementaryAbelianMaxJ (⊤ : Subgroup G)
  let : J.Characteristic := elementaryAbelianMaxJ_top_characteristic
  let q := e.toMonoidHom.comp (actionHom ρ)
  have hq : Function.Surjective q := e.surjective.comp ρ.asGroupHom.rangeRestrict_surjective
  let : (J.map q).Normal := Subgroup.Normal.map inferInstance q hq
  have hne : A.map q ≠ ⊥ := by
    intro hh
    have hh' : (actionSubgroup ρ A).map e.toMonoidHom = ⊥ := by
      change (A.map (actionHom ρ)).map e.toMonoidHom = ⊥
      simpa only [q,Subgroup.map_map] using hh
    exact hoff.1.1 ((Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hh')
  have hjtop : J.map q = ⊤ := normal_three_eq_top_of_contains_two _ _
    ((hA.2.1.isPGroup).map q)
    (Subgroup.map_mono ((le_sSup hA).trans (elementaryAbelianMaxJ_sylow_le_top S))) hne
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [Subgroup.map_map,Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
    using hjtop
end CFSG.Quasithin.ChapterB
