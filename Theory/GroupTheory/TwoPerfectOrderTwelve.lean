module

public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# A two-perfect group of order twelve is A4

A Sylow three-subgroup has index four. Its normal core is trivial because
a normal cubic subgroup would give a nontrivial two-group quotient. The
faithful four-coset action lands in A4 by two-perfection, and the equal
orders give an isomorphism.

Application: the A3-block in Aschbacher--Smith F.6.13, printed p.307.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
theorem alternatingFour_of_twoPerfect_card_twelve
    (hp : IsPPerfect 2 G) (hc : Nat.card G = 12) :
    Nonempty (G ≃* alternatingGroup (Fin 4)) := by
  classical
  let P : Sylow 3 G := Classical.choice inferInstance
  have hPc : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hc]
    have hf : Nat.factorization 12 3 = 1 := by
      change Nat.factorization (2 ^ 2 * 3) 3 = 1
      rw [Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
      norm_num [Nat.prime_two.factorization, Nat.prime_three.factorization]
    rw [hf, pow_one]
  have hPi : (P : Subgroup G).index = 4 := by
    have hh := (P : Subgroup G).index_mul_card
    rw [hPc, hc] at hh
    omega
  have hcore : (P : Subgroup G).normalCore = ⊥ := by
    have hd : Nat.card (P : Subgroup G).normalCore ∣ 3 := by
      have hh := card_dvd_of_le (P : Subgroup G).normalCore_le
      rwa [hPc] at hh
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact card_eq_one.mp h1
    · have hi : (P : Subgroup G).normalCore.index = 4 := by
        have hh := (P : Subgroup G).normalCore.index_mul_card
        rw [h3, hc] at hh
        omega
      have ht := hp (P : Subgroup G).normalCore inferInstance
        (IsPGroup.of_card (n := 2) (by change (P : Subgroup G).normalCore.index = 2 ^ 2; exact hi))
      have hh := index_eq_one.mpr ht
      omega
  let points := G ⧸ (P : Subgroup G)
  let ep : points ≃ Fin 4 := (Finite.equivFin points).trans (finCongr hPi)
  let a : G →* Equiv.Perm points := MulAction.toPermHom G points
  let f : G →* Equiv.Perm (Fin 4) := (Equiv.permCongrHom ep).toMonoidHom.comp a
  have hker : f.ker = ⊥ := by
    rw [MonoidHom.ker_comp_of_injective _ _ (Equiv.permCongrHom ep).injective]
    exact (P : Subgroup G).normalCore_eq_ker.symm.trans hcore
  have hf : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hR : f.range ≤ alternatingGroup (Fin 4) := by
    have hm := map_pResidual_le 2 f
    rw [(pResidual_eq_top_iff 2 G).mpr hp, ← MonoidHom.range_eq_map] at hm
    apply hm.trans
    apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 4)).index = 2 ^ 1
    simp
  let r := f.codRestrict (alternatingGroup (Fin 4)) (fun x => hR ⟨x, rfl⟩)
  have hr : Function.Injective r := fun x y hh => hf (congrArg Subtype.val hh)
  have hcard : Nat.card G = Nat.card (alternatingGroup (Fin 4)) := by
    rw [hc, nat_card_alternatingGroup, Nat.card_fin]
    rfl
  exact ⟨MulEquiv.ofBijective r ((Nat.bijective_iff_injective_and_card r).mpr ⟨hr, hcard⟩)⟩
end Theory.GroupTheory
