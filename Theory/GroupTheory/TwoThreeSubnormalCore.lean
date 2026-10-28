module
public import Theory.GroupTheory.TwoThreeSolvable
public import Theory.GroupTheory.CComponent.FittingCentralizer
/-!
# Subnormal {2,3}-subgroups and the two-core

If both the two- and three-cores of a finite group vanish, a subnormal
{2,3}-subgroup has trivial Fitting subgroup. Burnside solvability then
makes it trivial. Applying this to the literal quotient by O₂(G) places
every subnormal {2,3}-subgroup in O₂(G) whenever O₃(G/O₂(G)) vanishes.

Source: the subnormal reduction in Aschbacher–Smith 14.7.26, printed
p.1053, refs/quasithin.pdf. Its actual overgroup application is in
LocalReduction.ExtraspecialFourThreeCore.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- In a finite group with trivial two- and three-cores, a subnormal
{2,3}-subgroup is trivial. -/
theorem eq_bot_of_subnormal_two_three
    (h2 : pCore 2 G = ⊥) (h3 : pCore 3 G = ⊥)
    (J : Subgroup G) (hJ : J.IsSubnormal)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3) : J = ⊥ := by
  let : Group.IsSolvable J := isSolvable_of_prime_dvd_card_eq_two_or_three J hp
  have hcore (p : (Nat.card J).primeFactors.attach) : pCore p.val.val J = ⊥ := by
    have hprime := Nat.prime_of_mem_primeFactors p.val.property
    rcases hp p.val.val hprime (Nat.dvd_of_mem_primeFactors p.val.property) with h | h
    · rw [h,pCore_subnormal_eq_comap 2 hJ,h2,MonoidHom.comap_bot]
      exact J.subtype.ker_eq_bot J.subtype_injective
    · rw [h,pCore_subnormal_eq_comap 3 hJ,h3,MonoidHom.comap_bot]
      exact J.subtype.ker_eq_bot J.subtype_injective
  have hfit : fittingSubgroup J = ⊥ := by
    rw [fitting_eq_sup_pCore]
    simp only [hcore,iSup_bot]
  exact (eq_bot_iff_card J).mpr ((fitting_eq_bot_iff_card_eq_one_of_solvable J).mp hfit)

/-- If O₃(G/O₂(G)) is trivial, every subnormal {2,3}-subgroup is in O₂(G).
The image is taken under the actual two-core quotient map. -/
theorem le_twoCore_of_subnormal_two_three
    (h3 : pCore 3 (G ⧸ pCore 2 G) = ⊥)
    (J : Subgroup G) (hJ : J.IsSubnormal)
    (hp : ∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3) :
    J ≤ pCore 2 G := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hmap : J.map q = ⊥ := eq_bot_of_subnormal_two_three
    (pCore_quotient_pCore_eq_bot 2) h3 _ (hJ.map (QuotientGroup.mk'_surjective _))
    (fun p hp' hd => hp p hp' (hd.trans (card_map_dvd J q)))
  simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff J).mp hmap
end Subgroup
