module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.ResidualTransport
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic
public import Theory.GroupTheory.PPerfectHom
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Selecting the source rank-one residual

The theta identity of 15.3.11(6) makes `Y₊` two-perfect. Its image under
the assumed `S₃` shadow therefore has trivial sign and lies in `A₃`.
The image kernel is a two-group, so the index of `O₂(Y₊)` divides three.
Nontriviality excludes index one. This rules out the order-nine and
order-twenty-seven alternative of 15.3.11(5), selecting its second case
and its genuine prime-to-three residual identity.

Only the numerical consequence of (5i) is needed in the disjunction below;
(5ii) retains both the uniqueness condition and the exact residual choice
in Hypothesis 15.3.10(2). The first-plane centralization is deduced from
that choice. No conclusion of 15.3.35 is used.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.43(a),(b), printed p.1139; earlier 15.3.11(5),(6),(9), p.1123.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne
variable {G : Type*} [Group G] [Finite G]

/-- The sign character kills the theta-generated subgroup in the `S₃` shadow. -/
theorem index_dvd_three_of_shadow {Yplus S : Subgroup G}
    (hshadow : SymmetricThreeShadow Yplus S) (htheta : theta Yplus = Yplus) :
    (pCore 2 Yplus).index ∣ 3 := by
  obtain ⟨e⟩ := hshadow
  let j : Yplus →* (Yplus ⊔ S : Subgroup G) := inclusion le_sup_left
  let q := QuotientGroup.mk' (pCore 2 (Yplus ⊔ S : Subgroup G))
  let f := e.toMonoidHom.comp (q.comp j)
  have hperfect : IsPPerfect 2 Yplus := htheta ▸ ComponentIntersection.theta_isPPerfect Yplus
  have hu : IsPGroup 2 ℤˣ := IsPGroup.of_card (n := 1) (by
    simp [Nat.card_eq_fintype_card, Fintype.card_units_int])
  have hs := hperfect.hom_eq_one_of_isPGroup hu (Equiv.Perm.sign.comp f)
  have hfg (y : Yplus) : f y ∈ alternatingGroup (Fin 3) :=
    Equiv.Perm.mem_alternatingGroup.mpr (DFunLike.congr_fun hs y)
  let g := f.codRestrict (alternatingGroup (Fin 3)) hfg
  have hk : IsPGroup 2 g.ker := by
    have he : g.ker = (pCore 2 (Yplus ⊔ S : Subgroup G)).comap j := by
      ext x
      change (g x = 1) ↔ _
      rw [Subtype.ext_iff]
      change e (q (j x)) = 1 ↔ _
      rw [← e.map_one, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff (j x)
    rw [he]
    exact pCore_isPGroup.comap_of_injective j (inclusion_injective _)
  have hle : g.ker ≤ pCore 2 Yplus := le_sSup ⟨inferInstance, hk⟩
  have hd : (pCore 2 Yplus).index ∣ Nat.card (alternatingGroup (Fin 3)) :=
    (index_dvd_of_le hle).trans (by
    rw [index_ker]
    exact g.range.card_subgroup_dvd_card)
  have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  exact hc ▸ hd

/-- Nontriviality gives exactly three, not just a bound on the three-rank. -/
theorem index_three_of_shadow {Yplus S : Subgroup G}
    (hshadow : SymmetricThreeShadow Yplus S)
    (htheta : theta Yplus = Yplus) (hne : Yplus ≠ ⊥) :
    (pCore 2 Yplus).index = 3 := by
  have hd := index_dvd_three_of_shadow hshadow htheta
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · have htop : pCore 2 Yplus = ⊤ := index_eq_one.mp h
    have hp : IsPGroup 2 Yplus := (htop ▸ pCore_isPGroup).of_equiv topEquiv
    have hperfect : IsPPerfect 2 Yplus := htheta ▸ ComponentIntersection.theta_isPPerfect Yplus
    have hid := hperfect.hom_eq_one_of_isPGroup hp (MonoidHom.id Yplus)
    apply (hne ((eq_bot_iff_forall Yplus).mpr ?_)).elim
    intro x hx
    exact congrArg Subtype.val (DFunLike.congr_fun hid (⟨x, hx⟩ : Yplus))
  · exact h

/-- Clause (a) and the full second choice of Hypothesis 15.3.10, selected from 15.3.11(5). -/
theorem rank_one_choice_of_preliminary_alternative
    {Yplus Y S M I V₁ : Subgroup G}
    (hshadow : SymmetricThreeShadow Yplus S)
    (htheta : theta (M ⊓ I) = Yplus) (hne : Yplus ≠ ⊥)
    (h11 : 3 < (pCore 2 Yplus).index ∨
      ((Chapter4.UniqueMaximalOvergroup (Y ⊔ S) M ∧
          Yplus = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G))) ∧
        Yplus = threeResidualIn (M ⊓ I))) :
    (Chapter4.UniqueMaximalOvergroup (Y ⊔ S) M ∧
      Yplus = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G))) ∧
    Yplus = threeResidualIn (M ⊓ I) ∧ (pCore 2 Yplus).index = 3 := by
  have hi := index_three_of_shadow hshadow
    (by rw [← htheta, theta_idempotent]) hne
  rcases h11 with hbad | ⟨hchoice, hres⟩
  · omega
  · exact ⟨hchoice, hres, hi⟩

omit [Finite G] in
/-- The first assertion of (b) follows from the selected centralizer residual. -/
theorem centralizes_first_plane_of_residual_choice {Yplus Y V₁ : Subgroup G}
    (hchoice : Yplus = Stellmacher.twoResidualAmbient (Y ⊓ centralizer (V₁ : Set G))) :
    ⁅V₁, Yplus⁆ = ⊥ := by
  apply commutator_eq_bot_iff_le_centralizer.mpr
  apply le_centralizer_iff.mpr
  rw [hchoice]
  exact (map_subtype_le _).trans inf_le_right

end CFSG.Quasithin.Chapter15.Section03.RankOne
