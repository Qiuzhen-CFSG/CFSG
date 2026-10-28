module

public import Theory.Mathieu.M22.ValueBoundParabolics.SmallQuotients
public import Theory.SpecificGroups.Alternating.FiveExtensionAction

/-!
# Automorphism two-rank of the five-letter symmetric group

Restriction to the characteristic alternating subgroup embeds Aut(S₅) into
Aut(A₅) ≃ S₅: an automorphism fixing A₅ preserves each permutation's faithful
conjugation action on A₅. The dihedral Sylow calculation for S₅ therefore
bounds its automorphism two-rank by two. Faithfulness also gives trivial
center, and normal-subgroup simplicity excludes a nontrivial two-core.

These facts control the centralizer local in two-extensions of HS, as used
in Aschbacher–Smith E.1.14(5), printed p.214. The imported automorphism
identification follows GLS3, Theorem 5.2.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricFive

/-- Faithful conjugation on A₅ makes the center of S₅ trivial. -/
theorem center_eq_bot : center (Equiv.Perm (Fin 5)) = ⊥ := by
  apply eq_bot_iff.mpr
  intro g hg
  apply mem_bot.mpr
  apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).injective
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change g * x.val * g⁻¹ = 1 * x.val * 1⁻¹
  rw [← (mem_center_iff.mp hg x.val)]
  simp

/-- A nontrivial normal subgroup of S₅ contains A₅, so its two-core is trivial. -/
theorem pCore_two_eq_bot : pCore 2 (Equiv.Perm (Fin 5)) = ⊥ := by
  by_contra hn
  have hnt : Nontrivial (pCore 2 (Equiv.Perm (Fin 5))) := (nontrivial_iff_ne_bot _).mpr hn
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (by simp : 5 ≤ Nat.card (Fin 5)) hnt
  have hdiv : 60 ∣ Nat.card (pCore 2 (Equiv.Perm (Fin 5))) := by
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    exact hc ▸ card_dvd_of_le hle
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := Equiv.Perm (Fin 5))).exists_card_eq
  have hthree : 3 ∣ 2 ^ n := hn ▸ (dvd_trans (by decide : 3 ∣ 60) hdiv)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hthree)

private theorem symmetricFive_restriction_injective : Function.Injective
    (MulAut.characteristic (alternatingGroup (Fin 5))) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro f hf
  apply Subgroup.mem_bot.mpr
  have hfq (q : alternatingGroup (Fin 5)) : f (q : Equiv.Perm (Fin 5)) = q :=
    congrArg Subtype.val (DFunLike.congr_fun (MonoidHom.mem_ker.mp hf) q)
  apply MulEquiv.ext
  intro p
  apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
    (by decide) (by decide)).injective
  apply MulEquiv.ext
  intro q
  apply Subtype.ext
  change f p * (q : Equiv.Perm (Fin 5)) * (f p)⁻¹ =
    p * (q : Equiv.Perm (Fin 5)) * p⁻¹
  calc
    _ = f (p * (q : Equiv.Perm (Fin 5)) * p⁻¹) := by
      rw [map_mul, map_mul, map_inv, hfq q]
    _ = _ := hfq (MulAut.conjNormal p q)

/-- Restriction to A₅ bounds the two-rank of the full automorphism group. -/
theorem automorphism_primeRank_two_le :
    primeRank 2 (MulAut (Equiv.Perm (Fin 5))) ≤ 2 := by
  let e := Theory.SpecificGroups.Alternating.FiveExtensionAction.symmetricAutEquiv
  have h := Theory.GroupTheory.primeRank_le_of_injective 2
    (MulAut.characteristic (alternatingGroup (Fin 5))) symmetricFive_restriction_injective
  exact h.trans ((primeRank_equiv 2 e).symm.le.trans
    Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two)

end Theory.SpecificGroups.SymmetricFive
