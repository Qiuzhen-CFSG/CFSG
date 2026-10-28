module

public import Theory.PGroupCore
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Tactic.NormNum

/-!
# The two-core of the actual alternating group of degree five

Simplicity makes the two-core trivial or the whole group. The latter
alternative is impossible because three divides the order sixty.

Source application: the A₅ sections in Aschbacher–Smith, *The Classification
of Quasithin Groups*, Lemma 1.3.9, combined manuscript, printed p.514.
-/

public section
open Subgroup
namespace alternatingGroup

/-- The actual degree-five alternating group has trivial two-core. -/
theorem five_twoCore_eq_bot : pCore 2 (alternatingGroup (Fin 5)) = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (pCore 2 (alternatingGroup (Fin 5))) inferInstance with h | h
  · exact h
  · have hp : IsPGroup 2 (alternatingGroup (Fin 5)) := by
      have ht : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) :=
        h ▸ pCore_isPGroup
      exact ht.of_surjective
        (Subgroup.topEquiv (G := alternatingGroup (Fin 5))).toMonoidHom
        (Subgroup.topEquiv (G := alternatingGroup (Fin 5))).surjective
    obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
    have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [hc] at hn
    have h3 : 3 ∣ 2 ^ n := dvd_trans (by norm_num : 3 ∣ 60) hn
    exact False.elim (by simpa using (Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) h3))

end alternatingGroup
