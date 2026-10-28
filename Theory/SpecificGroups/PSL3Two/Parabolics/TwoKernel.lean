module
public import Theory.SpecificGroups.PSL3Two.Parabolics.SolvableOvergroups
public import Theory.GroupTheory.SolvableSylowOvergroupLifts

/-!
# Parabolics above a two-group kernel in PSL₃(2)

A two-group kernel lies in every Sylow two-subgroup. Thus the subgroup
correspondence lifts the two order-24 parabolics of PSL₃(2) to the original
group. Every subgroup containing the original Sylow is the Sylow itself,
one of these two proper parabolics, or the whole group. The parabolics are
solvable, since both their images and their kernels are solvable.

This gives actual subgroups, their intersection and their exhaustive interval,
rather than an unconnected model label. The source application is the
uniqueness step in Aschbacher–Smith 13.4.10(8) and 13.4.12, pp.909–911.
The imported matrix model retains the ATLAS attribution in LICENSES/ATLAS.txt.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Matrix.PSL3Two

private theorem interval_of_card_twentyFour
    (S : Sylow 2 PSL) (P U : Subgroup PSL)
    (hP : Nat.card P = 24) (hSU : (S : Subgroup PSL) ≤ U) (hUP : U ≤ P) :
    U = (S : Subgroup PSL) ∨ U = P := by
  have h8 : 8 ∣ Nat.card U := card_sylow_two S ▸ card_dvd_of_le hSU
  have hd : Nat.card U ∣ 24 := hP ▸ card_dvd_of_le hUP
  have hb := Nat.le_of_dvd (by decide : 0 < 24) hd
  have he : Nat.card U = 8 ∨ Nat.card U = 24 := by
    interval_cases hc : Nat.card U <;> omega
  rcases he with he | he
  · exact Or.inl (eq_of_le_of_card_ge hSU (by rw [he, card_sylow_two])).symm
  · exact Or.inr (eq_of_le_of_card_ge hUP (by rw [he, hP]))

/-- The complete Sylow-overgroup interval lifts through the specified surjection. -/
theorem two_kernel_parabolics {X : Type*} [Group X] [Finite X]
    (S : Sylow 2 X) (f : X →* PSL) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker) :
    ∃ P Q : Subgroup X,
      IsCoatom P ∧ IsCoatom Q ∧ P ≠ Q ∧
      P ⊓ Q = (S : Subgroup X) ∧
      (S : Subgroup X) < P ∧ (S : Subgroup X) < Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧
      ∀ U : Subgroup X, (S : Subgroup X) ≤ U →
        U = (S : Subgroup X) ∨ U = P ∨ U = Q ∨ U = ⊤ := by
  let S' := S.mapSurjective hf
  have hker : f.ker ≤ (S : Subgroup X) := hk.le_sylow_of_normal S
  have hS : (S' : Subgroup PSL).comap f = (S : Subgroup X) :=
    comap_map_eq_self hker
  obtain ⟨P, Q, hP, hQ, hPQ, hI, hPc, hQc, hmax⟩ := sylow_parabolics S'
  have hSP : (S' : Subgroup PSL) ≤ P := hI ▸ inf_le_left
  have hSQ : (S' : Subgroup PSL) ≤ Q := hI ▸ inf_le_right
  have hSP' : (S : Subgroup X) ≤ P.comap f := by
    rw [← hS]
    exact comap_mono hSP
  have hSQ' : (S : Subgroup X) ≤ Q.comap f := by
    rw [← hS]
    exact comap_mono hSQ
  have hliftP : IsCoatom (P.comap f) := isCoatom_comap_of_surjective hf hP
  have hliftQ : IsCoatom (Q.comap f) := isCoatom_comap_of_surjective hf hQ
  have hs : SolvableSylowOvergroups X :=
    SolvableSylowOvergroups.of_two_kernel f hf hk solvableSylowOvergroups
  refine ⟨P.comap f, Q.comap f, hliftP, hliftQ,
    fun he => hPQ ((comap_injective hf) he), ?_, ?_, ?_,
    hs S _ hSP' hliftP.ne_top, hs S _ hSQ' hliftQ.ne_top, ?_⟩
  · rw [← comap_inf, hI, hS]
  · refine lt_of_le_of_ne hSP' ?_
    intro he
    have himage : (S' : Subgroup PSL) = P := by
      rw [Sylow.coe_mapSurjective]
      simpa only [map_comap_eq_self_of_surjective hf] using congrArg (fun U => U.map f) he
    have hc := card_sylow_two S'
    rw [himage, hPc] at hc
    omega
  · refine lt_of_le_of_ne hSQ' ?_
    intro he
    have himage : (S' : Subgroup PSL) = Q := by
      rw [Sylow.coe_mapSurjective]
      simpa only [map_comap_eq_self_of_surjective hf] using congrArg (fun U => U.map f) he
    have hc := card_sylow_two S'
    rw [himage, hQc] at hc
    omega
  · intro U hSU
    have hUS : (S' : Subgroup PSL) ≤ U.map f := map_mono hSU
    have hUc : (U.map f).comap f = U := comap_map_eq_self (hker.trans hSU)
    by_cases hU : U.map f = ⊤
    · exact Or.inr (Or.inr (Or.inr (by rw [← hUc, hU, comap_top])))
    obtain ⟨R, hR, hUR⟩ := (eq_top_or_exists_le_coatom (U.map f)).resolve_left hU
    rcases (hmax R hR).mp (hUS.trans hUR) with he | he
    · subst R
      rcases interval_of_card_twentyFour S' P (U.map f) hPc hUS hUR with he | he
      · exact Or.inl (by rw [← hUc, he, hS])
      · exact Or.inr (Or.inl (by rw [← hUc, he]))
    · subst R
      rcases interval_of_card_twentyFour S' Q (U.map f) hQc hUS hUR with he | he
      · exact Or.inl (by rw [← hUc, he, hS])
      · exact Or.inr (Or.inr (Or.inl (by rw [← hUc, he])))

end Matrix.PSL3Two
