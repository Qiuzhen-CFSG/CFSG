module
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.PrimeActors
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import Theory.GroupTheory.SolvableSylowOvergroups.CubicSections
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Solvable Rudvalis Sylow overgroups containing a cubic

The native odd-index maximal cover places the overgroup in max4 or max6.
Their literal surjective maps to L₃(2) and S₅ have two-group kernels.
The small-quotient argument bounds every odd subgroup by three. The
Chapter6 application supplies the proved cover and the original right
Hall cubic, then excludes the escaping Cartan action on that same carrier.

Source: Aschbacher--Smith A.3.12(20) and 5.1.13, printed pp.47--48,637.
The imported ATLAS RuG1 word programs and quotient certificates retain
their source attribution and license; no new finite enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Rudvalis.SylowOvergroups

/-- An odd subgroup of a solvable full-Sylow overgroup containing a cubic
has order dividing three, under the literal native maximal-overgroup cover. -/
theorem odd_card_dvd_three_of_cubic
    (hcover : OddIndexMaximalCover) (S : Sylow 2 Model) (J E : Subgroup Model)
    (hSJ : (S : Subgroup Model) ≤ J) (hJ : J ≠ ⊤)
    (hs : Group.IsSolvable J) (h3 : 3 ∣ Nat.card J)
    (hEJ : E ≤ J) (ho : Odd (Nat.card E)) : Nat.card E ∣ 3 := by
  obtain ⟨M,hM,hJM⟩ := (eq_top_or_exists_le_coatom J).resolve_left hJ
  have hodd : ¬ 2 ∣ M.index := fun hd =>
    S.not_dvd_index (hd.trans (index_dvd_of_le (hSJ.trans hJM)))
  have branch {X : Type} [Group X] [Finite X] (e : M ≃* X)
      {Q : Type} [Group Q] [Finite Q] (f : X →* Q)
      (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
      (hc : Nat.card Q = 120 ∨ Nat.card Q = 168) (hn : ¬ Group.IsSolvable Q) :
      Nat.card E ∣ 3 := by
    let P := (S.subtype (hSJ.trans hJM)).mapSurjective (f := e.toMonoidHom) e.surjective
    let U := (J.subgroupOf M).map e.toMonoidHom
    let D := (E.subgroupOf M).map e.toMonoidHom
    have hU : Nat.card U = Nat.card J := (card_map_of_injective e.injective).trans
      (Nat.card_congr (subgroupOfEquivOfLe hJM).toEquiv)
    have hD : Nat.card D = Nat.card E := (card_map_of_injective e.injective).trans
      (Nat.card_congr (subgroupOfEquivOfLe (hEJ.trans hJM)).toEquiv)
    let := hs
    let : Group.IsSolvable (J.subgroupOf M) := Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe hJM).toMonoidHom) (subgroupOfEquivOfLe hJM).injective
    let : Group.IsSolvable U := Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _)
    have hh := odd_card_dvd_three_of_small_nonsolvable_quotient f hf hk hc hn P U D
      (map_mono (comap_mono hSJ)) inferInstance (hU ▸ h3)
      (map_mono (comap_mono hEJ)) (hD ▸ ho)
    rwa [hD] at hh
  rcases hcover M hM hodd with he | he
  · obtain ⟨e⟩ := he
    exact branch e CoreQuotients.max4LinearAction CoreQuotients.max4LinearAction_surjective
      (by rw [CoreQuotients.max4LinearAction_ker_eq_pCore]; exact pCore_isPGroup)
      (.inr Matrix.PSL3Two.card_PSL) _root_.not_isSolvable_psl3_two
  · obtain ⟨e⟩ := he
    apply branch e CoreQuotients.max6FiveAction CoreQuotients.max6FiveAction_surjective
      (by rw [CoreQuotients.max6FiveAction_ker]; exact pCore_isPGroup)
      (.inl (by norm_num [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial]))
    intro hs
    let := hs
    let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

end Rudvalis.SylowOvergroups
