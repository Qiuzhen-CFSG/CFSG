module
public import Theory.SpecificGroups.AlternatingSix.PerfectSubgroups
public import Theory.GroupTheory.Commutator.PerfectSmallIndex

/-!
# The residual of a nonsolvable six-letter group omitting A₆

The finite solvable residual is perfect and nontrivial. Its faithful image
on six letters is therefore A₆ or A₅, by the perfect-subgroup theorem.
If the ambient image omits A₆, this identifies the literal residual with A₅.

Source application: Aschbacher--Smith 14.3.23(2), printed p.1000.
The HS consumer retains the original faithful action and uses this normal
subgroup to obtain actual binary module coordinates.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]

/-- The literal solvable residual of a nonsolvable six-letter group whose
image omits A₆ is A₅. -/
theorem residual_equiv_alternatingFive
    (f : G →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (hs : ¬ Group.IsSolvable G) (ha : ¬ alternatingGroup (Fin 6) ≤ f.range) :
    Nonempty (solvableResidual G ≃* alternatingGroup (Fin 5)) := by
  let R := solvableResidual G
  have hn : R ≠ ⊥ := by
    intro hb
    obtain ⟨n, hn⟩ := exists_derivedSeries_eq_solvableResidual (G := G)
    exact hs ⟨n, hn.trans hb⟩
  let j := f.comp R.subtype
  have hj : Function.Injective j := hf.comp R.subtype_injective
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hjn : j.range ≠ ⊥ := by
    intro hb
    apply hn
    apply bot_unique
    intro x hx
    apply mem_bot.mpr
    have h : j ⟨x,hx⟩ = 1 := mem_bot.mp (hb ▸ (show j ⟨x,hx⟩ ∈ j.range from ⟨_,rfl⟩))
    exact congrArg Subtype.val (hj (h.trans j.map_one.symm))
  rcases AlternatingSix.PerfectSubgroups.symmetric_six j.range hjn with hA | hA
  · apply (ha ?_).elim
    rw [← hA]
    rintro _ ⟨x,rfl⟩
    exact ⟨x.val,rfl⟩
  · obtain ⟨e⟩ := hA
    exact ⟨(MonoidHom.ofInjective hj).trans e⟩

/-- Such a nonsolvable group has order sixty or one hundred twenty. -/
theorem card_eq_sixty_or_oneTwenty
    (f : G →* Equiv.Perm (Fin 6)) (hf : Function.Injective f)
    (hs : ¬ Group.IsSolvable G) (ha : ¬ alternatingGroup (Fin 6) ≤ f.range) :
    Nat.card G = 60 ∨ Nat.card G = 120 := by
  obtain ⟨e⟩ := residual_equiv_alternatingFive f hf hs ha
  have hR : Nat.card (solvableResidual G) = 60 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hdiv : 60 ∣ Nat.card G := hR ▸ (solvableResidual G).card_subgroup_dvd_card
  have hi : 5 ≤ f.range.index := by
    by_contra hn
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact ha (le_of_isPerfect_of_index_le_four _ _ (by omega))
  have hc := f.range.card_mul_index
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_perm,Nat.card_fin] at hc
  norm_num [Nat.factorial] at hc
  have hb : Nat.card G ≤ 144 := by nlinarith
  have hp : 0 < Nat.card G := Nat.card_pos
  obtain ⟨k,hk⟩ := hdiv
  omega

end Theory.SpecificGroups.SymmetricSix
