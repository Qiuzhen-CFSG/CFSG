module

public import Theory.GroupTheory.Commutator.PerfectSmallIndex
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Perfect overgroups of order-360 subgroups in A₈

The relative index divides 56. A perfect group has no proper subgroup of
index at most four, while simplicity of A₈ rules out proper ambient indices
below eight. Thus only relative indices 1, 7 and 56 survive. In the middle
case the faithful eight-coset action, restricted to the seven cosets other
than the fixed base coset, gives an actual A₇ equivalence. This avoids any
maximal-overgroup table or classification of embeddings of A₆.

The finite certificate tests only the 57 integers from 0 through 56 for
being divisors of 56. Source application: Aschbacher–Smith, Proposition
8.2.8(1), printed p.719/PDF p.736, the M₂₄-code row.
-/

public section
open Subgroup
namespace BinaryAlternatingSixPerfectOvergroups

private theorem perfect_le_alternating {G : Type*} [Group G] [Group.IsPerfect G]
    {α : Type*} [Fintype α] [DecidableEq α] (f : G →* Equiv.Perm α) :
    f.range ≤ alternatingGroup α := by
  let s := Equiv.Perm.sign.comp f
  let : Group.IsPerfect s.range := Group.IsPerfect.range s
  rintro _ ⟨g, rfl⟩
  exact Equiv.Perm.mem_alternatingGroup.mpr
    (congrArg Subtype.val (Subsingleton.elim (⟨s g, ⟨g, rfl⟩⟩ : s.range) 1))

private def restrictFixed {G : Type*} [Group G]
    (f : G →* Equiv.Perm (Fin 8)) (i : Fin 8) (hi : ∀ g, f g i = i) :
    G →* Equiv.Perm {j : Fin 8 // j ≠ i} where
  toFun g := (f g).subtypePerm (fun j => by
    simpa only [hi g] using (f g).injective.ne_iff (x := j) (y := i))
  map_one' := by
    apply Equiv.ext
    intro j
    apply Subtype.ext
    exact congrArg (fun p : Equiv.Perm (Fin 8) => p j.val) f.map_one
  map_mul' g h := by
    apply Equiv.ext
    intro j
    apply Subtype.ext
    exact congrArg (fun p : Equiv.Perm (Fin 8) => p j.val) (f.map_mul g h)

private theorem restrictFixed_injective {G : Type*} [Group G]
    (f : G →* Equiv.Perm (Fin 8)) (hf : Function.Injective f)
    (i : Fin 8) (hi : ∀ g, f g i = i) :
    Function.Injective (restrictFixed f i hi) := by
  intro g h he
  apply hf
  apply Equiv.ext
  intro j
  by_cases hj : j = i
  · subst j; rw [hi g, hi h]
  · exact congrArg (fun p : Equiv.Perm {j : Fin 8 // j ≠ i} => (p ⟨j, hj⟩).val) he

/-- A perfect index-eight subgroup is A₇, via the action on the other seven cosets. -/
theorem index_eight_equiv (H : Subgroup (alternatingGroup (Fin 8)))
    [Group.IsPerfect H] (hi : H.index = 8) :
    Nonempty (H ≃* alternatingGroup (Fin 7)) := by
  classical
  let A8 := alternatingGroup (Fin 8)
  let : IsSimpleGroup A8 := alternatingGroup.isSimpleGroup (by simp)
  have hnt : H ≠ ⊤ := by intro h; simp [h] at hi
  let f := MulAction.toPermHom A8 (A8 ⧸ H)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [← H.normalCore_eq_ker]
    rcases H.normalCore_normal.eq_bot_or_eq_top with h | h
    · exact h
    · exact (hnt (top_le_iff.mp (h ▸ H.normalCore_le))).elim
  let e : (A8 ⧸ H) ≃ Fin 8 := (Finite.equivFin (A8 ⧸ H)).trans (finCongr hi)
  let p := e.permCongrHom.toMonoidHom.comp (f.comp H.subtype)
  have hp : Function.Injective p := e.permCongrHom.injective.comp
    (hf.comp H.subtype_injective)
  let i := e (QuotientGroup.mk (1 : A8))
  have hfix (h : H) : p h i = i := by
    change e (h.val • e.symm (e (QuotientGroup.mk (1 : A8)))) = _
    rw [e.symm_apply_apply]
    apply e.injective.eq_iff.mpr
    change QuotientGroup.mk (h.val * 1) = QuotientGroup.mk (1 : A8)
    simp [QuotientGroup.eq, h.property]
  let q := (finSuccAboveEquiv i).symm.permCongrHom.toMonoidHom.comp
    (restrictFixed p i hfix)
  have hq : Function.Injective q :=
    (finSuccAboveEquiv i).symm.permCongrHom.injective.comp
      (restrictFixed_injective p hp i hfix)
  have hcard : Nat.card H = 2520 := by
    have hc := H.card_mul_index
    rw [hi, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    rw [Nat.card_eq_fintype_card]
    omega
  have hr : q.range = alternatingGroup (Fin 7) := by
    apply eq_of_le_of_card_ge (perfect_le_alternating q)
    rw [← Nat.card_congr (MonoidHom.ofInjective hq).toEquiv, hcard,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  exact ⟨(MonoidHom.ofInjective hq).trans (MulEquiv.subgroupCongr hr)⟩

/-- Perfect overgroups of an order-360 subgroup of A₈. -/
theorem permutation_alternatives (A H : Subgroup (alternatingGroup (Fin 8)))
    [Group.IsPerfect H] (hA : Nat.card A = 360) (hAH : A ≤ H) :
    H = A ∨ Nonempty (H ≃* alternatingGroup (Fin 7)) ∨ H = ⊤ := by
  let : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have hAi : A.index = 56 := by
    have hc := A.card_mul_index
    rw [hA, nat_card_alternatingGroup] at hc
    norm_num [Nat.factorial] at hc
    omega
  have hm : A.relIndex H * H.index = 56 := (relIndex_mul_index hAH).trans hAi
  have hd : A.relIndex H ∣ 56 := hAi ▸ relIndex_dvd_index_of_le hAH
  have hb : A.relIndex H ≤ 56 := Nat.le_of_dvd (by decide) hd
  have hc : A.relIndex H = 1 ∨ A.relIndex H = 2 ∨ A.relIndex H = 4 ∨
      A.relIndex H = 7 ∨ A.relIndex H = 8 ∨ A.relIndex H = 14 ∨
      A.relIndex H = 28 ∨ A.relIndex H = 56 :=
    (by decide : ∀ n ∈ Finset.range 57, n ∣ 56 → n = 1 ∨ n = 2 ∨ n = 4 ∨
      n = 7 ∨ n = 8 ∨ n = 14 ∨ n = 28 ∨ n = 56)
      _ (Finset.mem_range.mpr (by omega)) hd
  have hsmall (h : A.relIndex H ≤ 4) : H = A := by
    let : Group.IsPerfect (⊤ : Subgroup H) :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := H)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := H)).symm.surjective
    have ht : A.subgroupOf H = ⊤ := top_unique
      (le_of_isPerfect_of_index_le_four ⊤ (A.subgroupOf H) h)
    exact le_antisymm (subgroupOf_eq_top.mp ht) hAH
  have hlarge (h : H.index ≤ 7) : H = ⊤ := by
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    calc
      H.index.factorial ≤ Nat.factorial 7 := Nat.factorial_le h
      _ < Nat.card (alternatingGroup (Fin 8)) := by
        rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
  rcases hc with h | h | h | h | h | h | h | h
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp h) hAH)
  · exact Or.inl (hsmall (by omega))
  · exact Or.inl (hsmall (by omega))
  · exact Or.inr (Or.inl (index_eight_equiv H (by rw [h] at hm; omega)))
  · exact Or.inr (Or.inr (hlarge (by rw [h] at hm; omega)))
  · exact Or.inr (Or.inr (hlarge (by rw [h] at hm; omega)))
  · exact Or.inr (Or.inr (hlarge (by rw [h] at hm; omega)))
  · exact Or.inr (Or.inr (hlarge (by rw [h] at hm; omega)))

end BinaryAlternatingSixPerfectOvergroups
