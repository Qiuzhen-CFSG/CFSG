module

public import Theory.Alternating.Aut
public import Theory.AtlasPort.OtherSporadic.GroupTheory.SmallIndexSimple
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Index-eight subgroups of A₈

The coset action of an index-eight subgroup is faithful by simplicity. Its
image is A₈ inside S₈, so the automorphism theorem identifies the original
subgroup with a point stabilizer. Transitivity then conjugates any two such
subgroups by an element of A₈ itself. An intermediate subgroup would have
index two or four, which simplicity excludes by its coset action; hence these
subgroups are maximal and self-normalizing.

This supplies the group-theoretic recognition used for the binary A₇ four-space
in Aschbacher–Smith, K.1.2, printed p.452 (PDF p.463). The automorphism input is
GLS, vol.3, Theorem 5.2.1, proved in `Theory.Alternating.Aut`.
-/

public section
open Subgroup
namespace GroupTheory.AlternatingIndexEight

local instance : IsSimpleGroup (alternatingGroup (Fin 8)) :=
  alternatingGroup.isSimpleGroup (by simp)

/-- Every index-eight subgroup of A₈ is a point stabilizer. -/
theorem index_eight_fixed (H : Subgroup (alternatingGroup (Fin 8))) (hi : H.index = 8) :
    ∃ i : Fin 8, ∀ g : alternatingGroup (Fin 8), g ∈ H ↔ g.val i = i := by
  classical
  let A := alternatingGroup (Fin 8)
  have hnt : H ≠ ⊤ := by intro h; simp [h] at hi
  let f := MulAction.toPermHom A (A ⧸ H)
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [← H.normalCore_eq_ker]
    rcases H.normalCore_normal.eq_bot_or_eq_top with h | h
    · exact h
    · exact (hnt (top_le_iff.mp (h ▸ H.normalCore_le))).elim
  let e : (A ⧸ H) ≃ Fin 8 :=
    (Finite.equivFin (A ⧸ H)).trans (finCongr hi)
  let p : A →* Equiv.Perm (Fin 8) := e.permCongrHom.toMonoidHom.comp f
  have hp : Function.Injective p := e.permCongrHom.injective.comp hf
  have hpr : p.range = alternatingGroup (Fin 8) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have hc : Nat.card p.range = 20160 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hp).toEquiv]
      change Nat.card (alternatingGroup (Fin 8)) = 20160
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hc' := p.range.card_mul_index
    rw [hc] at hc'
    have hs : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    rw [hs] at hc'
    omega
  let a : A ≃* A := (MonoidHom.ofInjective hp).trans (MulEquiv.subgroupCongr hpr)
  obtain ⟨s, hs⟩ := (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    8 (by decide) (by decide)).2 a
  let x := e (QuotientGroup.mk (1 : A))
  refine ⟨s⁻¹ x, fun g => ?_⟩
  have hg : p g x = x ↔ g ∈ H := by
    change e (g • (e.symm (e (QuotientGroup.mk (1 : A))))) =
      e (QuotientGroup.mk (1 : A)) ↔ _
    rw [e.symm_apply_apply, e.injective.eq_iff]
    change QuotientGroup.mk (g * 1) = QuotientGroup.mk (1 : A) ↔ _
    simp [QuotientGroup.eq]
  have he : p g = s * g.val * s⁻¹ := by
    have hh := congrArg (fun b : MulAut A => (b g).val) hs
    exact hh.symm
  rw [he] at hg
  rw [← hg]
  change s (g.val (s⁻¹ x)) = x ↔ _
  exact s.eq_symm_apply.symm

/-- An index-eight subgroup of A₈ equals its normalizer. -/
theorem index_eight_normalizer (H : Subgroup (alternatingGroup (Fin 8))) (hi : H.index = 8) :
    normalizer (H : Set (alternatingGroup (Fin 8))) = H := by
  have hnt : H ≠ ⊤ := by intro h; simp [h] at hi
  have hnb : H ≠ ⊥ := by
    intro h
    rw [h, Subgroup.index_bot, nat_card_alternatingGroup] at hi
    norm_num [Nat.factorial] at hi
  have hm : IsCoatom H := by
    refine ⟨hnt, fun J hJ => ?_⟩
    have hd : J.index ∣ 8 := by
      simpa only [hi] using Subgroup.index_dvd_of_le hJ.le
    have hj : J.index < 8 := by
      simpa only [hi] using Subgroup.index_strictAnti hJ
    apply Atlas.GroupTheory.subgroup_eq_top_of_index_factorial_lt
    have hjpos : 0 < J.index := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := J))
    have cases : J.index = 1 ∨ J.index = 2 ∨ J.index = 4 :=
      (by decide : ∀ n ∈ Finset.range 8, n ∣ 8 → 0 < n →
        n = 1 ∨ n = 2 ∨ n = 4) J.index (Finset.mem_range.mpr hj) hd hjpos
    rw [nat_card_alternatingGroup]
    rcases cases with h | h | h <;> rw [h] <;> norm_num [Nat.factorial]
  by_contra hn
  have ht : normalizer (H : Set (alternatingGroup (Fin 8))) = ⊤ :=
    hm.2 _ (lt_of_le_of_ne H.le_normalizer (Ne.symm hn))
  have hnormal := Subgroup.normalizer_eq_top_iff.mp ht
  exact (hnormal.eq_bot_or_eq_top).elim hnb hnt

/-- Any two index-eight subgroups of A₈ are conjugate inside A₈. -/
theorem index_eight_conjugate
    (H J : Subgroup (alternatingGroup (Fin 8))) (hH : H.index = 8) (hJ : J.index = 8) :
    ∃ c : alternatingGroup (Fin 8), H.map (MulAut.conj c).toMonoidHom = J := by
  classical
  obtain ⟨i, hi⟩ := index_eight_fixed H hH
  obtain ⟨j, hj⟩ := index_eight_fixed J hJ
  let : MulAction.IsPretransitive (alternatingGroup (Fin 8)) (Fin 8) :=
    alternatingGroup.isPretransitive_of_three_le_card (Fin 8) (by simp)
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 8)) i j
  change c.val i = j at hc
  refine ⟨c, ?_⟩
  ext g
  rw [Subgroup.mem_map_equiv, hi, hj]
  change c.val.symm (g.val (c.val i)) = i ↔ g.val j = j
  rw [← c.val.injective.eq_iff]
  simp only [c.val.apply_symm_apply, hc]

end GroupTheory.AlternatingIndexEight
