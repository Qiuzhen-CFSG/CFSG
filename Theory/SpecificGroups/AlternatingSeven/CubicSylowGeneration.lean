module
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model
public import Theory.Alternating.theorem_5_2_1_2
import Mathlib.Tactic

/-!
# Generation of A₇ by cubic Sylow overgroups

Four explicit subgroups of order 24 contain the fixed dihedral Sylow subgroup.
Their cubic elements generate the star three-cycles, hence A₇. Conjugacy of
Sylow subgroups transports this generation statement to every Sylow subgroup.
This is the concrete generation input for the empty-family exclusion in
Aschbacher--Smith 14.3.6(5), printed p.992.
-/

@[expose] public section
open Equiv Subgroup
open scoped Pointwise
namespace AlternatingSeven.CubicSylowGeneration
open DihedralLocals
private def localWord (j : Fin 4) (v : Fin 8 × Fin 3) : Perm7 :=
  tWord v.1 * cubic j ^ v.2.val
private theorem localWords_mul (j : Fin 4) (v w : Fin 8 × Fin 3) :
    ∃ u : Fin 8 × Fin 3, localWord j v * localWord j w = localWord j u := by
  decide +revert +kernel
private theorem localWords_inv (j : Fin 4) (v : Fin 8 × Fin 3) :
    ∃ u : Fin 8 × Fin 3, (localWord j v)⁻¹ = localWord j u := by
  decide +revert +kernel
private def localSubgroup (j : Fin 4) : Subgroup Perm7 where
  carrier := Set.range (localWord j)
  one_mem' := ⟨(0,0), by decide +revert +kernel⟩
  mul_mem' := by
    rintro _ _ ⟨v,rfl⟩ ⟨w,rfl⟩
    obtain ⟨u,hu⟩ := localWords_mul j v w
    exact ⟨u,hu.symm⟩
  inv_mem' := by
    rintro _ ⟨v,rfl⟩
    obtain ⟨u,hu⟩ := localWords_inv j v
    exact ⟨u,hu.symm⟩
private theorem localSubgroup_card (j : Fin 4) : Nat.card (localSubgroup j) = 24 := by
  let f : (Fin 8 × Fin 3) → localSubgroup j := fun v => ⟨localWord j v, v, rfl⟩
  have hi : Function.Injective (localWord j) := by decide +revert +kernel
  have hb : Function.Bijective f := ⟨fun v w h => hi (congrArg Subtype.val h), by
    rintro ⟨g,v,rfl⟩
    exact ⟨v,rfl⟩⟩
  rw [←Nat.card_congr (Equiv.ofBijective f hb)]
  simp
private theorem localSubgroup_le_alternating (j : Fin 4) :
    localSubgroup j ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨v,rfl⟩
  exact (by decide +kernel : ∀ j : Fin 4, ∀ v : Fin 8 × Fin 3,
    Perm.sign (localWord j v) = 1) j v
private def localInAlternating (j : Fin 4) : Subgroup A7 :=
  (localSubgroup j).subgroupOf (alternatingGroup (Fin 7))
private theorem local_card (j : Fin 4) : Nat.card (localInAlternating j) = 24 :=
  (Nat.card_congr (subgroupOfEquivOfLe (localSubgroup_le_alternating j)).toEquiv).trans
    (localSubgroup_card j)
private theorem sylow_le_local (j : Fin 4) :
    (fixedSylow : Subgroup A7) ≤ localInAlternating j := by
  rintro g ⟨i,hi⟩
  exact ⟨(i,0), by simpa [localWord] using hi⟩
private theorem local_index (j : Fin 4) :
    (fixedSylow : Subgroup A7).relIndex (localInAlternating j) = 3 := by
  have he := ((fixedSylow : Subgroup A7).subgroupOf (localInAlternating j)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (sylow_le_local j)).toEquiv,
    show Nat.card (fixedSylow : Subgroup A7) = 8 from fixedTwoGroup_card,local_card] at he
  change (fixedSylow : Subgroup A7).relIndex (localInAlternating j) = 3
  change 8 * (fixedSylow : Subgroup A7).relIndex (localInAlternating j) = 24 at he
  omega
private theorem cubic_even (j : Fin 4) : cubic j ∈ alternatingGroup (Fin 7) :=
  (by decide +kernel : ∀ j : Fin 4, Perm.sign (cubic j) = 1) j
private def ar : A7 := ⟨r, twoGroup_le_alternating r_mem_twoGroup⟩
private def ass : A7 := ⟨s, twoGroup_le_alternating s_mem_twoGroup⟩
private def ac (j : Fin 4) : A7 := ⟨cubic j,cubic_even j⟩
private theorem local_cubic (j : Fin 4) : ac j ∈ localInAlternating j :=
  ⟨(0,1),by simp [localWord,tWord,ac]⟩
private theorem locals_generate (H : Subgroup A7)
    (hs : (fixedSylow : Subgroup A7) ≤ H)
    (hc : ∀ j : Fin 4, ac j ∈ H) : H = ⊤ := by
  have hr : ar ∈ H := hs r_mem_twoGroup
  have ht : ass ∈ H := hs s_mem_twoGroup
  apply top_unique
  rw [← GLS3.Chapter5.starThreeCycles_closure_eq_top
    (a := (0 : Fin 7)) (b := (1 : Fin 7)) (by decide),Subgroup.closure_le]
  rintro g ⟨c,hc0,hc1,hg⟩
  have identify (w : A7) (hw : (w : Perm7) = swap 0 1 * swap 0 c) : g = w :=
    Subtype.ext (hg.trans hw.symm)
  fin_cases c
  · exact (hc0 rfl).elim
  · exact (hc1 rfl).elim
  · rw [identify (ac 0 * ass) (by decide +kernel)]
    exact H.mul_mem (hc 0) ht
  · rw [identify (ar * ac 0 * ar) (by decide +kernel)]
    exact H.mul_mem (H.mul_mem hr (hc 0)) hr
  · rw [identify (ac 0 * ac 3 * ac 0 * ass * ac 0 * ac 3) (by decide +kernel)]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hc 0) (hc 3)) (hc 0)) ht) (hc 0)) (hc 3)
  · rw [identify (ac 0 * ac 3 * ass * ac 0 * ac 3) (by decide +kernel)]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hc 0) (hc 3)) ht) (hc 0)) (hc 3)
  · rw [identify (ac 0 * ac 1 * ac 3 * ac 3 * ac 0 * ac 3 * ac 2) (by decide +kernel)]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (hc 0) (hc 1)) (hc 3)) (hc 3)) (hc 0)) (hc 3)) (hc 2)

theorem fixed_sylow_index_three_generation (H : Subgroup A7)
    (hs : (fixedSylow : Subgroup A7) ≤ H)
    (hlocal : ∀ J : Subgroup A7, (fixedSylow : Subgroup A7) ≤ J →
      (fixedSylow : Subgroup A7).relIndex J = 3 → J ≤ H) : H = ⊤ := by
  exact locals_generate H hs fun j => hlocal _ (sylow_le_local j) (local_index j) (local_cubic j)

/-- The Sylow two-subgroup and all its index-three overgroups generate A₇. -/
theorem sylow_index_three_generation (P : Sylow 2 A7) (H : Subgroup A7)
    (hP : (P : Subgroup A7) ≤ H)
    (hlocal : ∀ J : Subgroup A7, (P : Subgroup A7) ≤ J →
      (P : Subgroup A7).relIndex J = 3 → J ≤ H) : H = ⊤ := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq A7 P fixedSylow
  let a := (MulAut.conj g).toMonoidHom
  have hmap : (P : Subgroup A7).map a = (fixedSylow : Subgroup A7) :=
    congrArg Sylow.toSubgroup hg
  have he : H.map a = ⊤ := by
    apply fixed_sylow_index_three_generation
    · exact hmap ▸ map_mono hP
    · intro J hPJ hi
      have hPpre : (P : Subgroup A7) ≤ J.comap a :=
        (map_le_iff_le_comap).mp (hmap ▸ hPJ)
      have hindex : (P : Subgroup A7).relIndex (J.comap a) = 3 := by
        have hh := relIndex_map_map_of_injective (f := a) (P : Subgroup A7) (J.comap a)
          (MulAut.conj g).injective
        rw [hmap,map_comap_eq_self_of_surjective (MulAut.conj g).surjective] at hh
        exact hh.symm.trans hi
      have hh := map_mono (f := a) (hlocal (J.comap a) hPpre hindex)
      rwa [map_comap_eq_self_of_surjective (MulAut.conj g).surjective] at hh
  apply (map_injective (f := a) (MulAut.conj g).injective)
  rw [he,map_top_of_surjective a (MulAut.conj g).surjective]

end AlternatingSeven.CubicSylowGeneration
