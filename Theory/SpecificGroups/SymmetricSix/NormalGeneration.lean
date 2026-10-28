module
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# Normal generation in a group with six-letter image

If the image contains A6 and the kernel is a two-group, the normal closure
of any subgroup with nontrivial image contains every two-perfect subgroup
whose image lies in A6. Simplicity handles the A6 image; a nontrivial normal
subgroup of S6 contains A6. Two-perfectness removes the full two-group kernel.

The plane Baumann argument applies this to J(T) in the literal LT action.
Source: Aschbacher--Smith C.1.37 and 13.2.2(10), pp.141--143,878.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G]

theorem perfect_le_normalClosure_of_nontrivial_image
    (q : G →* Equiv.Perm (Fin 6)) (hk : IsPGroup 2 q.ker)
    (hY : alternatingGroup (Fin 6) ≤ q.range)
    (K J : Subgroup G) (hK : IsPPerfect 2 K)
    (hKq : K.map q ≤ alternatingGroup (Fin 6)) (hJ : J.map q ≠ ⊥) :
    K ≤ normalClosure (J : Set G) := by
  let N := normalClosure (J : Set G)
  have hN : N.map q ≠ ⊥ := fun he => hJ
    (le_bot_iff.mp ((map_mono (show J ≤ N from le_normalClosure)).trans_eq he))
  have hcover : K.map q ≤ N.map q := by
    by_cases hq : Function.Surjective q
    · let : (N.map q).Normal := (inferInstance : N.Normal).map q hq
      exact hKq.trans (Equiv.Perm.alternatingGroup_le_of_normal (by simp)
        ((nontrivial_iff_ne_bot _).mpr hN))
    · have hi : q.range.index ∣ 2 := by
        simpa only [alternatingGroup.index_eq_two] using index_dvd_of_le hY
      have hr : q.range = alternatingGroup (Fin 6) := by
        rcases (Nat.dvd_prime Nat.prime_two).mp hi with hi | hi
        · exact (hq (MonoidHom.range_eq_top.mp (index_eq_one.mp hi))).elim
        · exact Equiv.Perm.eq_alternatingGroup_of_index_eq_two hi
      let f : G →* alternatingGroup (Fin 6) :=
        q.codRestrict _ (fun g => hr ▸ (show q g ∈ q.range from ⟨g,rfl⟩))
      have hf : Function.Surjective f := by
        intro a
        have ha : a.val ∈ q.range := by rw [hr];exact a.property
        obtain ⟨g,hg⟩ := ha
        exact ⟨g,Subtype.ext hg⟩
      let : (N.map f).Normal := (inferInstance : N.Normal).map f hf
      have hcomp : (alternatingGroup (Fin 6)).subtype.comp f = q := rfl
      have he : N.map f = ⊤ := by
        rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (by simp : 5 ≤ Nat.card (Fin 6))
          (N := N.map f) with hb | ht
        · exact (hN (by rw [←hcomp,←map_map,hb,Subgroup.map_bot])).elim
        · exact ht
      have hh : N.map q = alternatingGroup (Fin 6) := by
        rw [←hcomp,←map_map,he,←MonoidHom.range_eq_map,range_subtype]
      exact hKq.trans_eq hh.symm
  have hsup : K ≤ N ⊔ q.ker := by
    simpa only [comap_map_eq] using
      (le_comap_map q K).trans (comap_mono (f := q) hcover)
  exact le_normal_of_isPPerfect_of_le_sup_pGroup K N q.ker hK hk hsup

end Theory.SpecificGroups.SymmetricSix
