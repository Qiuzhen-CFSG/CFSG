module

public import Theory.SpecificGroups.AlternatingSix.PGLNineOvergroups

/-!
# Lifting A₅ overgroups through a small kernel

A homomorphism with kernel of order at most four is injective on an A₅
subgroup, by simplicity and order. If the kernel lies in a perfect subgroup,
a proper overgroup has proper image. The intrinsic PGL₂(9) calculation then
puts that image inside PSL₂(9), and the literal subgroup preimage gives the
upstairs containment.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, printed p.266.
The application uses the order-three center of the vertex centralizer.
-/

public section

open Subgroup
open Atlas.Comparisons.Exceptional GorensteinWalter

namespace AlternatingSix.PGLNineOvergroups

private theorem map_alternatingFive {G Q : Type*} [Group G] [Group Q] [Finite G]
    (f : G →* Q) (hk : Nat.card f.ker ≤ 4) (F : Subgroup G)
    (he : Nonempty (F ≃* alternatingGroup (Fin 5))) :
    Nonempty (F.map f ≃* alternatingGroup (Fin 5)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup F := he.some.isSimpleGroup
  let r := f.comp F.subtype
  have hinj : Function.Injective r := by
    apply r.ker_eq_bot_iff.mp
    rcases r.normal_ker.eq_bot_or_eq_top with h | h
    · exact h
    · have hFK : F ≤ f.ker := by
        intro x hx
        exact (show (⟨x, hx⟩ : F) ∈ r.ker by rw [h]; trivial)
      have hFc : Nat.card F = 60 := by
        rw [Nat.card_congr he.some.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        norm_num [Nat.factorial]
      have hc := Nat.card_le_card_of_injective (inclusion hFK) (inclusion_injective hFK)
      omega
  let e : F ≃* F.map f := MulEquiv.ofBijective (f.subgroupMap F)
    ⟨fun x y h => hinj (congrArg Subtype.val h), f.subgroupMap_surjective F⟩
  exact ⟨e.symm.trans he.some⟩

/-- Lift the intrinsic PGL₂(9) overgroup theorem through a small kernel,
retaining the actual image of the perfect subgroup and all subgroup maps. -/
theorem proper_overgroup_le_of_small_kernel {G : Type*} [Group G] [Finite G]
    (f : G →* PGL2 Nine.F) (C : Subgroup G) [Group.IsPerfect C]
    (hker : f.ker ≤ C) (hk : Nat.card f.ker ≤ 4)
    (himage : C.map f =
      (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := Nine.F)).range)
    (F U : Subgroup G) (he : Nonempty (F ≃* alternatingGroup (Fin 5)))
    (hFU : F ≤ U) (hU : U ≠ ⊤) : U ≤ C := by
  have hproper := map_ne_top_of_ker_le_perfect f C U hker hk hU
  have him := proper_overgroup_le_psl (F.map f) (U.map f)
    (map_alternatingFive f hk F he) (map_mono hFU) hproper
  rw [← himage] at him
  have hh := (map_le_iff_le_comap).mp him
  simpa only [comap_map_eq, sup_of_le_left hker] using hh

end AlternatingSix.PGLNineOvergroups
