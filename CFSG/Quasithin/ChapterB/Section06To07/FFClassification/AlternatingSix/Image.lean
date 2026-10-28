module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.SpecificGroups.SymmetricSix.Parabolics
/-!
# Six-letter images exclude minimal parabolicity

A group mapping onto an image between A6 and S6 cannot be minimal parabolic.
The image is not a two-group, so the kernel lies in the unique maximal
Sylow-overgroup core. Minimal parabolicity descends, contradicting the two
actual six-letter Sylow parabolics. No kernel-order hypothesis is imposed.

Source: Aschbacher–Smith B.6.9, p.116, and I.5, pp.419–422.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterB
open Theory.SpecificGroups.SymmetricSix
variable {G : Type*} [Group G] [Finite G]
/-- The symmetric six-letter group has two maximal overgroups of every Sylow. -/
theorem not_minimalParabolic_symmetricSix (T : Sylow 2 (Equiv.Perm (Fin 6))) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  intro hP
  obtain ⟨g,_,hh⟩ := coatoms_over_sylow T
  have hp := (hh _).mpr (Or.inl rfl)
  have hq := (hh _).mpr (Or.inr rfl)
  have he := (minimalParabolicMax_unique T hP hp.1 hp.2).trans
    (minimalParabolicMax_unique T hP hq.1 hq.2).symm
  have he' := (MulAut.conj g).mapSubgroup.injective he
  exact synthemeStabilizer_not_le_duad (he'.symm.le)

/-- The alternating six-letter group has the same two-overgroup obstruction. -/
theorem not_minimalParabolic_alternatingSix (T : Sylow 2 (alternatingGroup (Fin 6))) :
    ¬ IsMinimalParabolicOver T ⊤ := by
  intro hP
  obtain ⟨g,_,hh⟩ := a6_coatoms_over_sylow T
  have hp := (hh _).mpr (Or.inl rfl)
  have hq := (hh _).mpr (Or.inr rfl)
  have he := (minimalParabolicMax_unique T hP hp.1 hp.2).trans
    (minimalParabolicMax_unique T hP hq.1 hq.2).symm
  have he' := (MulAut.conj g).mapSubgroup.injective he
  exact a6SynthemeStabilizer_not_le_duad (he'.symm.le)

/-- Any six-letter image containing A6 contradicts ambient minimal parabolicity. -/
theorem not_minimalParabolic_of_six_image
    (T : Sylow 2 G) (q : G →* Equiv.Perm (Fin 6))
    (hA : alternatingGroup (Fin 6) ≤ q.range) : ¬ IsMinimalParabolicOver T ⊤ := by
  intro hP
  let R := q.range
  let r := q.rangeRestrict
  have hnp : ¬ IsPGroup 2 R := by
    intro hp
    have hpA := hp.of_injective (inclusion hA) (inclusion_injective hA)
    obtain ⟨n,hn⟩ := hpA.exists_card_eq
    have hd : 3 ∣ 2^n := by
      rw [← hn,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hh := Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 3) hd
    norm_num at hh
  have hk : r.ker ≤ minimalParabolicCore T hP := by
    obtain hk | hk := minimalParabolic_normal_subgroup_dichotomy T hP r.ker
    · exact hk
    exfalso
    have hm := congrArg (map r) hk
    have ht : (T : Subgroup G).map r = ⊤ := by
      simpa only [Subgroup.map_sup,map_ker_self,sup_bot_eq,
        map_top_of_surjective r q.rangeRestrict_surjective] using hm
    have hp : IsPGroup 2 (⊤ : Subgroup R) := ht ▸ T.isPGroup'.map r
    exact hnp (hp.of_equiv topEquiv)
  have hp := minimalParabolic_map_of_kernel_le_core T hP r q.rangeRestrict_surjective hk
  have hcases : R = alternatingGroup (Fin 6) ∨ R = ⊤ := by
    by_cases he : R ≤ alternatingGroup (Fin 6)
    · exact Or.inl (le_antisymm he hA)
    right
    obtain ⟨g,hg,hga⟩ := SetLike.not_le_iff_exists.mp he
    have hodd : Equiv.Perm.sign g = -1 :=
      (Int.units_eq_one_or _).resolve_left (fun hh => hga hh)
    apply top_unique
    intro x _
    rcases Int.units_eq_one_or (Equiv.Perm.sign x) with hx | hx
    · exact hA hx
    · have hm : x*g⁻¹ ∈ R := hA (by simp [Equiv.Perm.mem_alternatingGroup,hx,hodd])
      simpa only [inv_mul_cancel_right] using R.mul_mem hm hg
  rcases hcases with he | he
  · let e := MulEquiv.subgroupCongr he
    have hh := minimalParabolic_map_of_kernel_le_core (T.mapSurjective q.rangeRestrict_surjective)
      hp e.toMonoidHom e.surjective
      (by rw [(e.toMonoidHom.ker_eq_bot_iff).mpr e.injective]; exact bot_le)
    exact not_minimalParabolic_alternatingSix _ hh
  · let e := (MulEquiv.subgroupCongr he).trans topEquiv
    have hh := minimalParabolic_map_of_kernel_le_core (T.mapSurjective q.rangeRestrict_surjective)
      hp e.toMonoidHom e.surjective
      (by rw [(e.toMonoidHom.ker_eq_bot_iff).mpr e.injective]; exact bot_le)
    exact not_minimalParabolic_symmetricSix _ hh
end CFSG.Quasithin.ChapterB
