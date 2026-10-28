module
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Normality detected by a nontrivial component image

Distinct C-components commute modulo the solvable radical. If their normal
images coincide, that perfect image lies in the image of the solvable
radical and must be trivial. Thus any nontrivial normal image detects
normality, without a solvability assumption on the action kernel.

Source application: Aschbacher--Smith 14.3.15, lifting the normal dotted
component to its original point normalizer.
-/

public section
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- A C-component with nontrivial normal image is normal. The kernel of
`f` is unrestricted. -/
theorem IsCComponent.normal_of_normal_nontrivial_image
    {L : Subgroup G} (hL : L.IsCComponent) (f : G →* Q)
    (hn : (L.map f).Normal) (hne : L.map f ≠ ⊥) : L.Normal := by
  let R := solvableRadical G
  let q := QuotientGroup.mk' R
  let := hn
  let := hL.perfect
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hneq
  have hconj := hL.map_equiv (MulAut.conj g)
  have hneq' : L.map q ≠ (L.map (MulAut.conj g).toMonoidHom).map q := by
    intro he
    exact hneq (hconj.eq_of_map_quotient_eq hL R he.symm)
  have hq := (hL.map_quotient R).commutator_eq_bot_of_ne_of_solvableRadical_eq_bot
    (solvableRadical_quotient_solvableRadical (G := G)) (hconj.map_quotient R) hneq'
  have hc : ⁅L, L.map (MulAut.conj g).toMonoidHom⁆ ≤ R := by
    have hm : (⁅L, L.map (MulAut.conj g).toMonoidHom⁆ : Subgroup G).map q = ⊥ := by
      rw [map_commutator, hq]
    simpa only [q, QuotientGroup.ker_mk'] using (map_eq_bot_iff _).mp hm
  have himage : (L.map (MulAut.conj g).toMonoidHom).map f = L.map f := by
    have he : (L.map (MulAut.conj g).toMonoidHom).map f =
        (L.map f).map (MulAut.conj (f g)).toMonoidHom := by
      rw [map_map, map_map]
      congr 1
      ext x
      simp
    rw [he]
    exact normal_iff_map_conj_eq.mp hn (f g)
  have hle : L.map f ≤ R.map f := by
    have hh := map_mono (f := f) hc
    rw [map_commutator, himage, isPerfect_iff.mp (Group.IsPerfect.map f)] at hh
    exact hh
  let : Group.IsSolvable (R.map f) := Group.isSolvable_of_surjective (f.subgroupMap_surjective R)
  let : Group.IsPerfect (L.map f) := Group.IsPerfect.map f
  let : Nontrivial (L.map f) := (nontrivial_iff_ne_bot _).mpr hne
  let : Group.IsSolvable (L.map f) := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hle) (inclusion_injective hle)
  exact Group.IsPerfect.not_isSolvable (L.map f) inferInstance
end Subgroup
