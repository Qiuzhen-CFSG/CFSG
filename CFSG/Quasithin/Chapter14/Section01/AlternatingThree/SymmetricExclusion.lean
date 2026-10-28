module

public import CFSG.Quasithin.Chapter14.Section01.AlternatingThree.Centralizer
public import CFSG.Quasithin.ChapterI.Section04To05.SmallSylow.DihedralLocal
public import Theory.SpecificGroups.SymmetricFourSylow

/-!
# Excluding the faithful one-block overgroup in 14.1.10

An actual S₄ overgroup gives a dihedral Sylow subgroup. The proved I.4
transfer calculation gives C_G(z)=T for its central involution z. Since
z belongs to Ω₁Z(T), the full omega-centralizer is also T. This contradicts
the original unique-Mc and multiple-maximal-local hypotheses directly.
No ambient simple-group recognition is needed for this branch.

Source: Aschbacher--Smith 14.1.10, printed p.978, using I.4.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter14.AlternatingThree
variable {G : Type*} [Group G] [Finite G]

theorem not_symmetric_four_overgroup (hE : IsEvenCharacteristic G)
    (T : Sylow 2 G) {M Mc : Subgroup G} (hTM : (T : Subgroup G) ≤ M)
    (hu : maximalTwoLocalOvergroups
      (centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (e : M ≃* Equiv.Perm (Fin 4)) : False := by
  let S := T.subtype hTM
  let P := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨a⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four P
  let eT : T ≃* S := (subgroupOfEquivOfLe hTM).symm
  let eS : S ≃* P := e.subgroupMap (S : Subgroup M)
  obtain ⟨R,hR,hidx,z,hz,hzc,hout⟩ :=
    ChapterI.SmallSylow.dihedral_rotation_data (m := 2) (by decide) (eT.trans (eS.trans a))
  let : IsCyclic R := hR
  have hc := ChapterI.SmallSylow.centralizer_eq_sylow_of_rotation_data T hE
    R hidx z hz hzc hout
  have hzZ : (z : G) ∈ omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    refine ⟨(z : T).property,?_,?_⟩
    · have hh := pow_orderOf_eq_one z
      rw [hz] at hh
      exact congrArg (fun v : R => (v : G)) hh
    · intro t ht
      exact congrArg Subtype.val (mem_center_iff.mp hzc ⟨t,ht⟩)
  have he : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) =
      (T : Subgroup G) := by
    apply le_antisymm
    · exact (centralizer_le (Set.singleton_subset_iff.mpr hzZ)).trans hc.le
    · intro t ht w hw
      exact (((mem_omegaOneCenterAmbient_iff _ w).mp hw).2.2 t ht).symm
  rw [he] at hu
  rw [hu,Set.ncard_singleton] at hmany
  omega

end CFSG.Quasithin.Chapter14.AlternatingThree
