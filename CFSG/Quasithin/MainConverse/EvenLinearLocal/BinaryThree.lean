module

public import CFSG.Quasithin.MainConverse.EvenLinearLocal.BinaryThree.Matrices
public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.Ambient

/-!
# Even characteristic of PSL₃(2)

The explicit root-plane calculations make both standard flag parabolics
2-local groups of characteristic two. Every proper overgroup of the upper
unitriangular Sylow subgroup lies in one of these parabolics. Maximality among
2-locals therefore identifies the tested local with a parabolic; Sylow
conjugacy gives the condition for every Sylow subgroup.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Theorem 0.1.2(1), printed p.4, and I.5.3–4, printed pp.419–420.
-/

open Matrix.PSL3Two

namespace CFSG.Quasithin.MainConverse.BinaryThree

private theorem equiv_toMonoidHom : equiv.toMonoidHom = project := by
  ext g
  exact equiv_apply g

private theorem projective_twoLocal {P : Subgroup SL} (hP : IsTwoLocal P) :
    IsTwoLocal (P.map project) := by
  simpa only [equiv_toMonoidHom] using Theory.GroupTheory.isTwoLocal_map equiv hP

private theorem twoLocal_ne_top {M : Subgroup PSL} (hM : IsTwoLocal M) : M ≠ ⊤ := by
  obtain ⟨Q, hQ, hQp, rfl⟩ := hM
  intro h
  have hnormal : Q.Normal := Subgroup.normalizer_eq_top_iff.mp h
  have hle : Q ≤ pCore 2 PSL := le_sSup ⟨hnormal, hQp⟩
  exact hQ (le_bot_iff.mp (pCore_two_PSL_eq_bot ▸ hle))

public theorem evenCharacteristic : IsEvenCharacteristic PSL := by
  apply IsEvenCharacteristicAt.all (T := borelSylow)
  intro M hM hTM
  have hproper := twoLocal_ne_top hM.1
  have hproperSL : M.comap project ≠ ⊤ := by
    intro h
    apply hproper
    rw [← Subgroup.map_comap_eq_self_of_surjective project_surjective M, h]
    exact Subgroup.map_top_of_surjective project project_surjective
  have hB : borelSL ≤ M.comap project := by
    intro g hg
    exact hTM (Subgroup.mem_map_of_mem project hg)
  have hMP : M ≤ pointParabolic ∨ M ≤ lineParabolic := by
    rcases overgroup_borelSL (M.comap project) hB hproperSL with hp | hp
    · left
      change M ≤ pointParabolicSL.map project
      simpa only [Subgroup.map_comap_eq_self_of_surjective project_surjective] using
        Subgroup.map_mono (f := project) hp
    · right
      change M ≤ lineParabolicSL.map project
      simpa only [Subgroup.map_comap_eq_self_of_surjective project_surjective] using
        Subgroup.map_mono (f := project) hp
  rcases hMP with hP | hP
  · have hPM := hM.2 (projective_twoLocal pointParabolicSL_twoLocal) hP
    have heq : M = pointParabolic := le_antisymm hP hPM
    rw [heq]
    exact pointParabolicSL_characteristicTwo.of_equiv
      (Subgroup.equivMapOfInjective _ project project_injective)
  · have hPM := hM.2 (projective_twoLocal lineParabolicSL_twoLocal) hP
    have heq : M = lineParabolic := le_antisymm hP hPM
    rw [heq]
    exact lineParabolicSL_characteristicTwo.of_equiv
      (Subgroup.equivMapOfInjective _ project project_injective)

end CFSG.Quasithin.MainConverse.BinaryThree
