module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary
public import Theory.SpecificGroups.PSL3Even.ResidualComparison
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.GroupAction.AutomorphismFixedTransport


/-!
# Sylow-fixed involutions in the corank-three Borel models

In PSL₂(8), Sz(8), and PSU₃(8), a proper subgroup containing a Sylow
2-subgroup lies in its solvable Borel normalizer. The fixed subgroup of
an automorphism of order two is proper, so the concrete rank-one Borel
calculations prove its solvability. The unitary model retains arbitrary
Hermitian forms, fixed-field order eight, and matrix-field order sixty-four.

For PSL₃(8), the Sylow-pointwise fixer calculation identifies the involution
with conjugation by an element of the Sylow center. The inner fixed-subgroup
calculation then gives the solvable highest-root centralizer, transported
through the actual model isomorphism. The central two-cover constructor is
excluded by its parameter-two requirement.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, E.6.8 and
E.6.11, printed pp.247–250 (PDF pp.258–261), and the model inspection in
E.6.25, printed p.256 (PDF p.267). The rank-one inputs are the concrete
proofs of F.1.3(1), not the legacy rank-one hypothesis records.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.BorelEightFixed
universe u
variable {G : Type u} [Group G] [Finite G] {J : Subgroup G}

private theorem fixedSubgroup_lt_top {H : Type*} [Group H]
    (a : MulAut H) (ha : orderOf a = 2) : a.fixedSubgroup < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro he
  have ha1 : a = 1 := by
    ext x
    exact (MulAut.mem_fixedSubgroup a x).mp (he ▸ mem_top x)
  simp [ha1] at ha

private theorem rankOne_fixedSubgroup_solvable {H : Type*} [Group H]
    (a : MulAut H) (ha : orderOf a = 2) (S : Sylow 2 H)
    (hS : RankOneSylowFacts S) (hfix : ∀ x ∈ (S : Subgroup H), a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  have hSN : (S : Subgroup H) ≤ a.fixedSubgroup := by
    intro x hx
    exact (MulAut.mem_fixedSubgroup a x).mpr (hfix x hx)
  have hN := hS.unique_maximal a.fixedSubgroup hSN (fixedSubgroup_lt_top a ha)
  let := hS.solvable
  exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hN)

/-- The actual PSL₂(8) Borel contains the proper fixed subgroup. -/
theorem linear_two_fixedSubgroup_solvable
    (hmodel : ClassicalGroup.IsPSL J 2 8)
    (a : MulAut J) (ha : orderOf a = 2) (S : Sylow 2 J)
    (hfix : ∀ x ∈ (S : Subgroup J), a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  exact rankOne_fixedSubgroup_solvable a ha S
    (rankOneSylowFacts_of_equiv S e
      (rankOneSylowFacts_psl2 F 3 (by decide) (by simpa using hF) _)) hfix

/-- The actual Sz(8) Borel contains the proper fixed subgroup. -/
theorem suzuki_fixedSubgroup_solvable
    (hmodel : Nonempty (J ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))
    (a : MulAut J) (ha : orderOf a = 2) (S : Sylow 2 J)
    (hfix : ∀ x ∈ (S : Subgroup J), a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨e⟩ := hmodel
  exact rankOne_fixedSubgroup_solvable a ha S
    (rankOneSylowFacts_of_equiv S e (suzuki_rankOneSylowFacts 1 _)) hfix

/-- The PSU₃(8) calculation uses the specified order-64 matrix field and
its stored Frobenius conjugation, with no innerness premise. -/
theorem unitary_three_fixedSubgroup_solvable
    (hmodel : ClassicalGroup.IsPSU J 3 8)
    (a : MulAut J) (ha : orderOf a = 2) (S : Sylow 2 J)
    (hfix : ∀ x ∈ (S : Subgroup J), a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨F, _, _, form, hF, hconj, ⟨e⟩⟩ := hmodel
  exact rankOne_fixedSubgroup_solvable a ha S
    (rankOneSylowFacts_of_equiv S e
      (rankOneSylowFacts_psu3 form 3 (by decide) (by simpa using hF)
        (by simpa using hconj) _)) hfix

omit [Finite G] in
/-- Inner involutions in the actual PSL₃(8) model have solvable fixed groups.
Innerness remains an explicit hypothesis of this helper. -/
theorem linear_three_fixedSubgroup_solvable_of_inner
    (hmodel : ClassicalGroup.IsPSL J 3 8)
    (a : MulAut J) (ha : orderOf a = 2) (hi : ∃ x : J, a = MulAut.conj x) :
    Group.IsSolvable a.fixedSubgroup := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let b := MulAut.congr e a
  have hb : orderOf b = 2 := ((MulAut.congr e).orderOf_eq a).trans ha
  obtain ⟨f⟩ := Matrix.PSL3Even.ResidualComparison.inner_fixed_equiv_root F
    (n := 3) (by decide) (by simpa using hF) b hb
    ((MulAut.congr_inner_iff e a).mpr hi)
  let := Matrix.PSL3Even.ResidualComparison.root_centralizer_solvable F
    (n := 3) (by decide) (by simpa using hF)
  exact Group.isSolvable_of_isSolvable_injective
    (f := ((MulAut.fixedSubgroupCongr e a).trans f).toMonoidHom)
    ((MulAut.fixedSubgroupCongr e a).trans f).injective

/-- The complete corank-three Borel case split, conditional only on innerness
in the PSL₃(8) branch. The three rank-one cases have no additional premises. -/
theorem fixedSubgroup_solvable_of_linear_three_inner
    (hmodel : Components.BorelComponentModel J 3)
    (a : MulAut J) (ha : orderOf a = 2) (S : Sylow 2 J)
    (hfix : ∀ x ∈ (S : Subgroup J), a x = x)
    (hinner : ClassicalGroup.IsPSL J 3 8 → ∃ x : J, a = MulAut.conj x) :
    Group.IsSolvable a.fixedSubgroup := by
  cases hmodel with
  | linear_two _ iso => exact linear_two_fixedSubgroup_solvable iso a ha S hfix
  | suzuki m _ hn iso =>
    have hm : m = 1 := by omega
    subst m
    exact suzuki_fixedSubgroup_solvable iso a ha S hfix
  | linear_three _ iso =>
    exact linear_three_fixedSubgroup_solvable_of_inner iso a ha (hinner iso)
  | unitary_three _ iso => exact unitary_three_fixedSubgroup_solvable iso a ha S hfix
  | linear_three_cover hn _ _ => omega

/-- The Sylow-pointwise fixer calculation discharges the only conditional
premise in the corank-three Borel split. -/
theorem fixedSubgroup_solvable
    (hmodel : Components.BorelComponentModel J 3)
    (a : MulAut J) (ha : orderOf a = 2) (S : Sylow 2 J)
    (hfix : ∀ x ∈ (S : Subgroup J), a x = x) :
    Group.IsSolvable a.fixedSubgroup := by
  apply fixedSubgroup_solvable_of_linear_three_inner hmodel a ha S hfix
  intro hpsl
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hpsl
  obtain ⟨z, _, hz⟩ := Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv
    F (by decide : 0 < 3) (by simpa using hF) e S a hfix
  exact ⟨z, hz⟩

end CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.LocalFactors.ExceptionalModels.BorelEightFixed
