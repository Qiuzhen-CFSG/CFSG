module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeFiveExcluded
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceMathieuShadowRows.M22CodeChiefSieve
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.PairedFiveChiefExclusion
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.PairedFiveOffender

/-!
# Solvability of the original inside-core M22-code parabolic

The nonsolvable chief sieve retains only the paired-five action after the
single-five exclusion. Its same original sharp offender contains a pure
axis transposition. The paired overlap contradiction therefore excludes
nonsolvability. This discharges the solvability premise of the existing
original residual theorem: modulo O₂(H), the two-residual is the three-core,
and the quotient by that three-core is the actual dihedral group of order
eight.

The inside-core hypothesis is still a temporary branch of 8.2.2(1).
Its involution-centralizer contradiction and the later M22-code exclusion
are not asserted here; final M24-cocode selection remains to be proved.
Source: Aschbacher--Smith 3.1.9(6), p.578, applied in 8.2.2(1), p.715.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE Chapter7.NormalizedSource MathieuCode Sporadic.Mathieu
open ChapterB.QuasisimpleSource ChapterB.ComponentRecognition.KnownFFTypes.Sporadic
open ChapterD NoncentralChiefRefinement Chapter8.MathieuShadowRows
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

omit [Finite G] in
private theorem marked_code_mathieu
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation) : HasMathieuCentralQuotient D.orbitComponent := by
  have hq : Nonempty ((D.orbitComponent ⧸ center D.orbitComponent) ≃* M22) := by
    have hz : center D.orbitComponent = ⊥ := by
      have hh := FixedElementary.map_center d.componentEquiv
      rw [m22_center_eq_bot] at hh
      exact (map_eq_bot_iff_of_injective _ d.componentEquiv.injective).mp hh
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans
      d.componentEquiv⟩
  exact Or.inr (Or.inl hq)

set_option backward.isDefEq.respectTransparency false in
/-- The original temporary inside-core M22-code parabolic is solvable. -/
theorem sourceOrbit_m22_code_inside_core_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) : Group.IsSolvable H := by
  by_contra hns
  obtain ⟨c,hn,_,_⟩ := D.sourceOrbit_m22_code_inside_core_inputs h hmany hV hnon d hH hcore
  obtain ⟨hU,a,A,hA,_,_,_,ha,_,_⟩ :=
    D.sourceOrbit_m22_code_inside_core_nonsolvable_small_natural_faithful
      h hmany hV hnon d hH hcore hns
  let := hU
  obtain ⟨s⟩ := SeriesOn.exists_series ((conjugateSpan H D.sourceOrbit).subgroupOf H)
  have hex : ∃ i : Fin s.series.length, ¬ s.Central i := by
    by_contra! hz
    have hz' := s.noncentralCount_eq_zero_iff.mpr hz
    have ht := D.sourceOrbit_m22_code_inside_core_two_chiefs h hmany hV hnon d hH hcore s
    omega
  obtain ⟨i,hi⟩ := hex
  obtain ⟨hU',hf⟩ := D.sourceOrbit_m22_code_inside_core_nonsolvable_paired_five
    h hmany hV hnon d hH hcore hns
  obtain ⟨hk,e,hbase⟩ := hf s i hi
  let ρ := s.factorRepresentation i
  let q := e.groupEquiv.toMonoidHom.comp (actionHom ρ)
  have hker : q.ker = pCore 2 H := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.groupEquiv.injective]
    exact hk
  obtain ⟨B,hBA,hB⟩ := (ha.chief s i hi).1.exists_bestOffender _
  have hoff := (hB.isOffender _).map_equivariant _ _ e.groupEquiv.toMonoidHom
    e.groupEquiv.injective e.linearEquiv e.intertwines
  have hBB : B.map e.groupEquiv.toMonoidHom ≤ BinaryPermutation.FivePair.baseSubgroup :=
    hbase ▸ map_mono (hB.le_offenderSubgroup _)
  obtain ⟨j,b,hb,hs⟩ := paired_base_offender_swap _ hoff hBB
  have hbA : MathieuCode.NormalizedShadowRows.FivePairOverlap.axis j b ∈ A.map q := by
    have hh := (map_mono hBA) hb
    simpa only [actionSubgroup,map_map] using hh
  exact paired_five_chief_impossible c a.original_minimal hn
    (D.sourceOrbit_mathieu_odd_normalizer_le h hmany hV (D.marked_code_mathieu d) hnon)
    q (e.groupEquiv.surjective.comp ρ.asGroupHom.rangeRestrict_surjective)
    (hker ▸ pCore_isPGroup) A hA.1 ha.centralizes ⟨j,b,hbA,hs⟩

/-- The source inside-core branch now constructs the three-core residual and
literal dihedral-eight quotient, with no separate solvability premise. -/
theorem sourceOrbit_m22_code_inside_core_residual
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (d : M22Source.MarkedSimpleModel D.orbitRepresentation D.orbitComponent
      m22OuterCodeRepresentation)
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hcore : D.sourceOrbit ≤ H.pCoreIn 2) :
    Group.IsSolvable H ∧
      pResidual 2 (H ⧸ pCore 2 H) = pCore 3 (H ⧸ pCore 2 H) ∧
      Nonempty (((H ⧸ pCore 2 H) ⧸ pCore 3 (H ⧸ pCore 2 H)) ≃* DihedralGroup 4) := by
  have hs := D.sourceOrbit_m22_code_inside_core_solvable h hmany hV hnon d hH hcore
  exact ⟨hs,D.sourceOrbit_m22_code_inside_core_solvable_residual h hmany hV hnon d hH hcore hs⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
