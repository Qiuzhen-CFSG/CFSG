module
public import CFSG.Quasithin.ChapterF.Section04.UnitarySource.FourPlacement
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.ShortQuotient
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitarySource.DegreeConflict

/-!
# Unitary involution placement for the original prepared residuals

The ordinary projective placement theorem is transported along the literal
prepared subgroup amalgam. In the degree-two case, the already proved
restriction to the two-residuals supplies the ordinary amalgam with the full
reduced overlap. Its residuals are still the original L and O²(H).

Thus each involution in the reduced overlap is conjugate into an original
residual two-core. The common Sylow T ∩ L = T ∩ O²(H) and Sylow conjugacy
extend this placement to both residuals, with all conjugators in the actual
join of their full normalizers. The original sourceS and ambient T remain
distinct from the reduced Sylow; outer transfer is not asserted here.

Source: Aschbacher–Smith 5.2.6–7 and the local placement used in F.4.35,
printed pp.650–651,292 (`refs/quasithin.pdf`). Construction of the
full-normalizer extension in 5.3.2 and the ambient F.4.35–43 argument remain
separate steps in this source family.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.GreenBook.LieModels.UnitaryFour
open UnitaryCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}

/-- Original residual-core placement retains the ordinary and degree-two
comparisons, both orientations, and the whole reduced overlap. -/
theorem Preparation.unitary_reduced_overlap_involution_placement
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (x : G)
    (hx : x ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 0 ⊓
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) 1)
    (hx2 : x ^ 2 = 1) :
    (∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0,
      g * x * g⁻¹ ∈ (residual H).pCoreIn 2) ∨
    (∃ g ∈ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1,
      g * x * g⁻¹ ∈ L.pCoreIn 2) := by
  have hle (c : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))) (i : Fin 2) :
      ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i ≤
        ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i := by
    rw [d.reduced_source_parabolics h hH.1.1.2 hp c i]
    exact map_subtype_le _
  rcases hc with ho | he
  · exact ChapterF.UnitarySource.FourPlacement.comparison_involution_to_residual_core
      m hm (ChapterF.Source.parabolic ![L,residual H] (sourceS L H)) ![L,residual H]
      (d.parabolic_residuals h hH.1.1.2 hp) ho x
      ⟨hle (.unitary m hm ho) 0 hx.1,hle (.unitary m hm ho) 1 hx.2⟩ hx2
  · have hm' := (d.unitaryExtension_local_structure h hH.1.1.2 hp m hm he).1
    have hred := d.unitaryExtension_reduced_amalgam h hH.1.1.2 hp m hm' he
    have hplace := ChapterF.UnitarySource.FourPlacement.comparison_involution_to_residual_core
      m hm (ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L))
      ![L,residual H] (d.reduced_parabolic_residuals h hH.1.1.2 hp (.unitaryExtension m hm he))
      hred x hx hx2
    rcases hplace with ⟨g,hg,hc⟩ | ⟨g,hg,hc⟩
    · exact Or.inl ⟨g,hle (.unitaryExtension m hm he) 0 hg,hc⟩
    · exact Or.inr ⟨g,hle (.unitaryExtension m hm he) 1 hg,hc⟩

/-- Every involution of the reduced common Sylow has a residual-core
representative under the actual full-normalizer join. No equality with T is assumed. -/
theorem Preparation.unitary_inner_involution_placement
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (x : G) (hx : x ∈ (T : Subgroup G) ⊓ L) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ NormalizerJoin L (residual H),
      g * x * g⁻¹ ∈ L.pCoreIn 2 ∨ g * x * g⁻¹ ∈ (residual H).pCoreIn 2 := by
  have hP (i : Fin 2) : ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i ≤
      normalizer (![L,residual H] i : Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (show ![L,residual H] i ≤ ChapterF.Source.parabolic ![L,residual H] (sourceS L H) i
        from le_sup_left.trans le_sup_left)).mp
      ((d.hypothesisF11 h hH.1.1.2).local_normal_in_parabolic i)
  have hxi (i : Fin 2) :
      x ∈ ChapterF.Source.parabolic ![L,residual H] ((T : Subgroup G) ⊓ L) i :=
    (show (T : Subgroup G) ⊓ L ≤ _ from le_sup_right.trans le_sup_left) hx
  rcases d.unitary_reduced_overlap_involution_placement h hH hp m hm hc x
    ⟨hxi 0,hxi 1⟩ hx2 with ⟨g,hg,hgcore⟩ | ⟨g,hg,hgcore⟩
  · exact ⟨g,(show normalizer (L : Set G) ≤ NormalizerJoin L (residual H) from
      le_sup_left) (hP 0 hg),Or.inr hgcore⟩
  · exact ⟨g,(show normalizer (residual H : Set G) ≤ NormalizerJoin L (residual H) from
      le_sup_right) (hP 1 hg),Or.inl hgcore⟩

private theorem conjugate_in_sylow {X : Type*} [Group X] [Finite X]
    (P : Sylow 2 X) (x : X) (hx : x ^ 2 = 1) :
    ∃ k : X, k * x * k⁻¹ ∈ (P : Subgroup X) := by
  have hp : IsPGroup 2 (zpowers x) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  obtain ⟨k,hk⟩ := MulAction.exists_smul_eq X S P
  refine ⟨k,?_⟩
  rw [←hk]
  exact ⟨x,hS (mem_zpowers x),rfl⟩

/-- Every involution in either original residual has a representative in
one of the original two-cores, conjugate under the full-normalizer join. -/
theorem Preparation.unitary_factor_involution_placement
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (x : G) (hx : x ∈ L ∨ x ∈ residual H) (hx2 : x ^ 2 = 1) :
    ∃ g ∈ NormalizerJoin L (residual H),
      g * x * g⁻¹ ∈ L.pCoreIn 2 ∨ g * x * g⁻¹ ∈ (residual H).pCoreIn 2 := by
  have hcc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := by
    rcases hc with ho | he
    · exact .unitary m hm ho
    · exact .unitaryExtension m hm he
  have hs := d.common_sylow_of_comparison h hH.1.1.2 hp hcc
  have place (J : Subgroup G) (hJ : J ≤ NormalizerJoin L (residual H))
      (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
      (hS : (T : Subgroup G) ⊓ J = (T : Subgroup G) ⊓ L)
      (hxJ : x ∈ J) :
      ∃ g ∈ NormalizerJoin L (residual H),
        g * x * g⁻¹ ∈ L.pCoreIn 2 ∨ g * x * g⁻¹ ∈ (residual H).pCoreIn 2 := by
    obtain ⟨P,hP⟩ := exists_sylow_component hTJ
    let a : J := ⟨x,hxJ⟩
    obtain ⟨k,hk⟩ := conjugate_in_sylow P a (Subtype.ext hx2)
    have hy : k.val * x * k.val⁻¹ ∈ (T : Subgroup G) ⊓ L := by
      rw [←hS,←hP]
      exact mem_map_of_mem J.subtype hk
    have hy2 : (k.val * x * k.val⁻¹) ^ 2 = 1 := by
      simpa only [map_pow,map_one,MulAut.conj_apply] using congrArg (MulAut.conj k.val) hx2
    obtain ⟨g,hg,hgc⟩ := d.unitary_inner_involution_placement h hH hp m hm hc
      (k.val * x * k.val⁻¹) hy hy2
    refine ⟨g * k.val,(NormalizerJoin L (residual H)).mul_mem hg (hJ k.property),?_⟩
    simpa only [mul_inv_rev,mul_assoc] using hgc
  rcases hx with hx | hx
  · exact place L (L.le_normalizer.trans le_sup_left) h.sylow_normalizes rfl hx
  · exact place (residual H) ((residual H).le_normalizer.trans le_sup_right)
      (hH.1.1.2.trans (le_normalizer_residual H)) hs.symm hx

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
