module

public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson.Kernel
public import CFSG.Quasithin.Chapter16.Section04To05.Bender.GeometryConstruction.WeakClosure.LinearThompson.ModelBound
public import Stellmacher.MaxElementaryOffender
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxJWeakClosure

/-!
# The linear outer-offender and Thompson calculation

For a maximum-order elementary subgroup A of T, the elementary counting
argument gives |U_L| ≤ |C_{U_L}(A)| |A/C_A(U_L)|. The strict model estimate
therefore forces A to fix U_L. The actual PSL₂ pointwise-fixer theorem and
centerlessness put every element of A in V. Since V itself is elementary,
maximal order now forces V to be the elementary Thompson subgroup J(T).
Its general automorphism invariance gives the required weak closure.

The model calculation proves `StrictActionBound` for every n ≥ 3, including
even field degrees: an elementary outer image has order at most two, while
its nontrivial field involution loses strictly more fixed points. We discharge
that bound in the final results below, excluding genuine FF-star offenders
and establishing the Thompson identity and weak closure for the actual V.
The n = 2 and Suzuki branches belong to the separate weak-closure assembly.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), Proposition
16.5.1, printed p.1194; J(T) is as in Definition B.2.2, pp.74–75.
-/

@[expose] public section

open Subgroup
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L R : Subgroup G} {n : ℕ}

/-- The maximum elementary subgroups act trivially if the model loses more
fixed points than its nontrivial elementary image gains. -/
theorem maxElementary_le_kernel_of_bound (h : StandardSetup T z L)
    [IsElementaryAbelian 2 (componentOmegaInSylow T L)] (hb : StrictActionBound h)
    (A : Subgroup T) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤) :
    A ≤ (omegaAction h).ker := by
  let := componentOmega_normal h
  by_contra hnot
  have hne : A.map (omegaProjection h) ≠ ⊥ := by
    intro he
    apply hnot
    have hh := (map_eq_bot_iff A).mp he
    simpa only [omegaProjection, MonoidHom.ker_rangeRestrict] using hh
  have hlt := hb A hA.2.1 hne
  have hle := Stellmacher.maxElementary_card_le_fixed_mul_image ⊤
    (componentOmegaInSylow T L) A le_top hA (omegaProjection h) (omegaProjection_ker h)
  exact (not_lt_of_ge hle) hlt

/-- The quantitative model bound implies the full maximum-elementary calculation. -/
theorem space_eq_maxJ_of_bound (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (d : LocalAction T L R n) (hb : StrictActionBound h) :
    benderSpace T L = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) := by
  let := d.component_elementary
  let := d.commuting_elementary
  let := space_elementary_of_factors (T := T) (L := L)
  let : IsElementaryAbelian 2 (componentOmegaInSylow T L) :=
    IsElementaryAbelian.subgroupOf ((omegaOneAmbient_le _).trans inf_le_left)
  have hmax (A : Subgroup T) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups ⊤) :
      A.map (T : Subgroup G).subtype ≤ benderSpace T L := by
    let := hA.2.1
    rintro _ ⟨t, ht, rfl⟩
    exact kernel_involution_mem_space_psl2 h hZ hmodel t
      (maxElementary_le_kernel_of_bound h hb A hA ht)
      (elemPow_eq_one_of_isElementaryAbelian t ht)
  have hJ : Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) ≤ benderSpace T L := by
    have he := Stellmacher.elementaryAbelianMaxJ_map_injective
      (T : Subgroup G).subtype (T : Subgroup G).subtype_injective (⊤ : Subgroup T)
    rw [← MonoidHom.range_eq_map, range_subtype] at he
    rw [he, map_le_iff_le_comap]
    exact sSup_le fun A hA => map_le_iff_le_comap.mp (hmax A hA)
  obtain ⟨A, hA⟩ := Stellmacher.elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  have hAV : A ≤ benderSpace T L := (le_sSup hA).trans hJ
  have he : A = benderSpace T L := eq_of_le_of_card_ge hAV
    (hA.2.2 _ (benderSpace_le_sylow T L) inferInstance)
  exact le_antisymm (he ▸ le_sSup hA) hJ

/-- The computed Bender space is weakly closed in the actual Sylow subgroup. -/
theorem space_weakly_closed_of_bound (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (d : LocalAction T L R n) (hb : StrictActionBound h)
    (a : G) (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L := by
  rw [space_eq_maxJ_of_bound h hZ hmodel d hb] at ha ⊢
  exact Stellmacher.elementaryAbelianMaxJ_map_eq_of_le (T : Subgroup G) (MulAut.conj a) ha

/-- The actual component omega subgroup is an elementary binary module,
as follows from its PSL₂ model. -/
theorem componentOmega_elementary_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n)) :
    IsElementaryAbelian 2 (componentOmegaInSylow T L) := by
  let := componentSylow_elementary_psl2 h hZ hmodel
  let : IsElementaryAbelian 2 (omegaOneAmbient (componentSylow T L)) := by
    rw [omegaOneAmbient_eq_self]
    infer_instance
  exact IsElementaryAbelian.subgroupOf ((omegaOneAmbient_le _).trans inf_le_left)

/-- No image of an elementary subgroup of T is an FF-star offender on U_L
in the linear branch with n ≥ 3. The module structure is derived from the
actual PSL₂ model, and the strict action bound is discharged. -/
theorem image_not_bestOffender_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hn : 3 ≤ n) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (A : Subgroup T) (hA : IsElementaryAbelian 2 A) :
    letI := componentOmega_elementary_psl2 h hZ hmodel
    ¬ Representation.BinaryOffender.IsBestOffender (omegaRepresentation h)
      (A.map (omegaProjection h)) := by
  let := componentOmega_elementary_psl2 h hZ hmodel
  exact image_not_bestOffender_of_bound h (strictActionBound_psl2 h hZ hn hmodel) A hA

/-- The source Thompson calculation V = J(T) for PSL₂(2ⁿ), n ≥ 3.
Here J(T) is generated by the maximum-order elementary abelian subgroups,
as in Definition B.2.2. No offender or containment premise remains. -/
theorem space_eq_maxJ_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hn : 3 ≤ n) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (d : LocalAction T L R n) :
    benderSpace T L = Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) :=
  space_eq_maxJ_of_bound h hZ hmodel d (strictActionBound_psl2 h hZ hn hmodel)

/-- The actual Bender space in the linear branch is weakly closed in T
with respect to ambient conjugation, for every n ≥ 3. -/
theorem space_weakly_closed_psl2 (h : StandardSetup T z L) (hZ : center L = ⊥)
    (hn : 3 ≤ n) (hmodel : ClassicalGroup.IsPSL (L ⧸ center L) 2 (2^n))
    (d : LocalAction T L R n)
    (a : G) (ha : (benderSpace T L).conjBy a ≤ (T : Subgroup G)) :
    (benderSpace T L).conjBy a = benderSpace T L :=
  space_weakly_closed_of_bound h hZ hmodel d (strictActionBound_psl2 h hZ hn hmodel) a ha

end CFSG.Quasithin.Chapter16.Intersections.Bender.GeometryConstruction.WeakClosure.LinearThompson
