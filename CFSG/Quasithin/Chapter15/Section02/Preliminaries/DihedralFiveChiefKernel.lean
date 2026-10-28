module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.ChosenResidualKernel
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.DihedralFiveSetup
public import CFSG.Quasithin.Chapter15.Section01.RatioReduction.PreparedSmallChiefActions
public import Theory.Representation.BinaryOffender.IrreducibleResidual

/-!
# The actual outside-parabolic quotient in the marked-five case

The marked-five residual already has M as its unique maximal two-local
overgroup after adjoining T. Hence every nontrivial quotient of an outside
minimal parabolic H with trivial two-core has kernel O₂(H).

Choose a noncentral factor in an H-chief series on the actual conjugate
span of V. Its irreducible action image has trivial two-core, so the kernel
theorem identifies its faithful quotient with H/O₂(H). The prepared small
chief-action theorem therefore gives the four source possibilities for
this literal quotient. The remaining exclusions in 15.2.8 are separate.

Source: Aschbacher--Smith 15.2.7 and the opening of 15.2.8,
printed pp.1109--1110, using 15.1.12(1),(3).
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G]

/-- Original 15.2.8's four quotient possibilities, with its kernel premise
discharged by the marked-five residual uniqueness theorem. -/
theorem source_dihedral_five_HStar_small_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (l : LocalGeneration ((imageRepresentation M V hV.normalized).comp
      (Jhat (imageRepresentation M V hV.normalized)).subtype)) {m : ℕ}
    (hp : PrimeDimensionOptions 5 m) (hd : DihedralMarking l 5 m)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M) :
    ChapterB.ChiefSmallActor (H ⧸ pCore 2 H) := by
  let := hV.elementary
  let U := (conjugateSpan H V).subgroupOf H
  let := (hV.chief_data hG T hempty hM hJ H hH).1
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    (show conjugateSpan H V ≤ H by
      rw [UniqueFactor.conjugateSpan_eq]
      exact conjugateSpanBy_le_self ((hV.inside_core H hH).trans (twoCore_le H)))
  obtain ⟨s⟩ := SeriesOn.exists_series U
  have hcount := (hV.chief_data hG T hempty hM hJ H hH).2 s
  obtain ⟨i, hi⟩ : ∃ i, ¬ s.Central i := by
    by_contra! hc
    have hz := s.noncentralCount_eq_zero_iff.mpr hc
    omega
  let := s.factorRepresentation_irreducible i
  let ρ := s.factorRepresentation i
  let q := Representation.BinaryOffender.actionHom ρ
  have hn : q.ker ≠ ⊤ := by
    intro he
    apply hi
    apply (s.central_iff_action i).mpr
    intro h x
    have hh : q h = 1 := show h ∈ q.ker from he ▸ mem_top h
    exact congrArg Additive.toMul ((actionHom_eq_one_iff ρ h).mp hh (Additive.ofMul x))
  have huni := source_dihedral_five_residual_sylow_unique hG T hempty hM hJ hu hmany hV l hp hd
  have hk := source_HStar_reduced_kernel_of_residual_unique hG T hM hJ hu hV huni hH q
    ρ.asGroupHom.rangeRestrict_surjective (irreducible_image_twoCore_eq_bot ρ) hn
  have hs := hV.chief_small_quotient hG T hempty hM hJ hH s i hi
  change ChapterB.ChiefSmallActor (H ⧸ q.ker) at hs
  exact hs.of_equiv (QuotientGroup.quotientMulEquivOfEq hk.symm)

end CFSG.Quasithin.Chapter15.Section02
