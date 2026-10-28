module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionRows
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionPrimeIndex
public import Theory.GroupTheory.FittingFiveModels

/-!
# Removing the Fitting-five row before the global Thompson residual

A marked-five chosen action with Fitting subgroup of order five is D₁₀ or
Sz(2). In both cases its actual Sylow image has prime index five. The
prime-index maximal-overgroup argument and the independently proved
marked-five H-star wreath theorem give the source contradiction without
15.1.14. Consequently a failure of 15.1.14 on the original full module
leaves the three large actions or the cyclic-fifteen Fitting alternative.

The cyclic-fifteen and large-action cases remain genuine obligations.
Source: Aschbacher--Smith 15.1.7(5), 15.1.14 and 15.2.1--28,
printed pp.1087--1091 and 1104--1120.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter15.Section02
open Section01 Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

/-- The marked-five source is impossible when its literal whole action has
Fitting order five; no global Thompson residual or counterexample prior is used. -/
theorem source_chosen_marked_five_contradiction_of_fitting_five
    {T : Sylow 2 G} {M Mc V : Subgroup G} (h : ChosenSmallSource T M Mc V)
    (hd : letI := h.prepared.elementary
      ∃ l : LocalGeneration ((imageRepresentation M V h.prepared.normalized).comp
        (Jhat (imageRepresentation M V h.prepared.normalized)).subtype),
        DihedralMarking l 5 2)
    (hF : Nat.card (fittingSubgroup (internalActionImage M V h.prepared.normalized)) = 5) :
    False := by
  let := h.prepared.elementary
  let D := internalActionImage M V h.prepared.normalized
  let f : M →* D := (actionHom M V h.prepared.normalized).rangeRestrict
  let P := (T.subtype h.maximal.1.2).mapSurjective
    (f := f) (actionHom M V h.prepared.normalized).rangeRestrict_surjective
  have htwo : 2 ∣ Nat.card D := by
    obtain ⟨l,hl⟩ := hd
    have hc : Nat.card (Jhat (imageRepresentation M V h.prepared.normalized)) = 10 :=
      (Nat.card_congr hl.dihedral.some.toEquiv).trans DihedralGroup.nat_card
    exact (by decide : 2 ∣ 10).trans (hc ▸ (Jhat
      (imageRepresentation M V h.prepared.normalized)).card_subgroup_dvd_card)
  have hmodels := small_models_of_fitting_card_five
    (source_chosen_action_isSolvable h.ambient T h.empty h.maximal V
      h.prepared.normalized h.prepared.le_local) hF htwo
  have hcard : Nat.card D = 10 ∨ Nat.card D = 20 := by
    rcases hmodels with he | he
    · exact Or.inl ((Nat.card_congr he.some.toEquiv).trans DihedralGroup.nat_card)
    · exact Or.inr ((Nat.card_congr he.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card)
  apply source_chosen_marked_five_contradiction_of_prime_sylow_index h hd
  have hi : (P : Subgroup D).index = 5 := by
    have he := (P : Subgroup D).card_mul_index
    rcases hcard with hc | hc
    · have hP : Nat.card P = 2 := by rw [P.card_eq_multiplicity,hc]; decide +kernel
      rw [hP,hc] at he
      omega
    · have hP : Nat.card P = 4 := by rw [P.card_eq_multiplicity,hc]; decide +kernel
      rw [hP,hc] at he
      omega
  change (P : Subgroup D).index.Prime
  rw [hi]
  decide

end CFSG.Quasithin.Chapter15.Section02

namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06
open ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource
variable {G : Type*} [Group G] [Finite G]

universe u
private theorem marked_five_fitting_kernel
    {D W : Type u} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ)
    (l : LocalGeneration ρ) (hd : DihedralMarking l 5 2) :
    fittingSubgroup D = l.kernel := by
  let := l.normal
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic l.kernel := isCyclic_of_prime_card hd.card_kernel
  apply le_antisymm
  · have hcore := SmallBinaryFiveOvergroup.twoCore_eq_bot ρ hf hd.dimension l.kernel hd.card_kernel
    exact (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore).trans
      (pPrimeCore_le_pResidual.trans_eq l.kernel_eq_twoResidual.symm)
  · exact le_sSup ⟨inferInstance,inferInstance⟩

/-- The source-exact remaining full-module cases: large actions or the
marked quintic action with cyclic-four Sylow and cyclic-fifteen Fitting subgroup. -/
theorem source_full_residual_failure_large_or_fifteen
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : M ≠ Mc)
    (hno : ¬ Nonempty (NaturalOrthogonalAction M (localModule T M)))
    (hp : PreparedChosenModule T M (localModule T M))
    (hnot : ¬ (pResidual 2 (centralizer (centralInvolutions T : Set G))).map
      (centralizer (centralInvolutions T : Set G)).subtype ≤
        centralizer (thompsonFixed T (localModule T M) : Set G)) :
    letI := hp.elementary
    let V := localModule T M
    let D := internalActionImage M V hp.normalized
    let ρ := imageRepresentation M V hp.normalized
    let K := Jhat ρ
    let S := ((T : Subgroup G).subgroupOf M).map (actionHom M V hp.normalized).rangeRestrict
    LargeChosenAction T M V hp.normalized ∨
      (∃ l : LocalGeneration (ρ.comp K.subtype), DihedralMarking l 5 2 ∧
        Nonempty (S ≃* Multiplicative (ZMod 4)) ∧
        Nonempty (fittingSubgroup D ≃* Multiplicative (ZMod 15))) := by
  let := hp.elementary
  let V := localModule T M
  let D := internalActionImage M V hp.normalized
  let ρ := imageRepresentation M V hp.normalized
  let K := Jhat ρ
  rcases source_full_residual_failure_large_or_quintic hG T hempty hM hmany hJ hu hne hno hp hnot
    with hl | ⟨l,hd,hS,hF⟩
  · exact Or.inl hl
  have hpm : PrimeDimensionOptions 5 2 := (primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)
  let h : Section02.ChosenSmallSource T M Mc V :=
    ⟨hG,hempty,hM,hmany,hJ,hu,hne,hp,Or.inl rfl,Or.inl ⟨l,5,2,hpm,hd⟩⟩
  rcases hF with hF | hF
  · have hk := marked_five_fitting_kernel (ρ.comp K.subtype)
      ((imageRepresentation_injective M V hp.normalized).comp K.subtype_injective) l hd
    have hc : Nat.card (fittingSubgroup D) = 5 := by
      rw [hF,hk,card_map_of_injective K.subtype_injective]
      exact hd.card_kernel
    exact (Section02.source_chosen_marked_five_contradiction_of_fitting_five h ⟨l,hd⟩ hc).elim
  · exact Or.inr ⟨l,hd,hS,hF⟩

end CFSG.Quasithin.Chapter15.Section01
