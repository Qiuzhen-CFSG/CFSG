module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.Borel
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound.OddMover
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.SylowKernelCore

/-!
# The actual Cartan action on relative components

The source point normalizer is an SQTK-group for the full known-simple
catalogue. Lift the normal-or-index-two component-orbit theorem from its
two-core quotient. Every odd Cartan element therefore normalizes each
relative component of Y. Failure of the source commutator bound then gives
a nonidentity automorphism of the literal I/O₂(I), since O₂(I) ≤ O₂(Y).

No ambient normality of I or Y is imposed, and the two-component orbit
alternative is preserved for the subsequent Suzuki normalizer construction.
Source: Aschbacher--Smith 1.2.1(3) and 11.5.6(3), printed pp.780--781.
-/

public noncomputable section
open Subgroup
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Relative normality of Y carries its component into the original G₁. -/
theorem component_in_point_normalizer {I : Subgroup G}
    (hI : Source.ComponentIn E.Y I) : (I.subgroupOf E.G₁).IsCComponent := by
  let Y₀ := E.Y.subgroupOf E.G₁
  let : Y₀.Normal := (normal_subgroupOf_iff_le_normalizer E.Y_le_G₁).mpr
    E.G₁_normalizes_Y
  let e : E.Y ≃* Y₀ := (subgroupOfEquivOfLe E.Y_le_G₁).symm
  have h := (hI.2.map_equiv e).map_subtype
    (inferInstance : Y₀.Normal).isSubnormal
  have he : ((I.subgroupOf E.Y).map e.toMonoidHom).map Y₀.subtype =
      I.subgroupOf E.G₁ := by
    ext i
    constructor
    · rintro ⟨y, ⟨j, hj, rfl⟩, rfl⟩
      exact hj
    · intro hi
      exact ⟨e ⟨i, hI.1 hi⟩, ⟨⟨i, hI.1 hi⟩, hi, rfl⟩, rfl⟩
  exact he ▸ h

/-- Preserve the possible orbit of two components in the source local group. -/
theorem component_normal_or_index_two (hp : E.point ≠ ⊥) {I : Subgroup G}
    (hI : Source.ComponentIn E.Y I) :
    (I.subgroupOf E.G₁).Normal ∨
      (normalizer (I.subgroupOf E.G₁ : Set E.G₁)).index = 2 := by
  have hH : IsSQTK KnownSimple.IsKnownSimple E.G₁ := E.input.source.simpleQTKE.twoLocal_sqtk
    (D.centralQuotientPreimage_twoLocal E.point hp)
  have hQ : IsSQTK KnownSimple.IsKnownSimple (E.G₁ ⧸ pCore 2 E.G₁) := by
    refine ⟨?_, hH.isKGroup.quotient (pCore 2 E.G₁)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _
      pCore_isPGroup).trans (hH.stronglyQuasithin p hp ho)
  let := pCore_isNilpotent (p := 2) (G := E.G₁)
  have hI₀ := E.component_in_point_normalizer hI
  exact cComponent_normal_or_index_two_of_quotient hI₀ (pCore 2 E.G₁)
    (ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput _)
      hQ (pCore_quotient_pCore_eq_bot 2) (hI₀.map_quotient _))

/-- Odd order rules out interchanging the two possible component conjugates. -/
theorem cartan_normalizes_component (hp : E.point ≠ ⊥) (hX : E.X ≤ E.G₁)
    (ho : Odd (Nat.card E.X)) {I : Subgroup G} (hI : Source.ComponentIn E.Y I) :
    E.X ≤ normalizer (I : Set G) := by
  intro x hx
  let a : E.G₁ := ⟨x, hX hx⟩
  have ha : a ∈ normalizer (I.subgroupOf E.G₁ : Set E.G₁) := by
    rcases E.component_normal_or_index_two hp hI with hn | hi
    · exact (normalizer_eq_top_iff.mpr hn).symm ▸ mem_top a
    · have haodd : Odd (orderOf a) := by
        rw [← Subgroup.orderOf_coe a]
        exact ho.of_dvd_nat (E.X.orderOf_dvd_natCard hx)
      exact (zpowers_le.mpr
        ((normalizer (I.subgroupOf E.G₁ : Set E.G₁)).sq_mem_of_index_two hi a))
        (mem_zpowers_pow_iff.mpr (Nat.coprime_two_left.mpr haodd))
  rw [mem_normalizer_iff]
  intro i
  constructor
  · intro hi
    exact (mem_normalizer_iff.mp ha ⟨i, E.Y_le_G₁ (hI.1 hi)⟩).mp hi
  · intro hi
    have hiH : i ∈ E.G₁ := by
      have hh := E.G₁.mul_mem (E.G₁.mul_mem (E.G₁.inv_mem (hX hx))
        (E.Y_le_G₁ (hI.1 hi))) (hX hx)
      simpa [mul_assoc] using hh
    exact (mem_normalizer_iff.mp ha ⟨i, hiH⟩).mpr hi

/-- Noncentrality modulo O₂(Y) yields an actual nonidentity quotient actor. -/
theorem exists_component_quotient_mover (hp : E.point ≠ ⊥) (hX : E.X ≤ E.G₁)
    (ho : Odd (Nat.card E.X)) {I : Subgroup G} (hI : Source.ComponentIn E.Y I)
    (hm : ¬ ⁅I, E.X⁆ ≤ E.Y.pCoreIn 2) :
    ∃ x : normalizer (I : Set G), (x : G) ∈ E.X ∧ coreQuotientAction I x ≠ 1 := by
  classical
  have hn := E.cartan_normalizes_component hp hX ho hI
  have hcore : I.pCoreIn 2 ≤ E.Y.pCoreIn 2 := by
    have h := map_mono (f := E.Y.subtype) (pCoreIn_le_of_subnormal 2 hI.2.subnormal)
    rw [map_pCoreIn_of_injective 2 _ _ E.Y.subtype_injective,
      map_subgroupOf_eq_of_le hI.1] at h
    exact h
  by_contra! h
  apply hm
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx i hi
  have hxk : x ∈ coreQuotientCentralizer I :=
    ⟨⟨x, hn hx⟩, h ⟨x, hn hx⟩ hx, rfl⟩
  exact hcore (coreQuotientCentralizer_commutator hxk hi)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
