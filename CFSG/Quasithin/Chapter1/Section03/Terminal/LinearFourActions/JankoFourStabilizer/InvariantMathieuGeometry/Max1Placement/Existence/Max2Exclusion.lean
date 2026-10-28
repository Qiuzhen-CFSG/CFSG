module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Reduction
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.GroupTheory.SimpleSectionSolvableReduction.Model
public import Theory.Mathieu.M22.Basic
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Max2Exclusion.QuotientKernel
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.Max2Exclusion.MathieuMap
public import Theory.Mathieu.M22.Properties.NoOrder15

/-!
# Excluding local linear-four sections in the max2 subgroup

A local C-component is perfect in its join with the supplied Sylow subgroup,
and hence perfect as an abstract group. Thus it lies in the derived subgroup
of the literal max2 carrier. Its simple quotient L₄(2) has an element of order
15, exhibited by a binary Singer matrix. A map from that derived subgroup to
M₂₂ with solvable kernel transports the simple section to M₂₂; an element
mapping onto the Singer element then has a power of order 15.

The derived-subgroup map and the absence of order 15 in the concrete M₂₂ are
provided by the imported Mathieu-map and spectrum modules. The imported kernel
comparison proves the solvable kernel of the existing twelve-dimensional
action, which feeds that map. The final theorem below assembles these facts
into the unconditional max2 exclusion.

Source: Aschbacher–Smith A.3.12(17) and its Sylow-overgroup argument, printed
pp.47–48; proof of 1.3.9, p.514; GLS3 Table 5.3i, printed p.270.
-/

public section

open Subgroup
open scoped MatrixGroups

private def singer : SL(4, ZMod 2) :=
  ⟨![![0, 0, 0, 1], ![1, 0, 0, 1], ![0, 1, 0, 0], ![0, 0, 1, 0]], by decide +kernel⟩

private theorem singer_order : orderOf singer = 15 := by
  apply orderOf_eq_of_pow_and_pow_div_prime (by decide)
  · apply Subtype.ext
    decide +kernel
  · intro p hp hpd
    have h : p = 3 ∨ p = 5 := by
      have hm : p ∣ 3 * 5 := hpd
      rcases hp.dvd_mul.mp hm with h3 | h5
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h3)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h5)
    rcases h with rfl | rfl
    · exact of_decide_eq_true (by decide +kernel)
    · exact of_decide_eq_true (by decide +kernel)

private theorem four_properties {Q : Type*} [Group Q]
    (h : ClassicalGroup.IsPSL Q 4 2) :
    IsSimpleGroup Q ∧ Group.IsPerfect Q ∧ ∃ q : Q, orderOf q = 15 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  let _ := Fintype.ofFinite F
  let f : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let ep := e.trans (Atlas.fieldEquivPSL 4 f.symm)
  let es := ep.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 4))
  let := Atlas.psl_simple_high_rank (F := ZMod 2) 4 (by decide)
  let := Atlas.psl_perfect (F := ZMod 2) 4 (by decide)
  refine ⟨ep.isSimpleGroup, Group.IsPerfect.ofSurjective (f := ep.symm.toMonoidHom) ep.symm.surjective,
    es.symm singer, ?_⟩
  exact (es.symm.orderOf_eq singer).trans singer_order

private theorem no_section_of_solvable_kernel {G H Q : Type*}
    [Group G] [Group H] [Finite H] [Group Q] [IsSimpleGroup Q] [Group.IsPerfect Q]
    (f : G →* H) [Group.IsSolvable f.ker]
    (hH : ∀ x : H, orderOf x ≠ 15)
    (q : Q) (hq : orderOf q = 15)
    (U : Subgroup G) (π : U →* Q) (hπ : Function.Surjective π) : False := by
  let m : Group.SolvableKernelModel G f.range :=
    ⟨f.ker, inferInstance, inferInstance, QuotientGroup.quotientKerEquivRange f⟩
  obtain ⟨W, g, hg⟩ := m.simple_section (Group.IsPerfect.not_isSolvable Q) U π hπ
  obtain ⟨w, hw⟩ := hg q
  let x : H := w.val.val
  have hd : 15 ∣ orderOf x := by
    rw [← hq, ← hw]
    have h := orderOf_map_dvd g w
    simpa only [← Subgroup.orderOf_coe] using h
  exact hH (x ^ (orderOf x / 15))
    (orderOf_pow_orderOf_div (orderOf_pos x).ne' hd)

namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
open Section02.LocalModels
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- The two remaining concrete inputs imply the exact local exclusion.
Only perfectness is extracted from relative C-component membership; no ambient
normality or simplicity of J₄ is used. -/
theorem max2LocalExclusion_of_commutatorMap_and_spectrum
    (f : commutator sourceSubgroup →* Sporadic.Mathieu.M22)
    [Group.IsSolvable f.ker]
    (hM : ∀ x : Sporadic.Mathieu.M22, orderOf x ≠ 15) : Max2LocalExclusion := by
  intro B T hB hlocal
  let C := B.subgroupOf (B ⊔ T.toSubgroup)
  let : Group.IsPerfect C := hlocal.perfect
  let eC : C ≃* B := subgroupOfEquivOfLe le_sup_left
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eC.toMonoidHom) eC.surjective
  have hBD : B ≤ commutator sourceSubgroup := by
    rw [← B.commutator_eq_self]
    exact commutator_mono le_top le_top
  let U := B.subgroupOf (commutator sourceSubgroup)
  let eU : U ≃* B := subgroupOfEquivOfLe hBD
  let π : U →* XiQuotient B := (QuotientGroup.mk' (pCore 2 B)).comp eU.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp eU.surjective
  obtain ⟨hs, hp, q, hq⟩ := four_properties hB
  let := hs
  let := hp
  exact no_section_of_solvable_kernel f hM q hq U π hπ

/-- The literal max2 carrier has no local component with quotient `L₄(2)`. -/
theorem max2LocalExclusion : Max2LocalExclusion := by
  obtain ⟨f, hf⟩ := Max2Exclusion.exists_commutatorMathieuMap
  let : Group.IsSolvable f.ker := hf
  exact max2LocalExclusion_of_commutatorMap_and_spectrum f
    Sporadic.Mathieu.m22_orderOf_ne_fifteen

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement
