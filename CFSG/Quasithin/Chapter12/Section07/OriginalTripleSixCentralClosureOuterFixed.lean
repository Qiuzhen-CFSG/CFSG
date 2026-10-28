module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureOuterModel
public import Theory.Representation.HexacodeAction.WeightFourFullCoreFixed

/-!
# The actual fixed subgroup of the original outer closure

The retained full product-core marking identifies the actual image with
the full vector-stabilizer two-core. Its fixed binary line transports
through the unchanged chosen-module coordinates to the original <z>.

Source: Aschbacher--Smith, conclusion following12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Atlas.Codes
open Theory.SpecificGroups.SymmetricSix DuadCalculation
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- The outer closure fixes precisely the original central involution in U. -/
theorem original_tripleSix_central_closure_outer_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    U ⊓ centralizer (W : Set G) = zpowers (z : G) := by
  let C := centralizer ({(z : G)} : Set G)
  let W := conjugateSpanBy (tripleSixPoint D a z) (conjugateSpanBy U C)
  let c := tripleSixPointCoordinates D a
  let v := (c z).toAdd
  obtain ⟨hWT, f, _, _, _, hchart, hfix, e, _, _, _, hprod⟩ :=
    original_tripleSix_central_closure_outer_model h structural D a z hz hzT hnot houter
  let S := Hexacode.fullVectorStabilizer v
  let N := (inducedAutomizer U W).map f
  let B := N.subgroupOf S
  have hB : B = pCore 2 S := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact hprod.trans (DuadCalculation.productCore_eq.trans (pCore_map_iso 2 e).symm)
  have hN : N = S.pCoreIn 2 := by
    calc
      N = B.map S.subtype := (map_subgroupOf_eq_of_le hfix).symm
      _ = S.pCoreIn 2 := by rw [hB]; rfl
  have hv := tripleSix_sylow_fixed_weightFour D a z hz hzT
  apply le_antisymm
  · intro u hu
    have hf : (c ⟨u, hu.1⟩).toAdd ∈ fixedSpace Hexacode.action (S.pCoreIn 2) := by
      intro g
      have hg : g.val ∈ N := hN.symm ▸ g.property
      obtain ⟨b, ⟨w, hw, hwb⟩, hbg⟩ := hg
      have he : (U.normalizerMonoidHom.rangeRestrict w).val ⟨u, hu.1⟩ = ⟨u, hu.1⟩ := by
        apply Subtype.ext
        exact mul_inv_eq_of_eq_mul (mem_centralizer_iff.mp hu.2 w hw)
      have hh := hchart (U.normalizerMonoidHom.rangeRestrict w) ⟨u, hu.1⟩
      rw [he, hwb, hbg] at hh
      exact hh.symm
    rw [Hexacode.weightFourFullCore_fixed v hv] at hf
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hf
    have hr01 : r = 0 ∨ r = 1 := by
      fin_cases r
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hr01 with rfl | rfl
    · have he : c ⟨u, hu.1⟩ = c 1 := by
        apply Multiplicative.toAdd.injective
        rw [c.map_one]
        change (c ⟨u, hu.1⟩).toAdd = 0
        simpa only [zero_smul] using hr.symm
      have hu1 : u = 1 := congrArg Subtype.val (c.injective he)
      exact hu1 ▸ one_mem _
    · have he : c ⟨u, hu.1⟩ = c z := by
        apply Multiplicative.toAdd.injective
        change (c ⟨u, hu.1⟩).toAdd = v
        simpa only [one_smul] using hr.symm
      have huz : u = (z:G) := congrArg Subtype.val (c.injective he)
      exact huz ▸ mem_zpowers (z:G)
  · apply zpowers_le.mpr
    refine ⟨z.property, ?_⟩
    apply mem_centralizer_iff.mpr
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hzT (hWT hw))

end CFSG.Quasithin.Chapter12.Section07
