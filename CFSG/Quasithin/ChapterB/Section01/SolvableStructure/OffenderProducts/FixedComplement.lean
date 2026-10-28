module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts.Internal
public import Theory.Representation.BinaryOffender.NaturalPlaneSplitting


/-!
# Fixed complements of the concrete solvable FF factors

Each actual natural binary plane has a fixed complement. The cross-fixed
property of distinct factors assembles these complements for all factors
and for any selected subfamily, retaining the literal subgroup inclusions.

Source: Aschbacher–Smith, proof of 14.1.7, printed p.977, using the
concrete B.1.8 factor witness (printed p.70).
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} (d : SolvableFFFactors ρ)

theorem support_complement (i : Fin d.count) :
    IsCompl (subspaceCommutator ρ ⊤ (d.factor i)) (fixedSpace ρ (d.factor i)) := by
  have hc := Representation.natural_support_complement (ρ.comp (d.factor i).subtype)
    (d.factorModel i) (subspaceCommutator ρ ⊤ (d.factor i)) (d.naturalEquiv i)
    (d.naturalEquiv_action i)
    (fun g v => Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩)
  have he : fixedSpace (ρ.comp (d.factor i).subtype) ⊤ = fixedSpace ρ (d.factor i) := by
    ext v
    exact ⟨fun h g => h ⟨g, Subgroup.mem_top _⟩, fun h g => h g⟩
  rwa [he] at hc

private theorem fixed_iSup {ι : Type*} (C : ι → Subgroup G) :
    fixedSpace ρ (⨆ i, C i) = ⨅ i, fixedSpace ρ (C i) := by
  ext v
  constructor
  · intro hv
    exact (Submodule.mem_iInf _).mpr fun i a => hv ⟨a, le_iSup C i a.property⟩
  · intro hv a
    refine Subgroup.iSup_induction C (C := fun a => ρ a v = v) a.property ?_ ?_ ?_
    · intro i a ha
      exact ((Submodule.mem_iInf _).mp hv i) ⟨a, ha⟩
    · simp
    · intro a b ha hb
      simp only [map_mul, Module.End.mul_apply, ha, hb]

include d in
theorem moved_complement :
    IsCompl (subspaceCommutator ρ ⊤ (offenderSubgroup ρ))
      (fixedSpace ρ (offenderSubgroup ρ)) := by
  rw [← d.iSup_support, ← d.iSup_factor, fixed_iSup]
  exact Submodule.isCompl_iSup_iInf_of_cross_le _ _ d.support_complement
    (fun _ _ hij => d.support_le_fixedSpace_other hij.symm)

theorem selected_support_complement (I : Set (Fin d.count)) :
    IsCompl (⨆ i ∈ I, subspaceCommutator ρ ⊤ (d.factor i))
      (fixedSpace ρ (⨆ i ∈ I, d.factor i)) := by
  rw [iSup_subtype', iSup_subtype', fixed_iSup]
  exact Submodule.isCompl_iSup_iInf_of_cross_le _ _ (fun i => d.support_complement i)
    (fun i j hij => d.support_le_fixedSpace_other
      (fun h => hij (Subtype.ext h.symm)))

end CFSG.Quasithin.ChapterB.SolvableFFFactors
