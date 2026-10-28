module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.CoreCertificate
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension.GeneratorRelations
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Splitting the augmentation-core-by-natural extension

The rectangular cochain certificate corrects an actual quotient section.
Its invariant range complements the specified seven-dimensional core.
Source: Aschbacher–Smith 14.7.51, printed p.1065.
-/

public noncomputable section
open Representation
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- Every natural quotient of an augmentation-core extension admits a
complement to the specified core, with the actual natural quotient action. -/
theorem SectionData.core_complement
    {ρ : Representation (ZMod 2) (Equiv.Perm (Fin 8)) W} {X : Subrepresentation ρ}
    (s : SectionData ρ X coreSeven naturalSix) :
    ∃ K : Subrepresentation ρ, IsCompl X.toSubmodule K.toSubmodule ∧
      ∃ eK : K.toSubmodule ≃ₗ[ZMod 2] V,
        ∀ g v, eK (K.toRepresentation g v) = naturalSix g (eK v) := by
  let B (i : Fin 7) : CoreRect := LinearMap.toMatrix' (s.cochain (adjacent i))
  obtain ⟨D,hD⟩ := core_relations_coboundary B
    (coreRelations_of_cocycle coreSeven naturalSix s.cochain s.cochain_mul
      coreSeven_adjacent naturalSix_adjacent)
  apply s.complement_of_generator_correction (Set.range adjacent)
    (Equiv.Perm.mclosure_swap_castSucc_succ 7) D.mulVecLin
  rintro g ⟨i,rfl⟩
  apply LinearMap.ext
  intro v
  have hB : s.cochain (adjacent i) v = (CoreA i*D+D*A i).mulVec v := by
    calc
      _ = (B i).mulVec v := (LinearMap.toMatrix'_mulVec _ _).symm
      _ = _ := congrArg (fun M : CoreRect => M.mulVec v) (hD i)
  rw [hB,coreSeven_adjacent,naturalSix_adjacent]
  simp only [LinearMap.sub_apply,LinearMap.comp_apply,Matrix.mulVecLin_apply,
    Matrix.add_mulVec,Matrix.mulVec_mulVec]
  ext r
  exact (CharTwo.sub_eq_add _ _).symm

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource.SelfExtension
