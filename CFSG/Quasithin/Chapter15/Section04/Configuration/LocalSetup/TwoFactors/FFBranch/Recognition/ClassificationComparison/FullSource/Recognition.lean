module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.ActorRows
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.Nonquasisimple
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FullSource.SymmetricThree
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.SectionAlternatives.Source
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.BinaryG2
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ExceptionalFixedSpace.TripleSix
/-!
# Full-source recognition on the actual quotient action

The nonquasisimple source rows give S₃ × S₃. For a quasisimple ambient
component, the adequate FF classifier yields a bounded branch and the full
Goldschmidt source forces its actor into the small list. Every source section
then contradicts the seed centralizer, through the existing ordinary, binary
G₂, and triple-six fixed-space calculations on the same offender action.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.6.18, pp.309–310; B.5.1/B.5.6, pp.99–110; 15.4.18, p.1163.
-/

public section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
open QuasisimpleComparison
universe u v
variable {D : Type u} [Group D] [Finite D] {K : GroupClass.{u}}
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V} {G₁ G₂ : Subgroup D}
attribute [local instance] offenderSubgroup_normal

theorem ClassifiedAction.bounded_of_quasisimple_ambient
    (h : ClassifiedAction K ρ G₁ G₂) (hL : IsQuasisimple (generalizedFitting D)) :
    Nonempty (BoundedBranch (ρ.comp (offenderSubgroup ρ).subtype)) := by
  cases h.ffAlternatives with
  | trivial ht =>
    let : Subsingleton (offenderSubgroup ρ) := ht
    let : Nontrivial (offenderSubgroup ρ) := FFAlternatives.nontrivial_of_ff _ h.ffWitness
    obtain ⟨g,hg⟩ := exists_ne (1 : offenderSubgroup ρ)
    exact (hg (Subsingleton.elim _ _)).elim
  | quasisimple hq c => exact h.bounded_branch hq c
  | symmetricThree c => exact (h.not_symmetricThree ⟨c.equiv⟩).elim
  | twoFactors c => exact (ProductComparison.sourceTwoFactor_not_quasisimple ρ c hL).elim
  | outerSixThree c => exact (OuterGroupComparison.outerShape_not_quasisimple ρ c hL).elim
  | hyperplane c => exact (ProductComparison.hyperplane_not_quasisimple ρ c hL).elim

variable {H : Type u} [Group H] [Finite H]

theorem ClassifiedAction.quotient_equiv
    (P : Sylow 2 H) (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]
    (hC : centralizer (Z : Set H) = (P : Subgroup H))
    {G₁ G₂ : Subgroup (coreQuotient H)}
    (h : ClassifiedAction K (quotientAction P Z hC) G₁ G₂) :
    Nonempty (coreQuotient H ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  by_cases hL : IsQuasisimple (generalizedFitting (coreQuotient H))
  · obtain ⟨b⟩ := h.bounded_of_quasisimple_ambient hL
    have ha := h.smallActor_of_quasisimple_ambient hL b
    have he := offenderAction_exceptionalSection_of_models P Z hC _ b.source.sectionData
      (b.sectionAlternatives ha)
    obtain ⟨hf,hs⟩ := offenderAction_tripleSix_of_exceptionalSection P Z hC _ b.source.sectionData he
    exact (offenderAction_not_tripleSix P Z hC _ b.source.sectionData hf hs).elim
  · exact h.nonquasisimple_quotient hL

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FullSource
