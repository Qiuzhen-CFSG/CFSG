module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import Theory.SpecificGroups.PSL2.RootTwoRank
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTransfer

/-!
# The containing-component catalogue for the binary smaller subgroup

A binary PSL₂ subgroup of exponent at least two has two-rank at least two.
The containing C-component therefore cannot have noncentral Fitting
subgroup: that source branch has two-rank one. It is quasisimple, and the
full known-simple A.3.6 theorem supplies either its actual simple model
or its actual triple-cover model. No proper-embedding list is assumed.

Source: Aschbacher–Smith A.3.6, A.3.12 and C.5.13, pp.43–48,162–163.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02 Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]

/-- The binary smaller subgroup excludes both noncentral-Fitting rows of
A.3.6 without invoking the A.3.12 embedding alternatives. -/
theorem binary_containing_component_quasisimple
    {κ : GroupClass} (hG : IsSQTK κ G) (hO : pCore 2 G = ⊥)
    {B L : Subgroup G} (hL : L.IsCComponent) (hBL : B ≤ L)
    {n : ℕ} (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2 ^ n)) :
    IsQuasisimple L := by
  apply NoncentralFitting.quasisimple_of_two_le_two_rank hG hO hL
  have hb : n ≤ primeRank 2 B := by
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hB
    rw [primeRank_equiv 2 e]
    exact Theory.PSL2.root_two_rank_ge F hF
  exact (show 2 ≤ n by omega).trans
    (hb.trans (_root_.primeRank_le_of_injective 2 (inclusion hBL) (inclusion_injective hBL)))

/-- The full source carrier catalogue of the containing component, retaining
both the simple group and the precise triple-cover alternatives. -/
theorem binary_containing_component_models_knownSimple
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    {B L : Subgroup G} (hL : L.IsCComponent) (hBL : B ≤ L)
    {n : ℕ} (hn : 1 < n) (hB : ClassicalGroup.IsPSL B 2 (2 ^ n)) :
    IsQuasisimple L ∧
      ((IsSimpleGroup L ∧ TheoremCModel L) ∨
        (Nonempty (center L ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel L)) := by
  have hq := binary_containing_component_quasisimple hG hO hL hBL hn hB
  let : IsQuasisimple L := hq
  have hfit : generalizedFitting L ≠ fittingSubgroup L := by
    intro he
    have hf : fittingSubgroup L = ⊤ := he.symm.trans generalizedFitting_eq_top_of_quasisimple
    let : Group.IsSolvable (⊤ : Subgroup L) := hf ▸
      (inferInstance : Group.IsSolvable (fittingSubgroup L))
    exact hL.not_isSolvable
      (Group.isSolvable_of_surjective (f := (topEquiv (G := L)).toMonoidHom)
        (topEquiv (G := L)).surjective)
  have hsource := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    G hG hO L hL
  refine ⟨hq, ?_⟩
  cases hsource.1 with
  | simple _ hs hm => exact .inl ⟨hs, hm⟩
  | cover _ hc hm => exact .inr ⟨hc, hm⟩
  | natural h => exact (hfit h.1).elim
  | nilpotent h => exact (hfit h.1).elim

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
