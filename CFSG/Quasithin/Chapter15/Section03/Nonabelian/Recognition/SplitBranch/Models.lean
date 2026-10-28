module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import Theory.Representation.PSL3Two.NaturalCoordinates

/-!
# The input pair and recognition output for the split branch

`SplitPair` chooses the witnesses of `TwoSummandAlternative` without adding
hypotheses. `HasNaturalModels` is the remaining recognition conclusion: each
literal constituent has actual PSL₃(2) group and module coordinates. The two
coordinate systems may initially use different group isomorphisms. The polar
pairing subsequently aligns them with one natural–dual action.

Neither definition asserts recognition. Its construction from the earlier
universal G.6.4 and the local source data remains a separate proof obligation.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.57(2b)
and the two-summand paragraph of 15.3.58, printed pp.1148–1149.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]

/-- A chosen pair from the already established two-summand alternative. -/
structure SplitPair (ρ : Representation (ZMod 2) H W)
    (K : Subgroup H) (v : H) (s : ℕ) where
  first : Subrepresentation (ρ.comp K.subtype)
  second : Subrepresentation (ρ.comp K.subtype)
  complement : IsCompl first.toSubmodule second.toSubmodule
  first_irreducible : first.toRepresentation.IsIrreducible
  second_irreducible : second.toRepresentation.IsIrreducible
  first_dimension : Module.finrank (ZMod 2) first.toSubmodule = s + 2
  second_dimension : Module.finrank (ZMod 2) second.toSubmodule = s + 2
  first_invariant : first.toSubmodule.map (ρ v) = first.toSubmodule
  second_invariant : second.toSubmodule.map (ρ v) = second.toSubmodule
  first_displacement : Module.finrank (ZMod 2)
    (LinearMap.range ((ρ v - LinearMap.id).comp first.toSubmodule.subtype)) = 1
  second_displacement : Module.finrank (ZMod 2)
    (LinearMap.range ((ρ v - LinearMap.id).comp second.toSubmodule.subtype)) = 1

/-- Choose the witnesses of the branch input; this is not a recognition step. -/
noncomputable def SplitPair.ofAlternative
    {ρ : Representation (ZMod 2) H W} {K : Subgroup H} {v : H} {s : ℕ}
    (h : TwoSummandAlternative ρ K v s) : SplitPair ρ K v s := by
  classical
  exact Classical.choice (by
    obtain ⟨J₁, J₂, hc, hi₁, hi₂, hd₁, hd₂, hv₁, hv₂, hr₁, hr₂⟩ := h
    exact ⟨⟨J₁, J₂, hc, hi₁, hi₂, hd₁, hd₂, hv₁, hv₂, hr₁, hr₂⟩⟩)

/-- The actual constituent models to be constructed by the G.6.4 argument. -/
def SplitPair.HasNaturalModels
    {ρ : Representation (ZMod 2) H W} {K : Subgroup H} {v : H} {s : ℕ}
    (p : SplitPair ρ K v s) : Prop :=
  Nonempty (BinaryLinearThree.NaturalModel p.first.toRepresentation) ∧
    Nonempty (BinaryLinearThree.NaturalModel p.second.toRepresentation)

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch
