module

public import Theory.GroupTheory.SimpleSectionAction.Surjective
public import Theory.GroupTheory.SimpleSectionAction.Core
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.Action
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.CyclicFactors

/-!
# The actual section actions in the parameter reduction

The nonabelian factor hypothesis quantifies over genuine simple quotients of
subnormal subgroups and uses only the automorphisms induced by the endpoint
stabilizer in T. Surjective pullback preserves that exact image, so the
hypothesis passes to G/Y. For the local core section, its inner extension is
the literal pCoreJoinAction image; the existing action theorem then supplies
generation of J N_T(J). Cyclic factors use the split extension, retaining the
cyclic factor itself, and the independently proved solvable generation theorem.

The normal-product induction step and the remainder of E.1.11 are separate
obligations. In particular, an isomorphism of simple factors without control
of their induced automorphisms is not enough for that induction step.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.11, printed pp.212--214 (combined manuscript of 1 March 2004).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE
universe u
variable {G H : Type u} [Group G] [Group H]

/-- The generation form of the source hypothesis on nonabelian composition
sections. Conversion from attained parameter bounds remains with E.1.11's
assembly. Cyclic sections are handled by solvable generation separately. -/
def NonabelianSectionActionBound (i : ℕ) (T : Subgroup G) : Prop :=
  ∀ (L : Type u) [Group L] [Finite L] (s : ChiefFactor.SimpleSection G L),
    ¬ IsMulCommutative L → IsEGenerated i (s.extension T)

/-- Pullback of both endpoints proves factor-bound descent through a surjection. -/
theorem NonabelianSectionActionBound.map_surjective {i : ℕ} {T : Subgroup G}
    (h : NonabelianSectionActionBound i T) (f : G →* H) (hf : Function.Surjective f) :
    NonabelianSectionActionBound i (T.map f) := by
  intro L _ _ s hn
  have hg := h L (s.lift f hf) hn
  exact hg.map_equiv (MulEquiv.subgroupCongr (s.lift_extension f hf T))

/-- The literal quotient G/Y inherits the hypothesis used by the induction. -/
theorem NonabelianSectionActionBound.quotient {i : ℕ} {T : Subgroup G}
    (h : NonabelianSectionActionBound i T) (Y : Subgroup G) [Y.Normal] :
    NonabelianSectionActionBound i (T.map (QuotientGroup.mk' Y)) :=
  h.map_surjective (QuotientGroup.mk' Y) (QuotientGroup.mk'_surjective Y)

/-- The factor hypothesis applies to the actual core-quotient action of J N_T(J).
No arbitrary automorphism subgroup or local generation conclusion is assumed. -/
theorem NonabelianSectionActionBound.coreNormalizer [Finite G] {i : ℕ} {T : Subgroup G}
    (h : NonabelianSectionActionBound i T) (hT : IsPGroup 2 T)
    (J : Subgroup G) (hJ : J.IsSubnormal) [IsSimpleGroup (J ⧸ pCore 2 J)]
    (hn : ¬ IsMulCommutative (J ⧸ pCore 2 J)) :
    IsEGenerated i (J ⊔ (T ⊓ normalizer J) : Subgroup G) := by
  let s := ChiefFactor.SimpleSection.coreSection 2 J hJ
  apply isEGenerated_join_of_pCoreJoinAction J (T ⊓ normalizer J) inf_le_right
    (hT.to_le inf_le_left) (s.center_eq_bot hn)
  have hg := h _ s hn
  exact hg.map_equiv (MulEquiv.subgroupCongr
    (ChiefFactor.SimpleSection.coreSection_extension 2 J T hJ))

variable {L : Type u} [Group L] [Finite L]

/-- A cyclic section uses its actual split extension, even for C₂. Solvability
of the whole ambient group is not required for this factor calculation. -/
theorem simpleSection_commutative_splitExtension_isEGenerated_one
    (s : ChiefFactor.SimpleSection G L) (T : Subgroup G) [IsMulCommutative L] :
    IsEGenerated 1 (s.splitExtension T) := by
  let := s.simple
  let r : ChiefFactor.SimpleSection L L := ChiefFactor.simpleSectionOfSurjective
    ⊤ IsSubnormal.top (⊤ : Subgroup L).subtype (by
      intro x
      exact ⟨⟨x, mem_top x⟩, rfl⟩)
  exact simpleSection_cyclic_extension_isEGenerated_one r (s.action T).range

end CFSG.Quasithin.ChapterE
