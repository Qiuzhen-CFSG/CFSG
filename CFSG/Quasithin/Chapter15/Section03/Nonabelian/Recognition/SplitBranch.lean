module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Action
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.Statements
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.Models
public import Theory.Representation.BinaryQuadraticConstituent

/-!
# Orthogonal constituents in the two-summand branch of 15.3.58

These deductions use the literal representation of `H/O₂(H)` on `U/Z`.
Non-self-duality forces the irreducible summands to be totally singular;
the nondegenerate polar form then identifies the second with the dual of the
first for their same restricted `K*`-action.

These are conditional intermediate results. Recognition from G.6.4, construction
of the full automorphism group, the specified element's interchange of the
summands, and the extraspecial plus-type isomorphism remain separate obligations.
No theorem here asserts the complete source lemma.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.58,
printed pp.1148–1149, especially the two-summand paragraph on p.1149.
-/

@[expose] public section

open Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch
variable {G : Type*} [Group G] [Finite G] (Z ZS : Subgroup G)
  [(Z.subgroupOf (closureU Z ZS)).Normal]
  [IsElementaryAbelian 2 (VectorQuotient Z ZS)]
  (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))

/-- The actual source quadratic form vanishes on a non-self-dual constituent. -/
theorem constituent_totally_singular
    (K : Subgroup (ActorQuotient Z))
    (q : QuadraticForm (ZMod 2) (Space Z ZS))
    (hq : ∀ a v, q (actorRepresentation Z ZS hkernel a v) = q v)
    (J : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype))
    (hJ : J.toRepresentation.IsIrreducible)
    (hdim : 1 < Module.finrank (ZMod 2) J.toSubmodule)
    (hdual : ¬ Nonempty (Representation.Equiv J.toRepresentation J.toRepresentation.dual)) :
    ∀ v ∈ J.toSubmodule, q v = 0 := by
  let := hJ
  have hz := BinaryQuadraticConstituent.quadratic_eq_zero_of_not_self_dual
    J.toRepresentation hdim (q.comp J.toSubmodule.subtype)
    (fun a v => hq a.val v.val) hdual
  intro v hv
  exact congrArg (fun Q : QuadraticForm (ZMod 2) J.toSubmodule => Q ⟨v, hv⟩) hz

/-- Both summands are singular and paired for the same `K*`-action. -/
theorem summands_singular_and_dual
    (K : Subgroup (ActorQuotient Z))
    (q : QuadraticForm (ZMod 2) (Space Z ZS))
    (hq : ∀ a v, q (actorRepresentation Z ZS hkernel a v) = q v)
    (hnd : q.polarBilin.Nondegenerate)
    (J₁ J₂ : Subrepresentation ((actorRepresentation Z ZS hkernel).comp K.subtype))
    (hc : IsCompl J₁.toSubmodule J₂.toSubmodule)
    (h₁ : J₁.toRepresentation.IsIrreducible)
    (h₂ : J₂.toRepresentation.IsIrreducible)
    (hdim : Module.finrank (ZMod 2) J₁.toSubmodule =
      Module.finrank (ZMod 2) J₂.toSubmodule)
    (hlarge : 1 < Module.finrank (ZMod 2) J₁.toSubmodule)
    (hdual₁ : ¬ Nonempty (Representation.Equiv J₁.toRepresentation J₁.toRepresentation.dual))
    (hdual₂ : ¬ Nonempty (Representation.Equiv J₂.toRepresentation J₂.toRepresentation.dual)) :
    (∀ v ∈ J₁.toSubmodule, q v = 0) ∧
    (∀ v ∈ J₂.toSubmodule, q v = 0) ∧
    Nonempty (Representation.Equiv J₂.toRepresentation J₁.toRepresentation.dual) := by
  have hs₁ := constituent_totally_singular Z ZS hkernel K q hq J₁ h₁ hlarge hdual₁
  have hs₂ := constituent_totally_singular Z ZS hkernel K q hq J₂ h₂
    (hdim ▸ hlarge) hdual₂
  exact ⟨hs₁, hs₂, ⟨BinaryQuadraticConstituent.crossPairingEquiv
    ((actorRepresentation Z ZS hkernel).comp K.subtype) q (fun a v => hq a.val v)
    J₂ J₁ hc.symm hnd hs₂ hdim.symm⟩⟩

/-- Once the actual constituent models have been constructed, their dimensions
force `s = 1`. The polar form makes them singular, inequivalent, and a
natural–dual pair for the first model's fixed actor isomorphism. -/
theorem geometry_of_natural_models
    (K : Subgroup (ActorQuotient Z)) (v : ActorQuotient Z) (s : ℕ)
    (p : SplitPair (actorRepresentation Z ZS hkernel) K v s)
    (q : QuadraticForm (ZMod 2) (Space Z ZS))
    (hq : ∀ a w, q (actorRepresentation Z ZS hkernel a w) = q w)
    (hnd : q.polarBilin.Nondegenerate)
    (m₁ : BinaryLinearThree.NaturalModel p.first.toRepresentation)
    (m₂ : BinaryLinearThree.NaturalModel p.second.toRepresentation) :
    s = 1 ∧
    (∀ w ∈ p.first.toSubmodule, q w = 0) ∧
    (∀ w ∈ p.second.toSubmodule, q w = 0) ∧
    (¬ Nonempty (Representation.Equiv p.first.toRepresentation p.second.toRepresentation)) ∧
    Nonempty (Representation.Equiv p.second.toRepresentation
      (BinaryLinearThree.W.dual.comp
        (m₁.actor.trans Matrix.PSL3Two.equiv.symm).toMonoidHom)) := by
  have hs : s = 1 := by
    have h₁ := p.first_dimension
    have h₂ := m₁.finrank_eq_three
    omega
  obtain ⟨h₁, h₂, ⟨e⟩⟩ := summands_singular_and_dual Z ZS hkernel K q hq hnd
    p.first p.second p.complement p.first_irreducible p.second_irreducible
    (p.first_dimension.trans p.second_dimension.symm)
    (by rw [m₁.finrank_eq_three]; decide) m₁.not_self_dual m₂.not_self_dual
  refine ⟨hs, h₁, h₂, ?_, ⟨e.trans m₁.dualEquiv⟩⟩
  rintro ⟨f⟩
  exact m₁.not_self_dual ⟨f.trans e⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch
