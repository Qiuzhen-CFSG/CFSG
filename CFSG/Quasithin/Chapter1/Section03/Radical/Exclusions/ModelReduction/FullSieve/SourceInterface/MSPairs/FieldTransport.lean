module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs
public import Theory.Representation.SpecialLinearFieldTransport

/-!
# Field transport of the complete C.1.34 alternatives

Every section is transported by an additive equivalence intertwining its
actual conjugation action. The natural module and its dual use the same
entrywise field map on SL₃, including both repeated summands. The central,
Frattini, radical and index-seven assertions refer to the original subgroups
and therefore survive this change of coordinates literally.

Source: Aschbacher--Smith C.1.34, printed pp.136--137.
-/

public section
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Subgroup Representation
variable {G : Type*} [Group G]

/-- Change the coordinates of a section while retaining its literal quotient
and conjugation equations. Only the additive structure of the coordinates is
needed, so this also applies to semilinear coefficient transport. -/
theorem HasSectionModel.transport
    {B B' V V' F F' : Type*} [Group B] [Group B']
    [AddCommGroup V] [AddCommGroup V'] [Field F] [Field F']
    [Module F V] [Module F' V'] {L D E : Subgroup G}
    {a : L →* B} {a' : L →* B'} {rho : Representation F B V}
    {rho' : Representation F' B' V'} (h : HasSectionModel L D E a rho)
    (f : V ≃+ V')
    (hf : ∀ l v, f (rho (a l) v) = rho' (a' l) (f v)) :
    HasSectionModel L D E a' rho' := by
  obtain ⟨hED, hLD, hLE, hn, e, he⟩ := h
  let := hn
  refine ⟨hED, hLD, hLE, hn, e.trans f.toMultiplicative, ?_⟩
  intro l d d' hd
  change f (Multiplicative.toAdd (e (QuotientGroup.mk' _ d'))) = _
  rw [he l d d' hd]
  exact hf l _

namespace MSFieldTransport
variable {F K : Type*} [Field F] [Field K]
  {L D E : Subgroup G}
  (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F)
  (f : F ≃+* K)
open SpecialLinearFieldTransport

private theorem natural_model
    (h : HasSectionModel L D E (linearThreeActor e) (specialLinearNatural 3)) :
    HasSectionModel L D E (linearThreeActor (e.trans (Atlas.fieldEquivSL 3 f)))
      (specialLinearNatural 3) :=
  h.transport (natural 3 f) (fun _ _ => natural_action 3 f _ _)

private theorem dual_model
    (h : HasSectionModel L D E (linearThreeActor e) (specialLinearNatural 3).dual) :
    HasSectionModel L D E (linearThreeActor (e.trans (Atlas.fieldEquivSL 3 f)))
      (specialLinearNatural 3).dual :=
  h.transport (dual 3 f) (fun _ _ => dual_action 3 f _ _)

private theorem natural_pair_model
    (h : HasSectionModel L D E (linearThreeActor e)
      ((specialLinearNatural 3).prod (specialLinearNatural 3))) :
    HasSectionModel L D E (linearThreeActor (e.trans (Atlas.fieldEquivSL 3 f)))
      ((specialLinearNatural 3).prod (specialLinearNatural 3)) := by
  apply h.transport ((natural 3 f).prodCongr (natural 3 f))
  intro l v
  exact Prod.ext (natural_action 3 f _ _) (natural_action 3 f _ _)

private theorem dual_pair_model
    (h : HasSectionModel L D E (linearThreeActor e)
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual)) :
    HasSectionModel L D E (linearThreeActor (e.trans (Atlas.fieldEquivSL 3 f)))
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) := by
  apply h.transport ((dual 3 f).prodCongr (dual 3 f))
  intro l v
  exact Prod.ext (dual_action 3 f _ _) (dual_action 3 f _ _)

end MSFieldTransport

/-- All five source cases change coefficients together; in particular, every
dual and repeated summand retains the transported common quotient marking. -/
theorem MSModuleAlternatives.fieldTransport
    {L R S : Subgroup G} {n : ℕ} {F K : Type} [Field F] [Field K]
    {e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F}
    (h : MSModuleAlternatives L R S n F e) (f : F ≃+* K) :
    MSModuleAlternatives L R S n K (e.trans (Atlas.fieldEquivSL 3 f)) := by
  dsimp only [MSModuleAlternatives] at h ⊢
  rcases h with h | h | h | h | h
  · exact Or.inl ⟨h.1, h.2.1, MSFieldTransport.natural_model e f h.2.2⟩
  · exact Or.inr (Or.inl ⟨MSFieldTransport.natural_pair_model e f h.1, h.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨MSFieldTransport.natural_model e f h.1,
      MSFieldTransport.dual_pair_model e f h.2.1, h.2.2⟩))
  · rcases h with ⟨hC, hcard, hcentral, hZ, hdisjoint, hU, hPhi, hD, hQ, hR⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hC, hcard, hcentral, hZ, hdisjoint,
      MSFieldTransport.natural_model e f hU, MSFieldTransport.dual_model e f hPhi,
      MSFieldTransport.dual_pair_model e f hD, MSFieldTransport.natural_pair_model e f hQ,
      hR⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨h.1, h.2.1,
      MSFieldTransport.natural_model e f h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩)))

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
