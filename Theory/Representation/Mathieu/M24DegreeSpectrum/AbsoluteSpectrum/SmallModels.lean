module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.Inputs
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.CodePair
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFourExtension

/-!
# Assembly of the four small absolute M24 modules

The native code and cocode give two inequivalent simple eleven-dimensional
modules over every field of characteristic two. Adjoin the independently
constructed pair of degree forty-four. Dimension separates the pairs and
reindexing gives precisely the four-element family required by the absolute
spectrum contract.

The degree-forty-four pair comes from the native Golay exterior contraction
kernel and its dual. Their proved binary absolute irreducibility and
inequivalence survive genuine scalar extension, discharging the last premise
of the unconditional `smallModelsExist` theorem.

Sources: James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57--111; GM02, Proposition 5.1, manuscript p.17.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
open Sporadic.Mathieu
universe v

/-- The two native code modules and an independent degree-forty-four pair
supply the exact small-family contract. No exhaustivity input is used. -/
theorem smallModelsExist_of_fortyFour
    (h44 : SmallModels.FortyFourModelsExist.{v}) : SmallModelsExist.{v} := by
  intro F _ _ _
  obtain ⟨α, hαirr, hα⟩ := SmallModels.elevenModelsExist F
  obtain ⟨β, hβirr, hβ⟩ := h44 F
  let d : Fin 2 ⊕ Fin 2 → ℕ := fun i => match i with
    | .inl _ => 11
    | .inr _ => 44
  let ρ : ∀ i : Fin 2 ⊕ Fin 2, Representation F M24 (Fin (d i) → F) := fun i =>
    match i with
    | .inl j => α j
    | .inr j => β j
  have hirr : ∀ i, IsIrreducible (ρ i) := by
    rintro (i | i)
    · exact hαirr i
    · exact hβirr i
  have hneq : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)) := by
    intro i j hij
    constructor
    intro e
    have hdim := e.toLinearEquiv.finrank_eq
    rcases i with i | i <;> rcases j with j | j
    · exact (hα (fun h => hij (congrArg Sum.inl h))).false e
    · simp only [d, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
      omega
    · simp only [d, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
      omega
    · exact (hβ (fun h => hij (congrArg Sum.inr h))).false e
  let f : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm
  refine ⟨fun i => d (f i), fun i => ρ (f i), fun i => hirr (f i), ?_, ?_⟩
  · intro i j hij
    exact hneq (fun h => hij (f.injective h))
  · intro i
    change d (f i) = 11 ∨ d (f i) = 44
    rcases f i with j | j
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- It is enough to construct the two absolutely irreducible binary
forty-four-dimensional modules. Their scalar extension and coordinate
transport, and the entire degree-eleven pair, are discharged here. -/
theorem smallModelsExist_of_binary_fortyFour
    (h44 : SmallModels.BinaryFortyFourModelsExist) : SmallModelsExist.{v} :=
  smallModelsExist_of_fortyFour (SmallModels.fortyFourModelsExist_of_binary h44)

/-- Four actual pairwise inequivalent irreducible M24 modules, of degrees eleven
and forty-four, over every algebraically closed field of characteristic two.
The native code, cocode, exterior contraction kernel and its dual supply all
four modules; no exhaustivity or additional construction premise is needed. -/
theorem smallModelsExist : SmallModelsExist.{v} :=
  smallModelsExist_of_binary_fortyFour SmallModels.binaryFortyFourModelsExist

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum
