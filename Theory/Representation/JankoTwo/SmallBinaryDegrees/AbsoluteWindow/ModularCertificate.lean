module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.Models
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.ClassBound
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.Contracts
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.DegreeCompleteness.Inputs
public import Theory.Representation.PSL3Three.AbsoluteDegrees.Saturation

/-!
# Saturation assembly for the characteristic-two Hall--Janko certificate

The four small and five larger candidate modules, together with the trivial
module, form ten pairwise inequivalent simple actions. The checked class-count
reduction and modular trace independence then exhaust all simple modules.
The separate `ModularCertificate.Application` applies scalar extension and the
faithful lower-degree obstruction to obtain `DegreeWindow`.

The model constructions and exhaustive representative coverage are still
explicit inputs. This module proves their consumer applications, not the
unconditional modular catalogue. The final assembly must discharge both
`SmallModelsExist` and `LargeModelsExist`, as well as `RepresentativeCoverage`.

Sources: ATLAS characteristic-two J2 matrix candidates listed in `Models`;
Hiss--Malle corrected Table 2; Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.16. Completeness uses the proved modular trace
bound, not those tables or Table 6.7's offender hypothesis.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
open Sporadic.LeechRelated.J2
open PowerFusionCertificate
universe v

private theorem small_bounds (i : Fin 4) : 6 ≤ smallDegree i ∧ smallDegree i ≤ 14 := by
  revert i
  decide

private theorem large_lower (i : Fin 5) : 36 ≤ largeDegree i := by
  revert i
  decide

private theorem small_values (i : Fin 4) : smallDegree i = 6 ∨ smallDegree i = 14 := by
  revert i
  decide

private abbrev CandidateIndex := Option (Fin 4 ⊕ Fin 5)

/-- Saturation by actual simple actions proves the closed-field spectrum.
Inequivalence between the trivial, small and large families follows from their
integer dimensions; only within-family inequivalence is an input. -/
theorem closedSpectrum_of_models (hcover : RepresentativeCoverage)
    (hsmall : SmallModelsExist.{v}) (hlarge : LargeModelsExist.{v}) :
    ClosedSmallDegreeSpectrum.{v} := by
  intro F _ _ _ U _ _ _ τ _ hd
  classical
  obtain ⟨ρs, hsirr, hsne⟩ := hsmall F
  obtain ⟨ρl, hlirr, hlne⟩ := hlarge F
  let V : CandidateIndex → Type v := fun i => match i with
    | none => F
    | some (.inl j) => Fin (smallDegree j) → F
    | some (.inr j) => Fin (largeDegree j) → F
  let addV : ∀ i, AddCommGroup (V i) := fun i => by
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  let modV : ∀ i, Module F (V i) := fun i => by
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  let rep : ∀ i, Representation F Carrier (V i) := fun i => match i with
    | none => Representation.trivial F Carrier F
    | some (.inl j) => ρs j
    | some (.inr j) => ρl j
  have finV : ∀ i, FiniteDimensional F (V i) := by
    intro i
    rcases i with _ | (i | i) <;> dsimp [V] <;> infer_instance
  have irr : ∀ i, IsIrreducible (rep i) := by
    intro i
    rcases i with _ | (i | i)
    · change IsIrreducible (Representation.trivial F Carrier F)
      constructor
      intro S
      rcases IsSimpleOrder.eq_bot_or_eq_top S.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
    · exact hsirr i
    · exact hlirr i
  have hdistinct : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)) := by
    intro i j hij
    constructor
    intro e
    have he := e.toLinearEquiv.finrank_eq
    rcases i with _ | (i | i) <;> rcases j with _ | (j | j)
    all_goals simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at he
    · exact hij rfl
    · have := small_bounds j; omega
    · have := large_lower j; omega
    · have := small_bounds i; omega
    · exact (hsne (fun h => hij (by rw [h]))).false e
    · have := small_bounds i
      have := large_lower j
      omega
    · have := large_lower i; omega
    · have := large_lower i
      have := small_bounds j
      omega
    · exact (hlne (fun h => hij (by rw [h]))).false e
  have hc : Nat.card CandidateIndex = 10 := by
    simp [CandidateIndex, Nat.card_eq_fintype_card]
  obtain ⟨i, ⟨e⟩⟩ := exists_equiv_of_pRegular_class_bound V rep 2 hdistinct
    (hc ▸ odd_class_bound hcover) τ
  have he := e.toLinearEquiv.finrank_eq
  rcases i with _ | (i | i)
  all_goals simp only [V, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at he
  · exact Or.inl he
  · rcases small_values i with h | h
    · exact Or.inr (Or.inl (he.trans h))
    · exact Or.inr (Or.inr (he.trans h))
  · have := large_lower i
    omega

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate
