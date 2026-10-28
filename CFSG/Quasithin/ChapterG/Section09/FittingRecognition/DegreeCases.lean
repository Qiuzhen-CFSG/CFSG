module

public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Preparation
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Plane
public import Theory.Representation.SubrepresentationLattice

/-!
# The remaining degree branches in G.9.4

Once the cubic Fitting reduction supplies even degree and actor rank at
most two, positivity and the G.9.1 bound leave four pairs. The plane theorem
excludes degree two at actor rank two using the actual action. This separates
the numerical reduction from the independent GL₄ and GL₆ normalizer proofs.

Source: Aschbacher--Smith, proof of G.9.4, printed p.355.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

universe u v

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

/-- The literal rank/degree pairs needed by the three remaining recognition branches. -/
theorem ThreeCoreData.degree_cases (data : ThreeCoreData ρ A m)
    (h : Setup ρ A m) [Representation.IsIrreducible ρ] (hm : 0 < m) :
    (m = 1 ∧ Module.finrank (ZMod 2) V = 2) ∨
    (m = 1 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 6) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hpos := Module.finrank_pos (R := ZMod 2) (M := V)
  have hbound := h.degree_le
  have hrank := data.actor_rank_le
  obtain ⟨n, hn⟩ := data.even_degree
  have hplane : Module.finrank (ZMod 2) V = 2 → m = 1 :=
    fun hd => (plane_rank_and_card h hm hd).1
  by_cases hd : Module.finrank (ZMod 2) V = 2
  · exact Or.inl ⟨hplane hd, hd⟩
  · omega

/-- The first recognized alternative is already discharged in the cubic
branch. Only the degree-four and degree-six branches remain here. -/
theorem caseOne_or_remaining_degrees {K : GroupClass.{u}}
    (h : FittingHypothesis K ρ A m) (hm : 0 < m) (data : ThreeCoreData ρ A m) :
    CaseOne ρ m ∨
    (m = 1 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 4) ∨
    (m = 2 ∧ Module.finrank (ZMod 2) V = 6) := by
  let : Representation.IsIrreducible ρ := h.irreducible
  rcases data.degree_cases h.toSetup hm with htwo | hfour
  · exact Or.inl (caseOne_of_degree_two h hm htwo.2)
  · exact Or.inr hfour

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
