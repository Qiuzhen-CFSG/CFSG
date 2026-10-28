module

public import CFSG.KnownSimple.CarrierCatalogue
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Carrier
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BinaryAction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BinaryCorank
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Binary
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BorelPlacement
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification

/-!
# The symplectic component alternatives in E.6.8(2)

Both symplectic constructors of Theorem C give the literal derived matrix
model. The marked Sylow normalizer lies in L ∩ M by `BorelPlacement`, using
the universal E.6.7 source input. The diagram-preserving automorphism theorem
discharges the semilinear coverage needed for the nonbinary action calculation.
The binary and nonbinary calculations then give the corank bound, displacement
decomposition when n > 1, and the complete Borel/maximal-parabolic split.

The Borel case retains its strict intermediate subgroup and escaping
centralizer, or the actual A₆ identification. The parabolic case retains the
literal matrix root action. At parameter one its carrier is Sp₄(2)′ and the
acting roots are in the full Sp₄(2). Only the permitted earlier local facts
and universal E.6.7 statement remain explicit in `exists_alternative`; no
tailored action or placement premise, or downstream E.6.11 result, is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(2),
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Both source constructors supply the actual derived model and the common
positive upper and lower action bounds. This does not assert the alternatives. -/
theorem component_model_and_bounds (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSp L 2 (2 ^ n)) ∨
      Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    ∃ n, SymplecticDerivedModel L n ∧ 0 < actionCorank V L ∧
      actionCorank V L ≤ subgroupCorank V U := by
  obtain ⟨n, hn⟩ := exists_model hm
  exact ⟨n, hn, fixedSpace_corank_pos h (component_not_le h earlier hU hL),
    fixedSpace_corank_le hU.1 hL.1⟩

/-- The specified component Sylow lies in the actual local intersection;
its image is still the source L ∩ C_T(V). -/
theorem component_intersection_sylow (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ∃ S : Sylow 2 L,
      (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V ∧
      (S : Subgroup L).map L.subtype ≤ L ⊓ M := by
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  refine ⟨S, hS, ?_⟩
  rw [hS]
  exact le_inf inf_le_left (inf_le_right.trans (inf_le_left.trans h.sylow_le))

/-- The intrinsic automorphism classification discharges the universal
semilinearity premise of the nonbinary component calculation. -/
theorem diagram_semilinear_coverage : Nonbinary.DiagramSemilinearCoverage := by
  intro F _ _ _ a ha
  exact
    Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
      a ha

/-- Every clause of E.6.8(2) for an actual derived symplectic model. The only
additional source input is the full universal E.6.7 statement. -/
theorem alternative_of_model
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hm : SymplecticDerivedModel L n) :
    SymplecticAlternative M V U L n := by
  have hB := BorelPlacement.exists_borel h h67 hU hL hm
  by_cases hn : n = 1
  · subst n
    exact binary_alternative h earlier hU hL hm hB
  · exact Nonbinary.alternative diagram_semilinear_coverage h earlier hU hL
      (lt_of_le_of_ne hm.1 (Ne.symm hn)) hm hB

/-- The nonbinary projective constructor of Theorem C yields E.6.8(2) at
the same field exponent, including its decomposition and local action clauses. -/
theorem projective_alternative
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp L 2 (2 ^ n)) :
    SymplecticAlternative M V U L n :=
  alternative_of_model h earlier h67 hU hL (model_of_projective hn hm)

/-- The derived binary constructor of Theorem C yields the exact parameter-one
alternative. Its Sylow subgroup is self-normalizing, so E.6.7 is unnecessary. -/
theorem projective_derived_alternative
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    SymplecticAlternative M V U L 1 := by
  have hmodel := model_of_projective_derived hm
  exact binary_alternative h earlier hU hL hmodel
    (BorelPlacement.exists_borel_of_model_one h hU hL hmodel)

/-- Both symplectic constructors of Theorem C supply the complete symplectic
alternative for the component sieve, with the full known-simple catalogue. -/
theorem exists_alternative
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSp L 2 (2 ^ n)) ∨
      Nonempty (L ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    ∃ n, SymplecticAlternative M V U L n := by
  rcases hm with ⟨n, hn, hm⟩ | hm
  · exact ⟨n, projective_alternative h earlier h67 hU hL hn hm⟩
  · exact ⟨1, projective_derived_alternative h earlier hU hL hm⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic
