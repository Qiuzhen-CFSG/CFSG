module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ResidualRigidity

/-!
# The marked PSL₃ Borel placement in E.6.8

For ordinary PSL₃(2ⁿ), n ≥ 1, and every two-group central cover of PSL₃(4),
the actual intersection L ∩ M is the normalizer in L of the Sylow subgroup
marked by L ∩ C_T(V). The ordinary branch also supplies its trivial center's
two-group property. Trivial covering centers are included throughout.

The full universally quantified E.6.7 input gives Borel containment through
`Containment`. In the central quotient, any strict overgroup of this Borel
has trivial pointwise automorphism fixer on its embedded O^{2′} residual.
But the actual component action gives a nontrivial such fixer: the obstruction
condition centralizes O^{2′}(L ∩ M), and perfectness preserves the nontrivial
V-action through the central quotient. Transport along the actual PSL₃ model
therefore forces equality. Taking full preimages gives the marked equality
upstairs, and `component_sylow_action` supplies the required Sylow witness.

Only the genuine earlier local facts and complete E.6.7 source statement
remain explicit inputs. All containment and intrinsic residual-fixer premises
are discharged here; the parent owns the remaining E.6.8 action clauses.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem intersection_eq_markedBorel_of_containment
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : 1 ≤ n) (hz : IsPGroup 2 (center L))
    (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ n))
    (hB : markedBorel L S ≤ M) : L ⊓ M = markedBorel L S := by
  apply (quotientIntersection_eq_normalizer_iff h S hS hz).mp
  have hBJ := (quotient_normalizer_le_intersection_iff h S hS hz).mpr hB
  by_contra hne
  have hlt := lt_of_le_of_ne hBJ (Ne.symm hne)
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  let R := (quotientSylow S).mapSurjective (f := e.toMonoidHom) e.surjective
  have hltm : normalizer (R : Set PSL(3, F)) <
      (quotientIntersection L M).map e.toMonoidHom := by
    change normalizer (((quotientSylow S : Subgroup (L ⧸ center L)).map
      e.toMonoidHom) : Set PSL(3, F)) < _
    rw [← (quotientSylow S).normalizer_map_surjective e.toMonoidHom e.surjective]
    exact (map_lt_map_iff_of_injective e.injective).mpr hlt
  have hfix := Matrix.PSL3.LinearThree.ResidualRigidity.residual_fixer_eq_bot
    hn hF R ((quotientIntersection L M).map e.toMonoidHom) hltm
  have he := MulAut.map_fixingSubgroup_congr e
    ((primeToResidual 2 (quotientIntersection L M)).map (quotientIntersection L M).subtype)
  rw [map_embedded_primeToResidual, hfix] at he
  apply residual_fixer_ne_bot h earlier hU hL
  apply map_injective (f := (MulAut.congr e).toMonoidHom) (MulAut.congr e).injective
  simpa only [Subgroup.map_bot] using he

/-- The marked Borel is exactly the component intersection in the ordinary branch. -/
theorem ordinary_intersection_eq_markedBorel
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    L ⊓ M = markedBorel L S :=
  intersection_eq_markedBorel_of_containment h earlier hU hL S hS hn
    (ordinary_center_isTwoGroup iso) (ordinary_quotient_model iso)
    (Containment.ordinary_markedBorel_le h67 hU hL S hS hn iso)

/-- The marked equality for every allowed two-group central cover of PSL₃(4),
including the trivial covering center. -/
theorem cover_intersection_eq_markedBorel
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hz : IsPGroup 2 (center L)) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    L ⊓ M = markedBorel L S :=
  intersection_eq_markedBorel_of_containment h earlier hU hL S hS (n := 2)
    (by decide) hz iso (Containment.cover_markedBorel_le h67 hU hL S hS hz iso)

/-- The ordinary PSL₃(2ⁿ) branch supplies the center hypothesis and a Sylow
subgroup marked by the actual centralizer intersection. -/
theorem ordinary_placement
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    IsPGroup 2 (center L) ∧ ∃ S : Sylow 2 L,
      (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V ∧
        L ⊓ M = markedBorel L S := by
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hU hL rfl
  exact ⟨ordinary_center_isTwoGroup iso, S, hS,
    ordinary_intersection_eq_markedBorel h earlier h67 hU hL S hS hn iso⟩

/-- Every two-group central cover of PSL₃(4) has the required marked Borel
placement. No nontriviality is required of its center. -/
theorem cover_placement
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (hz : IsPGroup 2 (center L)) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    ∃ S : Sylow 2 L,
      (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V ∧
        L ⊓ M = markedBorel L S := by
  obtain ⟨_, S, hS, _⟩ := component_sylow_action h hU hL rfl
  exact ⟨S, hS, cover_intersection_eq_markedBorel h earlier h67 hU hL S hS hz iso⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement
