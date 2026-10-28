module
public import CFSG.Quasithin.ChapterG.Section11.StrictWholePair
public import CFSG.Quasithin.ChapterG.Section11.WholePairExclusion

/-!
# The original strict intersection is impossible

Construct the crossing cubic from Hypothesis611 and Conclusion6127.
The original local analysis yields the literal quotient action with its
commutator form and type-a2 rank-two element. All single whole components
are excluded, and the remaining natural tensor pair contradicts type-a2.
This closes the original strict source using its stated LocalAnalysis;
there is no additional classification, model, or whole-component premise.

The earlier local-analysis producer remains with the Chapter12 recognition
assembly. The original thirteen-row conclusion and its separately named
exceptional correction are preserved.
Source: Aschbacher--Smith 6.2.15--19, printed pp.688--691,
and G.11.7, printed pp.366--368.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The original strict source is impossible. The crossing cubic, literal
marked quotient and all whole-component exclusions are constructed here. -/
theorem LocalAnalysis.false_of_local_analysis_of_strict_intersection
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) : False := by
  obtain ⟨d,hdres,_,hdS,_,hd3,hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  obtain ⟨he,hX,B,v,h,_,_,_,ha,_,_,_,K,_,_,_,h9,hne,_⟩ :=
    A.strict_whole_component_pair h611 hnatural hz horder hTH hstrict hdres hdH hdS hd3
  let := he
  let := hX
  obtain ⟨a,_,_,ha2,_,hr,_,htype,_⟩ := ha
  exact ChapterG.Section11.WholePairExclusion.false_of_component_pair h h9 hne a ha2 hr htype

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
