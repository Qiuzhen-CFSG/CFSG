module
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionThree.LocalFamilyGeneratingExtraction
/-!
# Generation with a Sylow subgroup of a full graph edge

If a subgroup together with a full edge stabilizer generates one endpoint
stabilizer, the same subgroup together with any supplied Sylow two-subgroup
of that edge also generates it. The full edge need not itself be a two-group.

The full edge is proper in its endpoint: containment of one adjacent
stabilizer in the other would make the latter the ambient group, contrary
to its nontrivial two-core and the ambient trivial two-core. The local
P-family property gives a unique maximal overgroup of the edge Sylow.
If the smaller generated subgroup were proper, it and the full edge would
both lie there, contradicting the supplied generation.

This is the unique-maximality reduction used in Stellmacher (8.4)(7)--(8),
Journal of Algebra 190 (1997), p.39, for the actual Section Seven graph.
-/

namespace Stellmacher.SectionsFiveToSeven
open CosetGraphContext SevenSix
universe u

public theorem edge_sylow_generation
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2) (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hdl : Γ.adjacent d l) (R : Subgroup G)
    (hgen : R ⊔ (stabilizer Γ d ⊓ stabilizer Γ l) = stabilizer Γ d)
    (T : Sylow 2 ↥(stabilizer Γ d ⊓ stabilizer Γ l)) :
    R ⊔ sylowTwoAmbient (stabilizer Γ d ⊓ stabilizer Γ l) T = stabilizer Γ d := by
  let P := stabilizer Γ d
  let L := stabilizer Γ l
  let D := P ⊓ L
  let W := sylowTwoAmbient D T
  have hl := (mem_neighborhood_iff_adjacent Γ).mpr hdl
  have hd := edge_sectionThree_data h Γ hl T
  have hP : P ∈ SectionThree.PSet (⊤ : Subgroup G) W := hd.2.1
  have hL : L ∈ SectionThree.PSet (⊤ : Subgroup G) W := hd.2.2.1
  have hjoin : P ⊔ L = ⊤ := hd.2.2.2.2.1
  have hWD : W ≤ D := Subgroup.map_subtype_le _
  have hDproper : D ≠ P := by
    intro he
    have hPL : P ≤ L := he ▸ (inf_le_right : D ≤ L)
    have hLtop : L = ⊤ := by rwa [sup_eq_right.mpr hPL] at hjoin
    let Q := q Γ l
    have hQne : Q ≠ ⊥ := by
      rw [show Q = twoCoreAmbient L from Γ.twoCoreAt_def l]
      exact hL.1.2.2.1
    have hQp : IsPGroup 2 Q := by
      rw [show Q = twoCoreAmbient L from Γ.twoCoreAt_def l]
      exact (pCore_isPGroup (p := 2) (G := L)).map L.subtype
    have hQn : Q.Normal := by
      apply Subgroup.normalizer_eq_top_iff.mp
      apply top_unique
      rw [← hLtop]
      exact stabilizer_le_normalizer_q Γ l
    have hQle : Q ≤ pCore 2 G := le_sSup ⟨hQn,hQp⟩
    exact hQne (bot_unique (hQle.trans_eq h.twoCore_eq_bot))
  have hRP : R ≤ P := le_sup_left.trans_eq hgen
  by_contra hproper
  obtain ⟨M,hM,hWM,huniq⟩ := hP.2
  have hRWM : R ⊔ W ≤ M.map P.subtype := SectionThree.le_unique_maximal_over huniq
    le_sup_right (sup_le hRP (hWD.trans inf_le_left)) hproper
  have hDM : D ≤ M.map P.subtype := SectionThree.le_unique_maximal_over huniq
    hWD inf_le_left hDproper
  have hPM : P ≤ M.map P.subtype := hgen.ge.trans (sup_le (le_sup_left.trans hRWM) hDM)
  apply hM.ne_top
  apply Subgroup.map_injective P.subtype_injective
  rw [← MonoidHom.range_eq_map,Subgroup.range_subtype]
  exact le_antisymm (Subgroup.map_subtype_le _) hPM
end Stellmacher.SectionsFiveToSeven
