module
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.OddTransversal
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.LocalTransitivity

/-!
# Odd neighbor transport from the original starred model

The original starred factor is transitive on Borel cosets. Its intrinsic
two-core quotient has odd representatives for every Sylow-normalizer coset.
Lifting one of these representatives gives an odd-order element of that
same starred factor carrying the base neighbor to any chosen neighbor.
The quotient preimage is exactly the original full Borel intersection.
No identification of the enlarged actor is used; degree-one unitary and
strict D10-to-Sz(2) cases are therefore retained.

Source: DGS, Groups and Graphs (1985), 6.5, printed p.122.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterF.Source.DGS85
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Odd transport in the literal starred endpoint, for every original model. -/
theorem source_star_odd_neighbor_transport (h : LocallyRankOneTriple P B)
    (j : Bool) (d : LocalRankOneData (family P j) B)
    {w : Vertex (family P)} (hw : (graph (family P)).Adj (base (family P) j) w) :
    ∃ x ∈ d.Pstar, Odd (orderOf x) ∧ x • base (family P) (!j) = w := by
  let := d.finite_P
  let : Finite d.Pstar := Finite.of_injective (inclusion d.Pstar_le) (inclusion_injective _)
  obtain ⟨g,hg,hgw⟩ := neighbor_transitive_of_borel_cover h j d.Pstar
    ((normal_subgroupOf_iff_le_normalizer d.Pstar_le).mp d.normal) d.supplement w hw
  let q := QuotientGroup.mk' (pCore 2 d.Pstar)
  obtain ⟨x,hx,hgx⟩ := q.exists_odd_coset_of_comap (QuotientGroup.mk'_surjective _)
    (normalizer (d.sylow : Set d.Pstar))
    (normalizer (quotientSylow d.sylow : Set (d.Pstar ⧸ pCore 2 d.Pstar)))
    (quotientSylow_normalizer_comap d.sylow)
    (d.quotient.odd_sylow_normalizer_transversal (quotientSylow d.sylow)) ⟨g,hg⟩
  have hBmem : g⁻¹*(x : G) ∈ B := by
    rw [←source_star_borel d] at hgx
    exact hgx
  have hBP : B ≤ family P (!j) := by
    rw [←h.intersection]
    cases j
    · exact inf_le_right
    · exact inf_le_left
  have hf : (g⁻¹*(x : G)) • base (family P) (!j) = base (family P) (!j) := by
    change g⁻¹*(x : G) ∈ MulAction.stabilizer G (base (family P) (!j))
    rw [Subgroup.CosetGeometry.stabilizer_base]
    exact hBP hBmem
  refine ⟨x,x.property,?_,?_⟩
  · rwa [Subgroup.orderOf_coe]
  · have hh := congrArg (g • ·) hf
    simpa only [mul_smul,smul_inv_smul,hgw] using hh

/-- The source 6.5 transporter lies in the actual opposite full endpoint. -/
theorem source_rankOne_odd_neighbor_transport (h : LocallyRankOneTriple P B)
    (j : Bool) {w : Vertex (family P)}
    (hw : (graph (family P)).Adj (base (family P) j) w) :
    ∃ x ∈ family P j, Odd (orderOf x) ∧ x • base (family P) (!j) = w := by
  have hd : Nonempty (LocalRankOneData (family P j) B) := by
    cases j
    · exact h.local_data 0
    · exact h.local_data 1
  let d := Classical.choice hd
  obtain ⟨x,hx,ho,hw⟩ := source_star_odd_neighbor_transport h j d hw
  exact ⟨x,d.Pstar_le hx,ho,hw⟩
end CFSG.Quasithin.ChapterF.Source.DGS85
