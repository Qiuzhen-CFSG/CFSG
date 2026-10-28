module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.UnitaryInitial
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.FullGraphObstruction

/-!
# The original unitary escaping walk

The marked PSU or SU quotient at the beta endpoint gives the two-walk
transitivity needed by the unitary initial argument.  The theorem below
transports that marking through the literal reduced-to-original quotient map,
constructs the walk in the reduced graph, and returns its center escape under
the same inclusion.  Both unitary covers remain in the disjunction.
Source: DGS85 (11.4)--(11.6), pp.171--174.
-/

public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open CommutingNontrivial NoncommutingProfile Subgroup.CosetGeometry.RankTwo Reduction
open Theory.GroupTheory RankTwoAmalgam SuzukiContainment
variable {G : Type*} [Group G] {L₀ : Fin 2 → Subgroup G} {S₀ : Subgroup G}
local notation "F₀" => Reduction.reducedFamily L₀ S₀
local notation "G₀" => Reduction.G₀ L₀ S₀

/-- Construct the original reduced-graph escaping walk from a marked unitary
beta quotient, preserving the literal inclusion into the original completion. -/
theorem original_unitary_escaping_four_walk
    (h : HypothesisF11 L₀ S₀)
    (hc : IsCriticalPair F₀ (base F₀ false) (base F₀ true))
    (hb : DGS85.b F₀ = 1)
    (hcomm : ⁅Z F₀ (base F₀ false),Z F₀ (base F₀ true)⁆ = ⊥)
    (Ma : IsRankOneModel ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype ⧸
      pCore 2 ((graphLocalGroup F₀ (base F₀ false)).map (G₀).subtype)))
    {m : ℕ} (hm : 0 < m)
    (mark : ClassicalGroup.IsPSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m) ∨
      IsSU ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F₀ (base F₀ true)).map (G₀).subtype)) 3 (2^m)) :
    ∃ c, (graph F₀).Adj (base F₀ true) c ∧ (base F₀ false) ≠ c ∧
      ∃ g ∈ stabilizer F₀ (base F₀ false), g • (base F₀ true) ≠ (base F₀ true) ∧
        ¬ (Z F₀ (base F₀ true)).map (G₀).subtype ≤
          (Q F₀ (g • (base F₀ true))).map (G₀).subtype ∧
        ∃ p : BasedWalk (graph F₀) 4 (g • c), p.Nonbacktracking ∧
          p.vertices = [g • c,g • (base F₀ true),base F₀ false,base F₀ true,c] := by
  let d := reducedFullEarlierLocalTheorems h
  let ea := (d.localGroup (base F₀ false)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqa := QuotientGroup.congr _ _ ea (pCore_map_iso 2 ea)
  let eb := (d.localGroup (base F₀ true)).equivMapOfInjective
    (G₀).subtype (G₀).subtype_injective
  let eqb := QuotientGroup.congr _ _ eb (pCore_map_iso 2 eb)
  have ma : IsRankOneModel (d.localGroup (base F₀ false) ⧸
      pCore 2 (d.localGroup (base F₀ false))) := by
    exact Ma.of_equiv eqa
  have mark' : ClassicalGroup.IsPSU (d.localGroup (base F₀ true) ⧸
      pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) ∨
      IsSU (d.localGroup (base F₀ true) ⧸
        pCore 2 (d.localGroup (base F₀ true))) 3 (2^m) := by
    rcases mark with hh | ⟨E,_,_,J,hcard,hconj,⟨e⟩⟩
    · exact Or.inl (hh.of_mulEquiv eqb)
    · exact Or.inr ⟨E,inferInstance,inferInstance,J,hcard,hconj,⟨eqb.trans e⟩⟩
  obtain ⟨c,hbc,hac,g,hga,hgb,hesc,p,hp,hpv⟩ := source_unitary_beta_escaping_four_walk
    (P := fun i => (P₀ L₀ S₀ i).subgroupOf G₀) (B := (B₀ L₀ S₀).subgroupOf G₀)
    (a := base F₀ false) (b := base F₀ true)
    (reduced_triple h) (reduced_borel_core_sylow h) (reduced_vertex_sylow h)
    d hc hb hcomm ma hm mark'
  exact ⟨c,hbc,hac,g,hga,hgb,
    fun hh => hesc ((map_le_map_iff_of_injective (G₀).subtype_injective).mp hh),p,hp,hpv⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
