module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.JankoRecognition.J3Ambient.SourceSixteenCompletion
public import Theory.SpecificGroups.Janko3.SourceRecognition.Seventeen.Model.CubicNormalizer

/-!
# The actual completion meets the cubic normalizer in the pair subgroup

Marked completion recognition carries the literal original cubic into the
actual point-pair overlap of PSL₂(16):2. Its normalizer preserves the two
projective fixed points, so the whole intersection is the original pair
subgroup. Both ambient normalizers and the cubic retain the same field
embedding, with no intersection or model-map premise.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen Janko23.J3Recognition.Ambient
open Janko23.J3Recognition.Ambient.Seventeen
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition
open Sporadic.Janko3.SourceRecognition.BaumeisterParabolics

/-- The literal G₁–G₃ intersection in the original rank-three amalgam. -/
theorem literal_completion_cubic_normalizer_intersection
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (hc : Janko23.OneInvolutionClass G)
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (a : A ≃* Plane) (j : SingerField.Model →* G)
    (hj : PlaneTransport.FieldEmbedding A C a j) :
    completion j.range (overlap j) ⊓ normalizer (zpowers (j cubic) : Set G) =
      normalizer (overlap j : Set G) := by
  let L := completion j.range (overlap j)
  let s := j cubic
  have hsO : s ∈ overlap j := mem_map_of_mem j cubic_mem
  have hsJ : s ∈ j.range := overlap_le j hsO
  have hsN : s ∈ normalizer (overlap j : Set G) := (overlap j).le_normalizer hsO
  have hsL : s ∈ L := (show j.range ≤ L from le_sup_left) hsJ
  let sL : L := ⟨s,hsL⟩
  let mark := Janko23.J3Recognition.Ambient.BaumeisterParabolics.original_marking_of_pair_triangle
    j hj.1 (literal_overlap_pair_equiv P hc A C a j hj).some
    (literal_triangle_equiv P hc A C a j hj).some
  obtain ⟨e,hpoint,hpair,_htri,_hf⟩ := mark.recognition
  have hsm : e sL ∈ Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.point ⊓
      Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.pair := by
    constructor
    · rw [←hpoint]
      exact mem_map_of_mem e.toMonoidHom hsJ
    · rw [←hpair]
      exact mem_map_of_mem e.toMonoidHom hsN
  have hso : orderOf (e sL) = 3 :=
    (e.orderOf_eq sL).trans ((orderOf_coe sL).symm.trans
      ((orderOf_injective j hj.1 _).trans cubic_order))
  have hlineL : zpowers s ≤ L := zpowers_le.mpr hsL
  have hline : zpowers sL = (zpowers s).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [MonoidHom.map_zpowers,map_subgroupOf_eq_of_le hlineL]
    rfl
  apply le_antisymm
  · intro g hg
    let gL : L := ⟨g,hg.1⟩
    have hgn : gL ∈ normalizer (zpowers sL : Set L) := by
      rw [hline,←subgroupOf_normalizer_eq hlineL]
      exact hg.2
    have hem : e gL ∈ normalizer (zpowers (e sL) : Set _) := by
      have hh := le_normalizer_map (H := zpowers sL) e.toMonoidHom
        (mem_map_of_mem e.toMonoidHom hgn)
      rwa [MonoidHom.map_zpowers] at hh
    have hepair := Sporadic.Janko3.SourceRecognition.Seventeen.ModelAmalgam.overlap_cubic_normalizer_le_pair hso hsm hem
    rw [←hpair,mem_map_equiv] at hepair
    have hback : gL ∈ (second (overlap j)).subgroupOf L := by
      simpa only [e.symm_apply_apply] using hepair
    exact hback
  · exact le_inf le_sup_right (overlap_normalizer_le_cubic j hj.1)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
