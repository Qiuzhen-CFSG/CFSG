module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.LinearBlockSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SymmetricBlockSource
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveBlock
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.CompleteSource
/-!
# The complete original Baumann-characteristic block source

The original reduced action is classified with the complete known-simple
catalogue. The linear branches use the proved C.1.29 inside the residual
Baumann join; the symmetric-five branches use the same selected original
component and full canonical pair. No action marking, block, characteristic
control or earlier classification premise remains. The general theorem
retains all three χ₀ types of C.1.12. On nonsolvable groups it gives exactly
the L2-even or A5 alternatives, with the original generation and Thompson
commutator. Existing block definitions are unchanged.

Source: Aschbacher–Smith E.2.3(4), with C.1.12, C.1.24 and C.1.29,
printed pp.124,130–134,217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterC Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem outside_maximal_of_sup_sylow
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (L : Subgroup G) (hgen : L ⊔ (T : Subgroup G) = ⊤) :
    ¬L ≤ minimalParabolicMax T hP := by
  intro hL
  exact (minimalParabolicMax_spec T hP).1.ne_top
    (top_unique (hgen ▸ sup_le hL (minimalParabolicMax_spec T hP).2))

/-- The original hypotheses produce a genuine χ₀ block; the characteristic
subgroups quantified here belong to Baum(T), exactly as in the source. -/
theorem source_chiZero_block
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : generalizedFitting G = pCore 2 G)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hno : ∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
      (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥) :
    ∃ L : Subgroup G, IsChiZeroBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧ ¬L ≤ minimalParabolicMax T hP := by
  classical
  let := hU.normal
  let := hU.elementary
  let C := centralizer (U : Set G)
  let q := QuotientGroup.mk' C
  have hq := QuotientGroup.mk'_surjective C
  have hk : q.ker = centralizer (U : Set G) := QuotientGroup.ker_mk' C
  let α := NormalElementaryQuotient.representation U q hq hk
  have h36 : A36Input.{u} KnownSimple.IsKnownSimple :=
    ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  by_cases hs : Group.IsSolvable G
  · let := hs
    exact LinearBlockSource.chiZero_block_of_solvable_action hG T hP hf U hU hJ inferInstance hno
  rcases source_nonsolvable_natural_factors hG T hP U hU hs hJ with
    ⟨hqs,c,hlin|hfive⟩ | ⟨d,_,_⟩
  · obtain ⟨F,hF⟩ := hlin
    exact LinearBlockSource.chiZero_block_of_baumann_sylow hG T hP hf hno
      (quasisimple_linear_baumann_of_section T hP U hU hJ q hq hk hqs c.sectionData F hF).1
  · obtain ⟨e⟩ := hfive
    obtain ⟨hb,ha,hm,_,_⟩ := quasisimple_five_block_of_no_characteristic_baumann
      h36 hG T hP U hU hJ q hq hk hqs c.sectionData e hf hno
    exact ⟨pResidual 2 G,⟨hb,Or.inr (Or.inr ha)⟩,hm,pResidual_sup_sylow_eq_top T,
      outside_maximal_of_sup_sylow T hP _ (pResidual_sup_sylow_eq_top T)⟩
  · let := offenderSubgroup_normal α
    rcases pair_baumann_or_symmetric_five T hP U hU hJ q hq hk d with hlin | hfive
    · exact LinearBlockSource.chiZero_block_of_baumann_sylow hG T hP hf hno hlin.1
    obtain ⟨t,ht₁,ht₂,⟨c⟩⟩ := hfive
    obtain ⟨L,hb,ha,hm,_,_,hgen⟩ := paired_five_block_of_no_characteristic_baumann
      h36 hG T hP U hU hJ q hq hk hs hf d c ⟨t,ht₁,ht₂⟩ hno
    exact ⟨L,⟨hb,Or.inr (Or.inr ha)⟩,hm,hgen,outside_maximal_of_sup_sylow T hP L hgen⟩

/-- The strict L2-even/A5 conclusion on the original nonsolvable domain. -/
theorem source_nonsolvable_block
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (hf : generalizedFitting G = pCore 2 G) (hs : ¬Group.IsSolvable G)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hno : ∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
      (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥) :
    ∃ L : Subgroup G, IsBlock L ∧ ((∃ n, IsL2EvenBlock L n) ∨ IsAlternatingBlock L 5) ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      L ⊔ (T : Subgroup G) = ⊤ ∧ ¬L ≤ minimalParabolicMax T hP := by
  obtain ⟨L,hL,hm,hgen,hout⟩ := source_chiZero_block hG T hP hf U hU hJ hno
  refine ⟨L,hL.1,?_,hm,hgen,hout⟩
  rcases hL.2 with hl | h3 | h5
  · exact Or.inl hl
  · exact (LinearBlockSource.not_alternatingThree_of_nonsolvable_generation hs L hL.1 T hgen h3).elim
  · exact Or.inr h5
end CFSG.Quasithin.ChapterE.ThompsonAction
