module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.SourceComponent.PermutationRows
public import Theory.SpecificGroups.SymplecticFour.QuinticParabolic

/-!
# Excluding the nonbinary symplectic star component

The original first factor preserves the marked star intersection and its
image is solvable. In the symplectic row that same intersection is a full
parabolic over an odd-degree binary field. Its normalization of the actor
contradicts the intrinsic parabolic quotient calculation. This removes the
symplectic row from the complete six-clause B.5.1 conclusion.

The linear-three and G₂ comparisons, exchanged module geometry, original
index premise and final p=3 assembly remain with qt-e-14615-quintic-exclusion.
Earlier 14.6.12--14 discharge remains with qt-e-suitable-odd-normalizer.
Source: Aschbacher--Smith 14.6.15, printed p.1035. No ordinary-centralizer
residual identity is used.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion ComponentExtraction ComponentExclusion.ContainedComparison
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open ChapterC.C27Source ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (j : SourceEscapingComponent Mc (residualClosure H Mc) d.K1 d.K2 (Mc.pCoreIn 2))

/-- The original first factor preserves the same marked star intersection
that normalizes its action. -/
theorem source_first_preserves_star_marking
    (k : d.K1) :
    ((starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf
      (starImage j.J (Mc.pCoreIn 2) j.J)).map
      (starComponentAction j.J (Mc.pCoreIn 2)
        (inclusion (source_first_le_common_normalizer s d j) k)).toMonoidHom =
      (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf
        (starImage j.J (Mc.pCoreIn 2) j.J) := by
  let l := inclusion (source_first_le_common_normalizer s d j) k
  have hKN : (k : G) ∈ normalizer (d.K2 : Set G) :=
    closure_le_secondNormalizer s d ((d.join_eq ▸ le_sup_left) k.property)
  have hB : (k : G) ∈ normalizer
      (((Mc ⊓ normalizer (d.K2 : Set G)) ⊓ j.J : Subgroup G) : Set G) := by
    apply inf_normalizer_le_normalizer_inf
    refine ⟨?_,l.property.1⟩
    apply inf_normalizer_le_normalizer_inf
    exact ⟨Mc.le_normalizer (d.first_le k.property),
      (normalizer (d.K2 : Set G)).le_normalizer hKN⟩
  exact starComponentAction_image j.J (Mc.pCoreIn 2)
    ((Mc ⊓ normalizer (d.K2 : Set G)) ⊓ j.J) (starM_le _ _ _) l hB

/-- The marked nonbinary symplectic row is impossible under the original
first-factor action and intersection normalization. -/
theorem source_no_nonbinary_symplectic_star (F : ChapterB.QuasisimpleSource.BinaryField)
    (hl : 1 < F.degree)
    (e : starImage j.J (Mc.pCoreIn 2) j.J ≃* Matrix.symplecticGroup (Fin 2) F.Carrier) :
    False := by
  let C := starImage j.J (Mc.pCoreIn 2) j.J
  let P := (starM j.J (Mc.pCoreIn 2) (Mc ⊓ normalizer (d.K2 : Set G))).subgroupOf C
  let f := (starComponentAction j.J (Mc.pCoreIn 2)).comp
    (inclusion (source_first_le_common_normalizer s d j))
  let : Group.IsSolvable d.K1 := source_first_factor_solvable s d
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hi := source_component_input s d j
  obtain ⟨ho,g,hg⟩ := source_component_symplectic_marked_parabolic s d j F hl e
  let t := e.trans (MulAut.conj g)
  have ht : P.map t.toMonoidHom = Theory.SpecificGroups.SymplecticFour.pointParabolic ∨
      P.map t.toMonoidHom = Theory.SpecificGroups.SymplecticFour.planeParabolic := by
    change P.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _ ∨
      P.map ((MulAut.conj g).toMonoidHom.comp e.toMonoidHom) = _
    simpa only [map_map] using hg
  have hfix : ∀ b ∈ f.range, P.map b.toMonoidHom = P := by
    rintro _ ⟨k,rfl⟩
    exact source_first_preserves_star_marking s d j k
  have hN : P.map (MulAut.conj : C →* MulAut C) ≤ normalizer (f.range : Set _) := by
    have he : f.range = (d.K1.subgroupOf
        (normalizer (j.J : Set G) ⊓ normalizer (Mc.pCoreIn 2 : Set G))).map
          (starComponentAction j.J (Mc.pCoreIn 2)) := by
      rw [MonoidHom.range_comp,inclusion_range]
    rw [he]
    exact source_borel_normalizes_first_actor s d j hi.normalizes
  obtain ⟨k,hk,_,ha⟩ := source_component_star_quintic s d j hi.normalizes
  apply Theory.SpecificGroups.SymplecticFour.QuinticParabolic.no_solvable_quintic_actor_of_equiv
    F.card_eq hl ho t P ht f.range hfix hN
    (starComponentAction j.J (Mc.pCoreIn 2) k) ?_ ha
  exact ⟨⟨k,hk⟩,rfl⟩

/-- The two classical families remaining after the symplectic comparison. -/
inductive LinearG2QuinticRow {D : Type*} [Group D] (L : Subgroup D) : Prop
  | linearThree (F : BinaryField) (degree : ¬4 ∣ F.degree) (e : L ≃* SL(3,F.Carrier))
  | g2 (F : BinaryField) (large : 1 < F.degree) (degree : Odd F.degree)
      (field_five : 5 ∣ F.degree) (e : L ≃* Atlas.G2.Model F.Carrier)

/-- Exclude the symplectic alternative in the complete original source classifier. -/
theorem source_component_linear_g2_row_reduction
    (hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
    (c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
      ((starRepresentation j.J (Mc.pCoreIn 2)).comp
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))) :
    LinearG2QuinticRow
      ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
        (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  cases source_component_remaining_classical_row_reduction s d j hCJ c with
  | linearThree F hd e => exact .linearThree F hd e
  | symplectic F hl hd e =>
    exact (source_no_nonbinary_symplectic_star s d j F hl
      ((subgroupOfEquivOfLe hCJ).symm.trans e)).elim
  | g2 F hl hd h5 e => exact .g2 F hl hd h5 e

/-- Retain all six B.5.1 clauses on the actual moved-section action. -/
theorem source_component_linear_g2_moved_rows :
    ∃ (_hCJ : starImage j.J (Mc.pCoreIn 2) j.J ≤
      offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))
      (_c : ChapterB.SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion
        ((starRepresentation j.J (Mc.pCoreIn 2)).comp
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))).subtype)
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2))))),
      LinearG2QuinticRow
        ((starImage j.J (Mc.pCoreIn 2) j.J).subgroupOf
          (offenderSubgroup (starRepresentation j.J (Mc.pCoreIn 2)))) := by
  have hi := source_component_input s d j
  have hc := star_moved_section_from_source hi
  let c := Classical.choice hc.2
  exact ⟨hc.1,c,source_component_linear_g2_row_reduction s d j hc.1 c⟩

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic
