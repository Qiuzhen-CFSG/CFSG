module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.SeedGeometry
public import Theory.Representation.BinaryPermutation.EightSylowFixed
public import Theory.Representation.BinaryPermutation.EightGeometry

/-!
# The literal singular flag in an original eight-letter quotient

A nonzero vector fixed by the binary-tree Sylow is the class of 11110000.
The original proper quotient preserves its flag line and seed plane. The
point residual is transitive on the three nonzero seed vectors, so the
whole seed image is totally singular. The full preimage of its flag-point
stabilizer is the preimage of the literal unordered four-block stabilizer.
No fixation by that preimage on the original section is assumed or asserted.
Source: Aschbacher–Smith 14.7.2 and 14.7.51, printed pp.1043 and 1065,
refs/quasithin.pdf.
-/

@[expose] public section
open Subgroup Representation
open BinaryPermutation
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource

def standardPointWord : core (Fin 8) := ⟨![1,1,1,1,0,0,0,0], by
  rw [mem_core]
  decide⟩
noncomputable def standardPoint : natural (Fin 8) := coreToNatural (Fin 8) standardPointWord

private theorem first_six_fixed_point :
    ∀ j : Fin 6, ∃ i : Fin 8, treeGenerator j.castSucc i = i := by decide

private theorem first_six_coordinates (w : Full (Fin 8))
    (h : ∀ j : Fin 6, representation (Fin 8) (treeGenerator j.castSucc) w = w) :
    ∀ i : Fin 8, w i = if i.val < 4 then w 0 else w 4 := by
  have h01 := congrFun (h 0) 0
  have h23 := congrFun (h 1) 2
  have h45 := congrFun (h 2) 4
  have h67 := congrFun (h 3) 6
  have h02 := congrFun (h 4) 0
  have h46 := congrFun (h 5) 4
  change w 1 = w 0 at h01
  change w 3 = w 2 at h23
  change w 5 = w 4 at h45
  change w 7 = w 6 at h67
  change w 2 = w 0 at h02
  change w 6 = w 4 at h46
  intro i
  fin_cases i <;> simp_all

/-- The full permutation Sylow fixes a unique nonzero natural vector. -/
theorem tree_fixed_eq_standardPoint (v : natural (Fin 8)) (hv : v ≠ 0)
    (hfixed : ∀ g ∈ treeGroup, naturalRepresentation (Fin 8) g v = v) :
    v = standardPoint := by
  obtain ⟨w,rfl⟩ := coreToNatural_surjective v
  have hdel (g : S8) (hg : g ∈ treeGroup) :
      deletedRepresentation (Fin 8) g ((constants (Fin 8)).mkQ w.val) =
        (constants (Fin 8)).mkQ w.val := congrArg Subtype.val (hfixed g hg)
  have hcoords := first_six_coordinates w.val (fun j => by
    obtain ⟨i,hi⟩ := first_six_fixed_point j
    exact (deleted_fixed_iff_of_fixed_point _ w.val i hi).mp
      (hdel _ (treeGenerator_mem j.castSucc)))
  have hc : ∀ x : Full (Fin 8),
      (∀ i : Fin 8, x i = if i.val < 4 then x 0 else x 4) →
      x = 0 ∨ x = allOne (Fin 8) ∨ x = standardPointWord.val ∨
      x = standardPointWord.val + allOne (Fin 8) := by decide +kernel
  rcases hc w.val hcoords with hz | ho | he | he
  · exact (hv ((EightGeometry.coreToNatural_eq_zero w).mpr (Or.inl hz))).elim
  · exact (hv ((EightGeometry.coreToNatural_eq_zero w).mpr (Or.inr ho))).elim
  · exact congrArg (coreToNatural (Fin 8)) (Subtype.ext he)
  · let ones : core (Fin 8) := ⟨allOne (Fin 8),by rw [mem_core]; decide⟩
    have hone : coreToNatural (Fin 8) ones = 0 :=
      (EightGeometry.coreToNatural_eq_zero ones).mpr (Or.inr rfl)
    have hw : w = standardPointWord + ones := Subtype.ext he
    rw [hw,map_add,hone,add_zero]
    rfl

theorem standardPoint_ne_zero : standardPoint ≠ 0 := by
  exact (EightGeometry.nonzero_singular_core_iff standardPointWord).mpr (by decide) |>.1

theorem standardPoint_singular : TerminalOrthogonal.Eight.form standardPoint = 0 := by
  exact (EightGeometry.nonzero_singular_core_iff standardPointWord).mpr (by decide) |>.2

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource

public noncomputable section
open Subgroup Representation
open BinaryPermutation BinaryNaturalDual.VectorStabilizers
open Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
open Chapter12.Section08 CriticalFusion.Source AlternatingSevenSource
universe u v
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  {I : Subgroup G} {ρ : Representation (ZMod 2) I W}

/-- The exact flag image, singular seed and point-stabilizer preimage in any
proper natural quotient of the original local section. -/
theorem local_natural_flag_geometry_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (π : I →* Equiv.Perm (Fin 8))
    (hT : ((T : Subgroup G).subgroupOf I).map π = treeGroup)
    (c : BinaryConjugationSection I (F.UH I) (F.Vi 1) ρ)
    (p : ρ.IntertwiningMap ((naturalRepresentation (Fin 8)).comp π))
    (hp : p.toLinearMap.ker ≠ ⊤) :
    let E := (c.imageSpace V).map p.toLinearMap
    let D := (c.imageSpace (F.Vi 2)).map p.toLinearMap
    Module.finrank (ZMod 2) E = 2 ∧
      D = Submodule.span (ZMod 2) {standardPoint} ∧
      (∀ x ∈ E, TerminalOrthogonal.Eight.form x = 0) ∧
      representationStabilizer ((naturalRepresentation (Fin 8)).comp π) standardPoint =
        fourStabilizer.comap π := by
  let E := (c.imageSpace V).map p.toLinearMap
  let D := (c.imageSpace (F.Vi 2)).map p.toLinearMap
  have hd : Module.finrank (ZMod 2) D = 1 := local_quotient_plane_finrank h hI c p hp
  have hn : D ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  have hfixed (v : natural (Fin 8)) (hv : v ∈ D) :
      ∀ g ∈ treeGroup, naturalRepresentation (Fin 8) g v = v := by
    intro g hg
    obtain ⟨t,ht,rfl⟩ := (hT.symm ▸ hg)
    exact local_quotient_plane_sylow_fixed c p t ht v hv
  obtain ⟨v,hv,hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hveq := tree_fixed_eq_standardPoint v hv0 (hfixed v hv)
  have hsD : standardPoint ∈ D := hveq ▸ hv
  have hsE : standardPoint ∈ E :=
    Submodule.map_mono (c.imageSpace_mono (F.le_seed 2)) hsD
  refine ⟨local_quotient_seed_finrank h hI c p hp,?_,?_,?_⟩
  · apply le_antisymm
    · intro x hx
      by_cases hx0 : x = 0
      · rw [hx0]
        exact Submodule.zero_mem _
      · rw [tree_fixed_eq_standardPoint x hx0 (hfixed x hx)]
        exact Submodule.subset_span (Set.mem_singleton _)
    · exact Submodule.span_le.mpr (fun x hx => (Set.mem_singleton_iff.mp hx).symm ▸ hsD)
  · intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]
      exact map_zero _
    obtain ⟨a,ha⟩ := local_quotient_seed_transitive h hI c p
      standardPoint hsE standardPoint_ne_zero x hx hx0
    rw [←ha]
    exact (TerminalOrthogonal.Eight.form_invariant
      (π (inclusion (F.Li_one_le_of_mem_Hz hI) a)) standardPoint).trans standardPoint_singular
  · ext g
    exact EightSylowFixed.tree_fixed_stabilizer standardPoint standardPoint_ne_zero
      (hfixed standardPoint hsD) (π g)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.EightSource
