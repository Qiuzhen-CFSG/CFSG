module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings.Transport
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.Coverage.RootOrientation.Planes
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient
public import Theory.GroupTheory.SylowKernelCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.RankTwo
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Compatible SL₃ natural and diagram markings

The Borel is the normalizer of the literal upper unitriangular Sylow subgroup.
Aligning the natural constituent by Sylow conjugacy makes the comparison with
the independent source marking Borel preserving. Its action on the Borel
two-core permutes the two maximal elementary abelian root planes. Their
normalizers are the two standard parabolics, so diagram movement transfers.

Sylow orders q³ recover the target field size from the actual group
equivalence. For distinct field carriers, a finite-field isomorphism carries
the source flag to the target flag. Neither an agreement of the original
markings nor an automorphism-coverage hypothesis is required. This narrower
root-plane argument complements the natural/dual marking theorem in Chapter
13's `ExternalModules.FFSections.RankTwo.MarkingRigidity`.

Source: Aschbacher–Smith, E.2.2(2)(b), printed pp.215–216; the SL₃ natural
and diagram pair in 15.3.65, printed p.1152. These lemmas assume the constituent
and the source diagram witness; they do not select the F.9.18 branch.
-/

@[expose] public noncomputable section
open Representation Representation.BinaryOffender Subgroup
open Matrix Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3Even.UnipotentGeometry
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
variable {F F₀ : Type*} [Field F] [Finite F] [Field F₀] [Finite F₀]

/-- The actual SL₃ flag Borel is a Sylow-two normalizer. -/
theorem slThree_borel_normalizer {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 0 < f) :
    ∃ P : Sylow 2 SL(3,F), normalizer (P : Set SL(3,F)) = borelSL F := by
  exact ⟨PSL3.CartanActions.BorelQuotient.unipotentSLSylow F hf hF,
    normalizer_unipotentSL F⟩

/-- A group equivalence between binary SL₃ models determines the actual
field cardinality: the standard Sylow subgroups have orders q³. -/
theorem slThree_field_card_of_equiv [CharP F 2] {f : ℕ}
    (hF₀ : Nat.card F₀ = 2 ^ f) (hf : 0 < f) (e : SL(3,F₀) ≃* SL(3,F)) :
    Nat.card F = 2 ^ f := by
  let := Fintype.ofFinite F
  obtain ⟨⟨n, hn⟩, _, hc⟩ := FiniteField.card F 2
  have hF : Nat.card F = 2 ^ n := by
    simpa only [Nat.card_eq_fintype_card, PNat.mk_coe] using hc
  let P := PSL3.CartanActions.BorelQuotient.unipotentSLSylow F₀ hf hF₀
  let Q := PSL3.CartanActions.BorelQuotient.unipotentSLSylow F hn hF
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  have hcard : Nat.card P = Nat.card Q :=
    Nat.card_congr ((e.subgroupMap (P : Subgroup SL(3,F₀))).trans (P'.equiv Q)).toEquiv
  change Nat.card (P : Subgroup SL(3,F₀)) = Nat.card (Q : Subgroup SL(3,F)) at hcard
  dsimp only [P, Q] at hcard
  rw [PSL3.CartanActions.BorelQuotient.coe_unipotentSLSylow,
    PSL3.CartanActions.BorelQuotient.coe_unipotentSLSylow,
    card_unipotentSL, card_unipotentSL] at hcard
  exact (Nat.pow_left_injective (by decide : 3 ≠ 0) hcard).symm.trans hF₀

/-- After Borel alignment, the two actual SL₃ parabolics are permuted.
Their radicals are the two intrinsic maximal elementary abelian root planes. -/
theorem slThree_parabolic_pair [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (a : MulAut SL(3,F))
    (hB : (borelSL F).map a.toMonoidHom = borelSL F) :
    ((pointParabolicSL F).map a.toMonoidHom = pointParabolicSL F ∧
      (lineParabolicSL F).map a.toMonoidHom = lineParabolicSL F) ∨
    ((pointParabolicSL F).map a.toMonoidHom = lineParabolicSL F ∧
      (lineParabolicSL F).map a.toMonoidHom = pointParabolicSL F) := by
  have hcore : (borelSL F).pCoreIn 2 = unipotentSL F := by
    rw [pCoreIn, PSL3.CartanActions.BorelQuotient.twoCoreSL_eq F hF,
      map_subgroupOf_eq_of_le (unipotentSL_le_borelSL F)]
  have hU : (unipotentSL F).map a.toMonoidHom = unipotentSL F := by
    rw [← hcore, map_pCoreIn_of_injective 2 _ a.toMonoidHom a.injective, hB]
  obtain ⟨b, hp, hl⟩ :=
    PSL3Even.AutomorphismCoverage.RootOrientation.marked_plane_permutation F
      (unipotentSL F) (unipotentSLEquiv F) a hU
  have hm : markedHom F (unipotentSL F) (unipotentSLEquiv F) = specialLinear F := rfl
  rw [hm] at hp hl
  change (rootPlaneSL F true).map a.toMonoidHom = rootPlaneSL F b at hp
  change (rootPlaneSL F false).map a.toMonoidHom = rootPlaneSL F (!b) at hl
  have hN (c d : Bool) (h : (rootPlaneSL F c).map a.toMonoidHom = rootPlaneSL F d) :
      (parabolicSL F c).map a.toMonoidHom = parabolicSL F d := by
    rw [← normalizer_rootPlaneSL, map_equiv_normalizer_eq, h, normalizer_rootPlaneSL]
  cases b
  · exact Or.inr ⟨hN true false hp, hN false true hl⟩
  · exact Or.inl ⟨hN true true hp, hN false false hl⟩

/-- The parabolic-class interface needed to change an SL₃ diagram marking. -/
theorem slThree_parabolic_classes [CharP F 2] {f : ℕ}
    (hF : Nat.card F = 2 ^ f) (a : MulAut SL(3,F))
    (hB : (borelSL F).map a.toMonoidHom = borelSL F)
    (R : Subgroup SL(3,F)) (hR : R = pointParabolicSL F ∨ R = lineParabolicSL F) :
    ∃ S : Subgroup SL(3,F), (S = pointParabolicSL F ∨ S = lineParabolicSL F) ∧
      ∃ x : SL(3,F), R.map a.toMonoidHom = S.map (MulAut.conj x).toMonoidHom := by
  have hid (S : Subgroup SL(3,F)) : S.map (MulAut.conj (1 : SL(3,F))).toMonoidHom = S := by
    rw [map_one]
    exact Subgroup.map_id S
  rcases slThree_parabolic_pair hF a hB with ⟨hp, hl⟩ | ⟨hp, hl⟩
  · rcases hR with rfl | rfl
    · exact ⟨_, Or.inl rfl, 1, (hp.trans (hid _).symm)⟩
    · exact ⟨_, Or.inr rfl, 1, (hl.trans (hid _).symm)⟩
  · rcases hR with rfl | rfl
    · exact ⟨_, Or.inr rfl, 1, (hp.trans (hid _).symm)⟩
    · exact ⟨_, Or.inl rfl, 1, (hl.trans (hid _).symm)⟩

/-- Entrywise field transport identifies the literal standard SL₃ point parabolics. -/
theorem slThree_field_point (c : F₀ ≃+* F) :
    (pointParabolicSL F₀).map (Atlas.fieldEquivSL 3 c).toMonoidHom = pointParabolicSL F := by
  have hm (g : SL(3,F₀)) : Atlas.fieldEquivSL 3 c g ∈ pointParabolicSL F ↔
      g ∈ pointParabolicSL F₀ := by
    simp [mem_pointParabolicSL_iff, Atlas.fieldEquivSL, SpecialLinearGroup.map_apply_coe]
  ext g
  obtain ⟨g, rfl⟩ := (Atlas.fieldEquivSL 3 c).surjective g
  exact (Subgroup.mem_map_iff_mem (Atlas.fieldEquivSL 3 c).injective).trans (hm g).symm

/-- Entrywise field transport identifies the literal standard SL₃ plane parabolics. -/
theorem slThree_field_line (c : F₀ ≃+* F) :
    (lineParabolicSL F₀).map (Atlas.fieldEquivSL 3 c).toMonoidHom = lineParabolicSL F := by
  have hm (g : SL(3,F₀)) : Atlas.fieldEquivSL 3 c g ∈ lineParabolicSL F ↔
      g ∈ lineParabolicSL F₀ := by
    simp [mem_lineParabolicSL_iff, Atlas.fieldEquivSL, SpecialLinearGroup.map_apply_coe]
  ext g
  obtain ⟨g, rfl⟩ := (Atlas.fieldEquivSL 3 c).surjective g
  exact (Subgroup.mem_map_iff_mem (Atlas.fieldEquivSL 3 c).injective).trans (hm g).symm

/-- Entrywise field transport identifies the whole flag overlap. -/
theorem slThree_field_borel (c : F₀ ≃+* F) :
    (borelSL F₀).map (Atlas.fieldEquivSL 3 c).toMonoidHom = borelSL F := by
  rw [borelSL, Subgroup.map_inf _ _ (Atlas.fieldEquivSL 3 c).toMonoidHom (Atlas.fieldEquivSL 3 c).injective,
    slThree_field_point, slThree_field_line]
  rfl

variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V} {K T : Subgroup D}
  {I : Submodule (ZMod 2) V} {hI : K ≤ subspaceStabilizer ρ I}
  [Algebra (ZMod 2) F]

/-- Simultaneous natural-module, Borel and diagram alignment over one field.
The module and source markings are independent; the same inner correction
acts on both the group map and the linear intertwiner. -/
theorem slThree_alignment {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 0 < f)
    (d : CentralQuotientIdentification ρ K I hI
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)))
    (s : K ≃* SL(3,F)) (B : Subgroup K) (hs : B.map s.toMonoidHom = borelSL F)
    (a : InducedDiagramAction K T s (borelSL F) (pointParabolicSL F) (lineParabolicSL F)) :
    ∃ g : SL(3,F), B.map (innerIdentification d g).groupEquiv.toMonoidHom = borelSL F ∧
      ∃ a' : InducedDiagramAction K T (innerIdentification d g).groupEquiv
        (borelSL F) (pointParabolicSL F) (lineParabolicSL F), a'.element = a.element := by
  let : CharP F 2 := (Algebra.charP_iff (ZMod 2) F 2).mp inferInstance
  obtain ⟨g, hg⟩ := exists_innerIdentification d s B _ _ hs
    (slThree_borel_normalizer hF hf) (slThree_borel_normalizer hF hf)
  have hb := comparison_borel s (innerIdentification d g).groupEquiv B _ _ hs hg
  exact ⟨g, hg, remarkDiagram a _ _ _ _ hb (slThree_parabolic_classes hF _ hb), rfl⟩

/-- Equal-cardinality field carriers support the same compatible markings.
The field isomorphism is constructed and its parabolic and Borel maps checked. -/
theorem slThree_alignment_fields {f : ℕ}
    (hF₀ : Nat.card F₀ = 2 ^ f) (hF : Nat.card F = 2 ^ f) (hf : 0 < f)
    (d : CentralQuotientIdentification ρ K I hI
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)))
    (s : K ≃* SL(3,F₀)) (B : Subgroup K) (hs : B.map s.toMonoidHom = borelSL F₀)
    (a : InducedDiagramAction K T s (borelSL F₀) (pointParabolicSL F₀) (lineParabolicSL F₀)) :
    ∃ g : SL(3,F), B.map (innerIdentification d g).groupEquiv.toMonoidHom = borelSL F ∧
      ∃ a' : InducedDiagramAction K T (innerIdentification d g).groupEquiv
        (borelSL F) (pointParabolicSL F) (lineParabolicSL F), a'.element = a.element := by
  let := Fintype.ofFinite F₀
  let := Fintype.ofFinite F
  let c : F₀ ≃+* F := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hF₀.trans hF.symm)
  let e := Atlas.fieldEquivSL 3 c
  have hc : ∀ R : Subgroup SL(3,F₀), R = pointParabolicSL F₀ ∨ R = lineParabolicSL F₀ →
      ∃ S : Subgroup SL(3,F), (S = pointParabolicSL F ∨ S = lineParabolicSL F) ∧
        ∃ x : SL(3,F), R.map e.toMonoidHom = S.map (MulAut.conj x).toMonoidHom := by
    intro R hR
    rcases hR with rfl | rfl
    · refine ⟨_, Or.inl rfl, 1, ?_⟩
      rw [map_one]
      change _ = (pointParabolicSL F).map (MonoidHom.id _)
      rw [Subgroup.map_id]
      exact slThree_field_point c
    · refine ⟨_, Or.inr rfl, 1, ?_⟩
      rw [map_one]
      change _ = (lineParabolicSL F).map (MonoidHom.id _)
      rw [Subgroup.map_id]
      exact slThree_field_line c
  let a₁ := transportDiagram a e _ _ _ (slThree_field_borel c) hc
  have hs₁ : B.map (s.trans e).toMonoidHom = borelSL F := by
    change B.map (e.toMonoidHom.comp s.toMonoidHom) = _
    rw [← Subgroup.map_map, hs]
    exact slThree_field_borel c
  obtain ⟨g, hg, a', he⟩ := slThree_alignment hF hf d (s.trans e) B hs₁ a₁
  exact ⟨g, hg, a', he⟩

/-- Complete marking compatibility from the source field parameter alone.
The independently recognized natural representation determines the target
field parameter through the actual comparison of group carriers. -/
theorem slThree_compatible_markings {f : ℕ}
    (hF₀ : Nat.card F₀ = 2 ^ f) (hf : 0 < f)
    (d : CentralQuotientIdentification ρ K I hI
      (restrictScalars (k := ZMod 2) (specialLinearNatural (k := F) 3)))
    (s : K ≃* SL(3,F₀)) (B : Subgroup K) (hs : B.map s.toMonoidHom = borelSL F₀)
    (a : InducedDiagramAction K T s (borelSL F₀) (pointParabolicSL F₀) (lineParabolicSL F₀)) :
    Nat.card F = 2 ^ f ∧
    ∃ g : SL(3,F), B.map (innerIdentification d g).groupEquiv.toMonoidHom = borelSL F ∧
      ∃ a' : InducedDiagramAction K T (innerIdentification d g).groupEquiv
        (borelSL F) (pointParabolicSL F) (lineParabolicSL F), a'.element = a.element := by
  let : CharP F 2 := (Algebra.charP_iff (ZMod 2) F 2).mp inferInstance
  have hF := slThree_field_card_of_equiv hF₀ hf (s.symm.trans d.groupEquiv)
  exact ⟨hF, slThree_alignment_fields hF₀ hF hf d s B hs a⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.RankTwoMarkings
