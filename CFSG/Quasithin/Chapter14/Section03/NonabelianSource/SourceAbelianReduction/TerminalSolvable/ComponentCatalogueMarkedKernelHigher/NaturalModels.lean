module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedNormalModels
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelHigher.OrthogonalSource
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedRecognitionReduction

/-!
# Natural orbit recognition at higher marked multiplicity

The constructed orthogonal constituent has rank-one displacement under each
noncentral actor. Its faithful self-dual action gives the natural alternating
rows of G.6.4. Homogeneity transports these coordinates to the original marked
constituent without changing the component orbit. Simplicity identifies that
orbit with the original component, preserving ambient normality.

The rows A₅, A₆ and A₇ give the original local lift. The A₈ exclusion and the
faithful and two-copy branches remain separate mathematical obligations.
Source: Aschbacher--Smith, G.11.9(1)--(3), printed p.369;14.3.15, p.994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- Every noncentral actor has an orthogonal constituent on which the
actual quotient is a natural symmetric group, with the same alternating orbit. -/
theorem source_higher_orthogonal_natural_model
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (x : F.terminalDot (F.X g))
    (hxC : (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
    ∃ (J : Submodule (ZMod 2) (Additive F.Uhat))
      (hJ : IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) J),
      v ∉ J ∧ J ≤ B.orthogonal I ∧
      ∃ hY : zpowers (x : F.TerminalHdot) ≤ subspaceStabilizer F.terminalRepresentation J,
      let σ := ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (zpowers (x : F.TerminalHdot)) J hJ.choose hY
      ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
        ChapterG.Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤
          (BinaryPermutation.naturalRepresentation (Fin n)) ∧
        ChapterG.Section09.Quasiequivalent
          (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) J hJ.choose).toRepresentation
          (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := by
  let H := componentOrbit L ⊤
  let : H.Normal := componentOrbit_top_normal L
  let : Group.IsPerfect H := s.component.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr s.component.componentOrbit_top_ne_bot
  obtain ⟨J,hJ,hv,hperp,hxJ,hr⟩ := s.source_exists_orthogonal_constituent_rank_one hk hd x hxC
  let R := invariantSubspace F.terminalRepresentation H J hJ.choose
  have hi : IsIrreducible R.toRepresentation :=
    hJ.irreducible_of_normal_restriction F.terminalRepresentation
      (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) H
  have hdual := constituent_selfDual_of_sameModule F.terminalRepresentation H
    (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) B s.hypothesis.preserves
    s.hypothesis.nondegenerate hJ
    (fun K hK => (s.constituents_sameModule R hi).symm.trans (s.constituents_sameModule K hK))
  have hY : zpowers (x : F.TerminalHdot) ≤ subspaceStabilizer F.terminalRepresentation J :=
    zpowers_le.mpr hxJ
  refine ⟨J,hJ,hv,hperp,hY,?_⟩
  apply ChapterG.Section11.normal_constituent_natural_model F.terminalRepresentation H
    (zpowers (x : F.TerminalHdot)) J hJ.choose hY hi (s.constituent_faithful R hi)
    (by
      have he : Module.finrank (ZMod 2) J = Module.finrank (ZMod 2) I :=
        s.constituent_finrank_eq R hi
      have hi := s.dimension_gt_two
      omega)
    hdual ⟨Recognition.terminal_sqtkCover s.simple F (by decide)⟩
    ⟨x,mem_zpowers _⟩ ?_ hr
  exact congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 (F.terminalDot (F.X g))) x)

/-- G.11.9(3) with the original marked I and its literal component orbit. -/
theorem source_higher_natural_model
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
      ChapterG.Section09.Quasiequivalent
        (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := by
  have hn : ¬ F.terminalDot (F.X g) ≤ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) := by
    intro h
    exact (ne_of_lt s.actor_centralizer_lt) (inf_eq_left.mpr h)
  obtain ⟨x,hx,hxC⟩ := SetLike.not_le_iff_exists.mp hn
  obtain ⟨J,hJ,_,_,_,n,hn5,hn8,_,e,c,hc⟩ :=
    s.source_higher_orthogonal_natural_model hk hd ⟨x,hx⟩ hxC
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) J hJ.choose
  have hi : IsIrreducible R.toRepresentation := by
    let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
    exact hJ.irreducible_of_normal_restriction F.terminalRepresentation
      (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) (componentOrbit L ⊤)
  obtain ⟨f,hf⟩ := s.constituents_sameModule R hi
  exact ⟨n,hn5,hn8,e,f.trans c,fun a w => by change c (f (_)) = _; rw [hf,hc]; rfl⟩

/-- Simplicity of an alternating orbit recovers equality with the original
component, rather than merely normality inside the constituent quotient. -/
theorem component_eq_orbit_of_alternating
    (n : ℕ) (hn : 5 ≤ n) (e : componentOrbit L ⊤ ≃* alternatingGroup (Fin n)) :
    L = componentOrbit L ⊤ := by
  let H := componentOrbit L ⊤
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa using hn)
  let : IsSimpleGroup H := e.isSimpleGroup
  have hLH := le_componentOrbit L (⊤ : Subgroup F.TerminalHdot)
  rcases s.component.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup H) with hb | ht
  · have he := congrArg (Subgroup.map H.subtype) hb
    rw [map_subgroupOf_eq_of_le hLH,Subgroup.map_bot] at he
    exact (s.moved (by rw [he,commutator_bot_left])).elim
  · exact le_antisymm hLH (subgroupOf_eq_top.mp ht)

/-- The three catalogue rows produced by a natural orbit of degree below eight,
including equality of the component image with the whole orbit in the A₇ row. -/
theorem imageCases_of_natural_orbit_below_eight
    (n : ℕ) (hn5 : 5 ≤ n) (hn7 : n ≤ 7)
    (e : componentOrbit L ⊤ ≃* alternatingGroup (Fin n)) : s.ImageCases := by
  have heq := s.component_eq_orbit_of_alternating n hn5 e
  let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
  let j := MarkedAction.subgroupEquiv F.terminalRepresentation (componentOrbit L ⊤)
    (F.terminalDot (F.X g)) I s.selected.invariant s.actor_stabilizes
    (s.constituent_faithful R s.irreducible) L (le_componentOrbit L ⊤)
  let f := (MulEquiv.subgroupCongr heq).trans e
  interval_cases n
  · exact s.imageCases_of_smallComponentImage (Or.inl ⟨f⟩)
  · exact s.imageCases_of_smallComponentImage (Or.inr ⟨f⟩)
  · exact Or.inl ⟨(MarkedAction.image_eq_iff F.terminalRepresentation
      (componentOrbit L ⊤) (F.terminalDot (F.X g)) I s.selected.invariant
      s.actor_stabilizes (s.constituent_faithful R s.irreducible) L
      (le_componentOrbit L ⊤)).mpr heq.symm,Or.inr (Or.inl ⟨j.symm.trans f⟩)⟩

/-- All higher-multiplicity marked sources yield the actual catalogue lift
unless the same orbit and original marked constituent are the natural A₈ model. -/
theorem local_lift_or_natural_eight_of_higher_dimension
    (hk : ¬ ActorFaithful (F := F) (g := g) (I := I))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    (∃ K : Subgroup G, ComponentLift F g K ∧ ComponentCases F K) ∨
      (L = componentOrbit L ⊤ ∧ L.Normal ∧
        ChapterG.Section09.Quasiequivalent
          (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant).toRepresentation
          (BinaryPermutation.alternatingNaturalRepresentation (Fin 8))) := by
  obtain ⟨n,hn5,hn8,hm⟩ := s.source_higher_natural_model hk hd
  have hm' := hm
  obtain ⟨e,_,_⟩ := hm'
  by_cases he : n = 8
  · subst n
    have heq := s.component_eq_orbit_of_alternating 8 (by decide) e
    exact Or.inr ⟨heq,heq.symm ▸ componentOrbit_top_normal L,hm⟩
  · exact Or.inl (s.local_lift_of_image_cases
      (s.imageCases_of_natural_orbit_below_eight n hn5 (by omega) e))

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
