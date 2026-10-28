module
public import CFSG.Quasithin.ChapterG.Section10.Components.Containment
public import CFSG.Quasithin.ChapterG.Section10.Components.Orthogonal
public import Theory.Representation.NormalComponentConstituents.Homogeneous
/-!
# The homogeneous constituent branch of G.10.15

For the actual normal orbit of a moved component, every nonzero HX-submodule
contains the marked point. An X-invariant constituent therefore determines
the unique occurring simple type; its full homogeneous component is V.
Faithfulness and self-duality follow for its literal restricted action.

A nondegenerate constituent containing the point must be all of V, since
its invariant orthogonal complement would also contain the point. The
alternative is total isotropy. The marked point also proves uniqueness of
the X-invariant constituent. These are G.10.13 and the homogeneous branch
of G.10.15, Aschbacher--Smith, printed pp.360--361.

The exchanged-constituent branch is not asserted in this module.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10.Hypothesis
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- G.10.13 on the normal orbit of the selected component. -/
theorem constituent_isotropic_or_top_of_point_mem (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ (componentOrbit L ⊤) I)
    (hv : v ∈ I) :
    (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∨
      (I = ⊤ ∧ IsIrreducible (ρ.comp (componentOrbit L ⊤).subtype)) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hi := h.irreducible_of_not_solvable hn
  rcases hI.isotropic_or_nondegenerate_of_normal_restriction ρ hi H B h.alternating
    h.preserves with hiso | hnd
  · exact Or.inl hiso
  right
  have hcomp := B.isCompl_orthogonal_of_restrict_nondegenerate h.alternating.isRefl hnd
  have htop : I = ⊤ := by
    by_contra hne
    have ho0 : B.orthogonal I ≠ ⊥ := by
      intro hz
      exact hne (by simpa only [hz,sup_bot_eq] using hcomp.sup_eq_top)
    have hXI := h.stabilizes_constituent_of_point_mem hi H hI hv
    have hvo := h.point_mem_normal_component_subspace hn hL hm S hnX hind
      (B.orthogonal I) (orthogonal_invariant ρ B h.preserves hI.choose)
      (orthogonal_invariant ρ B h.preserves hXI) ho0
    have hz : v ∈ I ⊓ B.orthogonal I := ⟨hv,hvo⟩
    rw [hcomp.inf_eq_bot] at hz
    exact h.point_ne_zero hz
  refine ⟨htop,?_⟩
  let R := invariantSubspace ρ H I hI.choose
  have hR : IsAtom R := (Subrepresentation.irreducible_iff_isAtom R).mp
    (hI.irreducible_of_normal_restriction ρ hi H)
  have hRt : R = ⊤ := Subrepresentation.toSubmodule_injective htop
  exact isSimpleOrder_iff_isAtom_top.mpr (hRt ▸ hR)

/-- The constituent through the marked point determines the unique occurring
simple type for the actual normal orbit H. -/
theorem constituent_sameModule_of_point_mem (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ (componentOrbit L ⊤) I)
    (hv : v ∈ I) :
    ∀ J : Subrepresentation (ρ.comp (componentOrbit L ⊤).subtype),
      IsIrreducible J.toRepresentation →
      Homogeneous.SameModule (invariantSubspace ρ (componentOrbit L ⊤) I hI.choose) J := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hi := h.irreducible_of_not_solvable hn
  exact sameModule_of_common_point ρ H X v h.point_ne_zero
    (invariantSubspace ρ H I hI.choose) (hI.irreducible_of_normal_restriction ρ hi H)
    hv (h.stabilizes_constituent_of_point_mem hi H hI hv)
    (h.point_mem_normal_component_subspace hn hL hm S hnX hind)

/-- The homogeneous branch of G.10.15 retains the actual faithful self-dual
constituent, not an isomorphism-class label. -/
theorem constituent_homogeneous_faithful_selfDual_of_point_mem (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlus ρ (componentOrbit L ⊤) I)
    (hv : v ∈ I) :
    let R := invariantSubspace ρ (componentOrbit L ⊤) I hI.choose
    Homogeneous.homogeneousPart R ⊤ = ⊤ ∧
      Function.Injective R.toRepresentation ∧
      Nonempty (Representation.Equiv R.toRepresentation R.toRepresentation.dual) ∧
      ((∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∨
        (I = ⊤ ∧ IsIrreducible (ρ.comp (componentOrbit L ⊤).subtype))) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let R := invariantSubspace ρ H I hI.choose
  have hi := h.irreducible_of_not_solvable hn
  have hR : IsIrreducible R.toRepresentation := hI.irreducible_of_normal_restriction ρ hi H
  have hh := h.constituent_sameModule_of_point_mem hn hL hm S hnX hind hI hv
  refine ⟨?_, constituent_faithful_of_sameModule ρ H h.faithful hi R hR hh,
    constituent_selfDual_of_sameModule ρ H hi B h.preserves h.nondegenerate hI hh,
    h.constituent_isotropic_or_top_of_point_mem hn hL hm S hnX hind hI hv⟩
  apply top_unique
  have ht := hI.conjugates_span_of_normal_restriction ρ hi H
  have ht' := congrArg (fun J : Subrepresentation (ρ.comp H.subtype) => J.toSubmodule) ht
  rw [Homogeneous.toSubmodule_iSup] at ht'
  change (⨆ g : G, (conjugateSubrepresentation ρ H R g).toSubmodule) = (⊤ : Submodule (ZMod 2) V) at ht'
  change (⊤ : Submodule (ZMod 2) V) ≤ Homogeneous.homogeneousPart R ⊤
  conv_lhs => rw [← ht']
  refine iSup_le fun g => ?_
  let J := conjugateSubrepresentation ρ H R g
  have hJ : IsIrreducible J.toRepresentation := by
    apply (Subrepresentation.irreducible_iff_isAtom _).mpr
    simpa only [J, conjugateSubrepresentationOrderIso_apply, inv_inv] using
      ((conjugateSubrepresentationOrderIso ρ H g⁻¹).isAtom_iff R).mpr
        ((Subrepresentation.irreducible_iff_isAtom R).mp hR)
  exact le_iSup_of_le J (le_iSup_of_le ⟨le_top,hh J hJ⟩ le_rfl)

/-- There is at most one X-invariant Irr-plus constituent of the normal orbit.
Its nonzero common point rules out distinct simple subspaces. -/
theorem invariant_constituent_unique (hn : ¬ Group.IsSolvable G)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    (S : Sylow 2 G) (hnX : (S : Subgroup G) ≤ normalizer (X : Set G))
    (hind : (normalizer (L : Set G)).index ≤ 2)
    {I J : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hJ : IsIrrPlus ρ (componentOrbit L ⊤) J)
    (hXI : X ≤ subspaceStabilizer ρ I) (hXJ : X ≤ subspaceStabilizer ρ J) : I = J := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  have hi := h.irreducible_of_not_solvable hn
  have hvI := (h.point_mem_iff_stabilizes_component_constituent hn hL hm S hnX hind hI).mpr hXI
  have hvJ := (h.point_mem_iff_stabilizes_component_constituent hn hL hm S hnX hind hJ).mpr hXJ
  let R := invariantSubspace ρ H I hI.choose
  let Q := invariantSubspace ρ H J hJ.choose
  have ha := (Subrepresentation.irreducible_iff_isAtom R).mp
    (hI.irreducible_of_normal_restriction ρ hi H)
  have hb := (Subrepresentation.irreducible_iff_isAtom Q).mp
    (hJ.irreducible_of_normal_restriction ρ hi H)
  by_contra he
  have hRQ : R ≠ Q := fun h => he (congrArg
    (fun P : Subrepresentation (ρ.comp H.subtype) => P.toSubmodule) h)
  have hd := (ha.disjoint_of_ne hb hRQ).eq_bot
  have hvbot : v ∈ (⊥ : Subrepresentation (ρ.comp H.subtype)) := hd ▸ ⟨hvI,hvJ⟩
  exact h.point_ne_zero hvbot

end CFSG.Quasithin.ChapterG.Section10.Hypothesis
