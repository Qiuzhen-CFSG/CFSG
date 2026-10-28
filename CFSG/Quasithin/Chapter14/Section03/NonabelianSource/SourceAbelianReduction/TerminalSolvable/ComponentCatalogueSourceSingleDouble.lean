module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueSourceSingleActor
public import Theory.Representation.BinaryScalarDoubleCentralizer
public import Theory.Representation.BinaryPermutation.FiveTensorSquare.Constituent
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NormalCubicKernel
public import Theory.GroupTheory.NormalSymmetricThreeSection

/-!
# Excluding the original doubled normalized A₅

Borel containment embeds the five-point augmentation core through the original
seed. Homogeneity identifies this core with the selected constituent, so its
endomorphisms are binary scalars. The actual two-copy action then embeds the
centralizer of the same normal component in S₃. Its intersection with the
original actor has order two, and the dotted group has trivial two-core;
therefore the component centralizer supplies an ambient normal cubic subgroup.
The original source cubic-index exclusion gives the contradiction.

The final lift theorem removes the normalized A₅ from the marked small-actor
branch, retaining the literal L₂(8) row for its separate exclusion owner.
This closes the degree-eight A₅ branch without assuming ambient recognition.
The degree-four branch and final solvability remain with this task.
Source: Aschbacher–Smith 5.1.19, G.11.8 and 14.3.5,14.3.15,
printed pp.643–644,368–369,991,994.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

namespace MarkedSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s


/-- The original Borel-fixed core identifies the selected constituent on the same normal component orbit. -/
theorem single_five_constituent_core
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) :
    let H := componentOrbit L ⊤
    let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
    ∃ (a : H ≃* alternatingGroup (Fin 5))
      (c : I ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5)),
      ∀ h u, c (R.toRepresentation h u) =
        BinaryPermutation.alternatingCoreRepresentation (Fin 5) (a h) (c u) := by
  let H := componentOrbit L ⊤
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  let a : H ≃* alternatingGroup (Fin 5) := (MulEquiv.subgroupCongr hHL).trans eL
  let δ := BinaryPermutation.alternatingCoreRepresentation (Fin 5)
  let τ := F.terminalRepresentation.comp H.subtype
  obtain ⟨K,hKH,hlocal,hcomp,he,_,hnormal⟩ :=
    Recognition.terminal_component_lift s.simple F (by decide) L s.component
  change F.terminalDot K = L at he
  have hK : ComponentLift F g K :=
    ⟨hKH,hlocal,hcomp,he.symm ▸ s.component,he.symm ▸ s.moved,hnormal⟩
  have hn : L.Normal := hHL ▸ componentOrbit_top_normal L
  have hspan := hK.eq_conjugateSpanBy_of_image_normal (he.symm ▸ hn)
  let e5 := (MulEquiv.subgroupCongr he).trans eL
  obtain ⟨f,hf,_⟩ := source_single_a5_seed_core_embedding s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
    F s.nonabelian s.not_model g s.parabolic_mem s.normalizer_not_mem s.hypothesis
    hK e5 hspan
  let fH : IntertwiningMap (δ.comp a.toMonoidHom) τ := {
    toLinearMap := f.toLinearMap
    isIntertwining' h := by
      ext u
      have hh := IntertwiningMap.isIntertwining _ _ f (a h) u
      simpa [a,e5,τ,δ,BinaryPermutation.alternatingCoreRepresentation] using hh }
  let b := LinearEquiv.ofInjective fH.toLinearMap hf
  let bR : (δ.comp a.toMonoidHom) ≃ₗ fH.range.toRepresentation :=
    ⟨b, by
      intro h
      ext u
      exact IntertwiningMap.isIntertwining _ _ fH h u⟩
  have hδ : IsIrreducible (δ.comp a.toMonoidHom) := by
    exact (Representation.irreducible_comp_surjective_iff a.toMonoidHom a.surjective δ).mpr
      BinaryPermutation.FiveTensorSquare.core_irreducible
  have hr : IsIrreducible fH.range.toRepresentation := bR.symm.irreducible_of_euqiv hδ
  obtain ⟨c⟩ := (Homogeneous.sameModule_iff_repEquiv R fH.range).mp
    (s.constituents_sameModule fH.range hr)
  let d := c.trans bR.symm
  refine ⟨a,d.toLinearEquiv,?_⟩
  intro h u
  exact LinearMap.congr_fun (d.isIntertwining' h) u

/-- The same normalized A₅ constituent has only binary scalar endomorphisms. -/
theorem single_five_constituent_scalar
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) :
    let R := invariantSubspace F.terminalRepresentation (componentOrbit L ⊤) I s.selected.invariant
    ∀ t : IntertwiningMap R.toRepresentation R.toRepresentation,
      ∃ a : ZMod 2, ∀ u, t u = a • u := by
  intro R t
  obtain ⟨a,c,hc⟩ := s.single_five_constituent_core hHL eL
  let cR : R.toSubmodule ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5) := c
  have hcR (h) (u : R.toSubmodule) : cR (R.toRepresentation h u) =
      BinaryPermutation.alternatingCoreRepresentation (Fin 5) (a h) (cR u) := hc h u
  let b := cR.toLinearMap.comp (t.toLinearMap.comp cR.symm.toLinearMap)
  obtain ⟨k,hk⟩ := BinaryPermutation.FiveTensorNormalizer.core_commuting_scalar b (by
    intro z w
    obtain ⟨h,rfl⟩ := a.surjective z
    obtain ⟨u,rfl⟩ := cR.surjective w
    change cR (t (cR.symm (BinaryPermutation.alternatingCoreRepresentation (Fin 5) (a h) (cR u)))) = _
    rw [←hcR,cR.symm_apply_apply]
    rw [IntertwiningMap.isIntertwining _ _ t,hcR]
    simp only [b,LinearMap.comp_apply,LinearEquiv.coe_coe,IntertwiningMap.toLinearMap_apply,cR.symm_apply_apply])
  refine ⟨k,fun u => cR.injective ?_⟩
  have hh := hk (cR u)
  simpa only [b,LinearMap.comp_apply,LinearEquiv.coe_coe,IntertwiningMap.toLinearMap_apply,cR.symm_apply_apply,map_smul] using hh

/-- The actual centralizer of the selected normalized A₅ embeds in S₃. -/
theorem single_five_centralizer_embedding
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) :
    ∃ j : centralizer (L : Set F.TerminalHdot) →* Equiv.Perm (Fin 3),
      Function.Injective j := by
  have hk := s.not_actorFaithful_of_single_five hHL eL
  have hd := s.single_five_degree_eight hHL eL
  have hi := (s.single_five_constituent_four hHL eL).1
  obtain ⟨d⟩ := s.double_constituent_equiv hk (by omega)
  let H := componentOrbit L ⊤
  let R := invariantSubspace F.terminalRepresentation H I s.selected.invariant
  let : Nontrivial R.toSubmodule := Module.nontrivial_of_finrank_pos
    (show 0 < finrank (ZMod 2) R.toSubmodule from hi ▸ (by decide : 0 < 4))
  obtain ⟨j,hj⟩ := Representation.BinaryScalarDouble.doubled_centralizer_embedding
    F.terminalRepresentation s.hypothesis.faithful H R.toRepresentation
    (MulEquiv.refl H) d.toLinearEquiv
    (fun h u => LinearMap.congr_fun (d.isIntertwining' h) u)
    (s.single_five_constituent_scalar hHL eL)
  have hC : centralizer (H : Set F.TerminalHdot) = centralizer (L : Set F.TerminalHdot) :=
    congrArg (fun J : Subgroup F.TerminalHdot => centralizer (J : Set F.TerminalHdot)) hHL
  let a := (MulEquiv.subgroupCongr hC).symm
  exact ⟨j.comp a.toMonoidHom,hj.comp a.injective⟩

/-- A normalized A₅ in the original small-actor source is impossible. Its
nontrivial actor centralizer forces an ambient normal cubic. -/
theorem not_single_five
    (hHL : componentOrbit L ⊤ = L) (eL : L ≃* alternatingGroup (Fin 5)) : False := by
  let : L.Normal := hHL ▸ componentOrbit_top_normal L
  let C := centralizer (L : Set F.TerminalHdot)
  obtain ⟨j,hj⟩ := s.single_five_centralizer_embedding hHL eL
  have ht : 2 ∣ Nat.card C := by
    let X := F.terminalDot (F.X g)
    let Y := C.subgroupOf X
    let k : Y →* C := {
      toFun y := ⟨y.val.val,y.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
    have hk : Function.Injective k := by
      intro a b h
      have hh : a.val.val = b.val.val := congrArg (fun z : C => z.val) h
      exact Subtype.ext (Subtype.ext hh)
    have hh := Subgroup.card_dvd_of_injective k hk
    rw [(s.single_five_actor_parameters hHL eL).2] at hh
    exact hh
  obtain ⟨Q,hQ,hc,_⟩ := normal_cubic_of_normal_symmetric_three_embedding C
    s.hypothesis.twoCore_eq_bot j hj ht
  let := hQ
  let h := source_lemma_14_2_4 s.simple T s.empty s.maximal s.unique_overgroup
    s.many_overgroups s.seed_card s.centralizer_quotient.some
  let d := Recognition.rankTwo_closure_geometry h F s.nonabelian
  have hk := (Recognition.rankTwo_small_actor_geometry h F g d s.nonabelian
    s.parabolic_mem s.normalizer_not_mem s.hypothesis s.small_actor).2.2.2.2
  exact Recognition.no_normal_cubic_of_two_kernel s.simple T s.empty s.maximal
    s.unique_overgroup s.many_overgroups s.seed_card s.centralizer_quotient.some
    s.not_model F d (hk ▸ pCore_isPGroup) Q hc

/-- The original marked source leaves only the literal L₂(8) component row. -/
theorem local_lift_eight :
    ∃ K : Subgroup G, ComponentLift F g K ∧ EightImageRow F K := by
  obtain ⟨K,hK,h5 | h8⟩ := s.local_lift_single_five_actor_or_eight
  · obtain ⟨hspan,he,⟨eL⟩,_⟩ := h5
    have hnK : (K.subgroupOf F.H).Normal := by
      have hh := hK.normal_span
      rwa [← hspan] at hh
    have hnL : L.Normal := he ▸ Normal.map hnK _ (QuotientGroup.mk'_surjective _)
    let := hnL
    have hHL : componentOrbit L ⊤ = L := le_antisymm
      (iSup_conjugates_le_of_le_normalizer L ⊤ L le_rfl (by rw [normalizer_eq_top]))
      (le_componentOrbit L ⊤)
    exact (s.not_single_five hHL eL).elim
  · exact ⟨K,hK,h8⟩

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
