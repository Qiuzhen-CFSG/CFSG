module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.ChiefCohomology
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.CaseComparison
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.CohomologyReduction

/-!
# Central-factor elimination for larger-field SL3 constituents

An isomorphism between actual SL3 groups induces an isomorphism of their
center quotients. Centers of Sylow two-subgroups recover the common field
degree, including the nontrivial central kernel at SL3(4). Field trace and
the graph automorphism identify the binary dual with the contragredient
natural action, so the proved larger-field H¹ vanishing applies on each
actual constituent.

Descending through a fully moved chief flag then excludes every central
factor; ascending through natural factors excludes fixed vectors. The
source consumer supplies these factors from the full earlier B.4.2 and
A.3.6 inputs and the genuine semisimple source theorem.

Source: Aschbacher--Smith, B.5.1, printed p.101, and I.1.6, p.408.
-/

public section
open Representation Representation.OneCohomology Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v

/-- The degree of an even SL3 field is intrinsic to its actual group. -/
theorem linearThree_degree_eq (F E : BinaryField)
    (e : SL(3,F.Carrier) ≃* SL(3,E.Carrier)) : F.degree = E.degree := by
  have hc : (center SL(3,F.Carrier)).map e.toMonoidHom = center SL(3,E.Carrier) := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact (centerCongr e ⟨y,hy⟩).property
    · intro hx
      refine ⟨((centerCongr e).symm ⟨x,hx⟩ : SL(3,F.Carrier)),
        ((centerCongr e).symm ⟨x,hx⟩).property, ?_⟩
      exact congrArg Subtype.val ((centerCongr e).apply_symm_apply ⟨x,hx⟩)
  let p : PSL(3,F.Carrier) ≃* PSL(3,E.Carrier) :=
    QuotientGroup.congr (center SL(3,F.Carrier)) (center SL(3,E.Carrier)) e hc
  let S : Sylow 2 PSL(3,F.Carrier) := Classical.choice inferInstance
  have hF := Matrix.PSL3.LinearThree.card_center_sylow F.Carrier F.degree_pos F.card_eq S
  have hE := Matrix.PSL3.LinearThree.card_center_sylow_of_equiv E.Carrier
    E.degree_pos E.card_eq p S
  exact Nat.pow_right_injective (by decide : 1 < 2) (hF.symm.trans hE)

private noncomputable def traceDualMap (F : BinaryField) (d : ℕ) :
    Module.Dual F.Carrier (Fin d → F.Carrier) →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Fin d → F.Carrier) where
  toFun f := (Algebra.trace (ZMod 2) F.Carrier).comp (f.restrictScalars (ZMod 2))
  map_add' f g := by ext v; simp
  map_smul' c f := by ext v; simp

private theorem traceDualMap_injective (F : BinaryField) (d : ℕ) :
    Function.Injective (traceDualMap F d) := by
  apply (LinearMap.ker_eq_bot).mp
  apply le_antisymm _ bot_le
  intro f hf
  apply LinearMap.ext
  intro v
  apply (traceForm_nondegenerate (ZMod 2) F.Carrier).1 (f v)
  intro c
  have he := LinearMap.congr_fun hf (c • v)
  simpa only [traceDualMap, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply, LinearMap.map_smul, smul_eq_mul, LinearMap.zero_apply,
    Algebra.traceForm_apply, mul_comm] using he

private noncomputable def traceDualEquiv (F : BinaryField) (d : ℕ) :
    Module.Dual F.Carrier (Fin d → F.Carrier) ≃ₗ[ZMod 2]
      Module.Dual (ZMod 2) (Fin d → F.Carrier) :=
  LinearEquiv.ofInjectiveOfFinrankEq (traceDualMap F d) (traceDualMap_injective F d) (by
    rw [← Module.finrank_mul_finrank (ZMod 2) F.Carrier
      (Module.Dual F.Carrier (Fin d → F.Carrier)),
      Subspace.dual_finrank_eq, Subspace.dual_finrank_eq, Module.finrank_mul_finrank])

/-- Dot product and field trace identify the binary dual of the natural SL3
module with its graph twist, in every positive binary field degree. -/
noncomputable def linearThreeGraphDualAction (F : BinaryField) :
    ActionEquiv (linearNatural F 3) (linearNatural F 3).dual where
  groupEquiv := (Matrix.PSL3.OuterSolvable.graphSL F.Carrier).symm
  linearEquiv := ((dotProductEquiv F.Carrier (Fin 3)).restrictScalars (ZMod 2)).trans
    (traceDualEquiv F 3)
  intertwines g v := by
    apply LinearMap.ext
    intro w
    let t := (Matrix.PSL3.OuterSolvable.graphSL F.Carrier).symm g
    have hg : g.val = (t⁻¹).val.transpose := by
      have h := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 3) F.Carrier => x.val)
        ((Matrix.PSL3.OuterSolvable.graphSL F.Carrier).apply_symm_apply g)
      change ((Matrix.SpecialLinearGroup.transpose t)⁻¹).val = g.val at h
      rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_transpose,
        ← Matrix.adjugate_transpose, ← Matrix.SpecialLinearGroup.coe_inv] at h
      exact h.symm
    change Algebra.trace (ZMod 2) F.Carrier ((g.val.mulVec v) ⬝ᵥ w) =
      Algebra.trace (ZMod 2) F.Carrier (v ⬝ᵥ ((t⁻¹).val.mulVec w))
    rw [hg, ← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.transpose_transpose]

/-- The graph-dual identification retains its explicit contragredient actor. -/
theorem linearThreeGraphDualAction_groupEquiv (F : BinaryField) :
    (linearThreeGraphDualAction F).groupEquiv =
      (Matrix.PSL3.OuterSolvable.graphSL F.Carrier).symm := by
  ext g
  rfl

variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

private noncomputable def dualActionEquiv {H W : Type*} [Group H]
    [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) H W} (e : ActionEquiv ρ σ) :
    ActionEquiv ρ.dual σ.dual where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv.symm.dualMap
  intertwines g f := by
    apply LinearMap.ext
    intro w
    change f (ρ g⁻¹ (e.linearEquiv.symm w)) =
      f (e.linearEquiv.symm (σ (e.groupEquiv g)⁻¹ w))
    congr 1
    apply e.linearEquiv.injective
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, map_inv,
      e.linearEquiv.apply_symm_apply]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- The actual larger-field natural constituent has vanishing dual first cohomology. -/
theorem linearThree_natural_dual_H1 (F : BinaryField) (hF : 1 < F.degree)
    (hn : IsLinearNatural ρ F 3) : Subsingleton (H1 ρ.dual) := by
  obtain ⟨e⟩ := hn
  let := ExtensionConsequences.H1_three_large F hF
  let := (ExtensionConsequences.actionSymm (linearThreeGraphDualAction F)).H1_subsingleton
  exact (dualActionEquiv ρ e).H1_subsingleton

/-- Commutator generation descends across a literal natural chief section. -/
theorem section_commutator_descent_of_dual_H1 (C : Subgroup G)
    (U W : Subrepresentation ρ) (hUW : U ≤ W)
    (hm : Coinvariants.ker (W.toRepresentation.comp C.subtype) = ⊤)
    [Subsingleton (H1 (Representation.dual ((sectionRepresentation ρ U W).comp C.subtype)))] :
    Coinvariants.ker (U.toRepresentation.comp C.subtype) = ⊤ := by
  let S : Subrepresentation (W.toRepresentation.comp C.subtype) :=
    ⟨(sectionLower ρ U W).toSubmodule, fun g _ hv => U.apply_mem_toSubmodule g.val hv⟩
  have hH : Subsingleton (H1 S.quotientRepresentation.dual) :=
    inferInstanceAs (Subsingleton (H1 (Representation.dual ((sectionRepresentation ρ U W).comp C.subtype))))
  let := hH
  have hs := submodule_commutator_top_of_dual_H1 (W.toRepresentation.comp C.subtype) S hm
  let e := sectionLowerEquiv ρ hUW
  have he : ∀ g v, e (S.toRepresentation g v) =
      (U.toRepresentation.comp C.subtype) g (e v) := fun _ _ => rfl
  have hmap : (Coinvariants.ker S.toRepresentation).map e.toLinearMap ≤
      Coinvariants.ker (U.toRepresentation.comp C.subtype) := by
    rw [Submodule.map_le_iff_le_comap]
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change e (S.toRepresentation g v - v) ∈ Coinvariants.ker (U.toRepresentation.comp C.subtype)
    rw [map_sub,he]
    exact Coinvariants.sub_mem_ker g (e v)
  rw [hs, Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective] at hmap
  exact top_unique hmap

/-- All layers of a fully moved natural chief flag are fully moved;
there are no central factors. This is the descending induction in B.5.1. -/
theorem flag_no_central_of_dual_H1 (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    (hm : Coinvariants.ker (ρ.comp C.subtype) = ⊤)
    (hn : ∀ i ∈ f.noncentral, Subsingleton
      (H1 (Representation.dual ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype)))) :
    (∀ i ≤ f.length, Coinvariants.ker ((f.chain i).toRepresentation.comp C.subtype) = ⊤) ∧
      f.noncentral = Finset.range f.length := by
  have step (i : ℕ) (hi : i < f.length)
      (hm : Coinvariants.ker ((f.chain (i+1)).toRepresentation.comp C.subtype) = ⊤) :
      i ∈ f.noncentral ∧ Coinvariants.ker ((f.chain i).toRepresentation.comp C.subtype) = ⊤ := by
    have hnc : i ∈ f.noncentral := by
      by_contra hh
      have hz : subspaceCommutator (sectionRepresentation ρ (f.chain i) (f.chain (i+1))) ⊤ C = ⊥ := by
        by_contra hne
        exact hh ((f.mem_noncentral i).mpr ⟨hi,hne⟩)
      exact (f.chief i hi).ne (eq_of_central_section ρ C _ _ (f.monotone (by omega)) hm hz)
    let := hn i hnc
    exact ⟨hnc,section_commutator_descent_of_dual_H1 ρ C _ _ (f.monotone (by omega)) hm⟩
  have htop : Coinvariants.ker ((f.chain f.length).toRepresentation.comp C.subtype) = ⊤ := by
    rw [f.top]
    have hle : Coinvariants.ker (ρ.comp C.subtype) ≤
        (Coinvariants.ker ((⊤ : Subrepresentation ρ).toRepresentation.comp C.subtype)).map
          (⊤ : Submodule (ZMod 2) V).subtype := by
      apply Submodule.span_le.mpr
      rintro _ ⟨⟨g,v⟩,rfl⟩
      exact ⟨((⊤ : Subrepresentation ρ).toRepresentation.comp C.subtype) g ⟨v,by trivial⟩ -
        ⟨v,by trivial⟩, Coinvariants.sub_mem_ker (ρ := (⊤ : Subrepresentation ρ).toRepresentation.comp C.subtype)
          g ⟨v,by trivial⟩, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w,hw,he⟩ := hle (hm ▸ (show v.val ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top))
    exact (Subtype.ext he : w = v) ▸ hw
  have hall (i : ℕ) (hi : i ≤ f.length) :
      Coinvariants.ker ((f.chain i).toRepresentation.comp C.subtype) = ⊤ := by
    induction hi using Nat.decreasingInduction with
    | self => exact htop
    | of_succ i hi ih => exact (step i hi ih).2
  refine ⟨hall,Finset.ext (fun i => ?_)⟩
  constructor
  · intro hi
    exact Finset.mem_range.mpr ((f.mem_noncentral i).mp hi).1
  · intro hi
    have hi := Finset.mem_range.mp hi
    exact (step i hi (hall (i+1) (by omega))).1

/-- Larger-field natural chief factors remove every central factor of the
actual fully moved flag. The field degree is checked on the true component. -/
theorem linearThree_large_flag_pure (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    (hm : Coinvariants.ker (ρ.comp C.subtype) = ⊤)
    (F : BinaryField) (hF : 1 < F.degree) (mark : C ≃* SL(3,F.Carrier))
    (hn : ∀ i ∈ f.noncentral, ∃ E : BinaryField,
      IsLinearNatural ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype) E 3) :
    f.noncentral = Finset.range f.length ∧
      ∀ i ≤ f.length,
        Coinvariants.ker ((f.chain i).toRepresentation.comp C.subtype) = ⊤ ∧
          Representation.invariants ((f.chain i).toRepresentation.comp C.subtype) = ⊥ := by
  have hH (i : ℕ) (hi : i ∈ f.noncentral) : Subsingleton
      (H1 (Representation.dual ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype))) := by
    obtain ⟨E,⟨a⟩⟩ := hn i hi
    have he := linearThree_degree_eq F E (mark.symm.trans a.groupEquiv)
    exact linearThree_natural_dual_H1 _ E (he ▸ hF) ⟨a⟩
  obtain ⟨hmoved,hindices⟩ := flag_no_central_of_dual_H1 ρ C f hm hH
  refine ⟨hindices,fun i hi => ⟨hmoved i hi, ?_⟩⟩
  apply flag_fixed_eq_bot ρ C f ?_ i hi
  intro j hj
  obtain ⟨E,⟨e⟩⟩ := hn j (hindices ▸ Finset.mem_range.mpr hj)
  exact ExtensionConsequences.invariants_of_equiv e
    (ExtensionConsequences.linearNatural_invariants E (by decide))

/-- The original earlier-source inputs discharge all natural and cohomology
premises on a fully moved SL3 chief flag. -/
theorem linearThree_large_source_flag_pure
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (hsemisimple : SourceInduction.HighThreeRank.CoverCentralizer.SourceConstruction.SemisimpleInput K)
    (h36 : Chapter1.Section02.A36Input K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hfaith : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    (hp : IsPGroup 2 (G ⧸ generalizedFitting G))
    (F : BinaryField) (hF : 1 < F.degree) (mark : generalizedFitting G ≃* SL(3,F.Carrier))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤)
    (hm : Coinvariants.ker (ρ.comp (generalizedFitting G).subtype) = ⊤) :
    f.noncentral = Finset.range f.length ∧
      ∀ i ≤ f.length,
        Coinvariants.ker ((f.chain i).toRepresentation.comp (generalizedFitting G).subtype) = ⊤ ∧
          Representation.invariants ((f.chain i).toRepresentation.comp (generalizedFitting G).subtype) = ⊥ := by
  exact linearThree_large_flag_pure ρ _ f hm F hF mark (fun i hi =>
    (linearThree_flag_natural ρ hK hsemisimple h36 earlier hsq hfaith hcore hp
      F mark f A hA hgen i hi).2.2)

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
