module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.SingleNaturalChiefs
public import Theory.Representation.FirstCohomologyDuality.Indecomposable

/-!
# Central-factor elimination and proper-submodule recursion in B.5.1

For an exact submodule U of a commutator-generated module V, vanishing of
H¹ on the dual quotient forces U to be commutator-generated. The proof
uses the literal central cover V/[U,G] → V/U and the checked universal-cover
kernel bound. No semisimplicity or splitting of V is assumed.

Descending through the binary-natural chief flag excludes every central
factor. Ascending through its fixed-point-free natural factors eliminates
fixed vectors. Faithfulness of the first section makes each nonzero term
faithful, and strict dimension decrease supplies the actual recursive B.5.1
application on every proper term, including the maximal one.

The source application discharges the model cohomology hypotheses using
the proved natural and contragredient binary calculations. The smaller-
dimension induction hypothesis remains explicitly restricted by dimension.
Source: Aschbacher--Smith, B.5.1, printed pp.101--102, and I.1.6(6), p.408.
-/

public section

open Representation Representation.OneCohomology Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem quotient_commutator_top (U : Subrepresentation ρ)
    (hm : Coinvariants.ker ρ = ⊤) : Coinvariants.ker U.quotientRepresentation = ⊤ := by
  apply top_unique
  intro w _
  obtain ⟨v,rfl⟩ := U.toSubmodule.mkQ_surjective w
  have hv : v ∈ Coinvariants.ker ρ := hm ▸ Submodule.mem_top
  have hle : Coinvariants.ker ρ ≤ (Coinvariants.ker U.quotientRepresentation).comap
      U.toSubmodule.mkQ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    change U.toSubmodule.mkQ (ρ g v - v) ∈ Coinvariants.ker U.quotientRepresentation
    rw [map_sub]
    exact Coinvariants.sub_mem_ker g (U.toSubmodule.mkQ v)
  exact hle hv

/-- Vanishing dual H¹ on the quotient makes every submodule of a fully
commutator-generated extension itself fully commutator-generated. -/
theorem submodule_commutator_top_of_dual_H1 (U : Subrepresentation ρ)
    (hm : Coinvariants.ker ρ = ⊤)
    [Subsingleton (H1 U.quotientRepresentation.dual)] :
    Coinvariants.ker U.toRepresentation = ⊤ := by
  let D : Subrepresentation ρ := {
    toSubmodule := (Coinvariants.ker U.toRepresentation).map U.toSubmodule.subtype
    apply_mem_toSubmodule g := by
      rintro _ ⟨v,hv,rfl⟩
      refine ⟨U.toRepresentation g v, ?_, rfl⟩
      have hh := (Coinvariants.ker U.toRepresentation).add_mem (Coinvariants.sub_mem_ker g v) hv
      rw [sub_add_cancel] at hh
      exact hh }
  have hDU : D ≤ U := Submodule.map_subtype_le _ _
  let p : D.quotientRepresentation.IntertwiningMap U.quotientRepresentation :=
    (D.toSubmodule.liftQ U.toSubmodule.mkQ (by
      intro v hv
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hDU hv))).intertwiningMap_of_isIntertwiningMap
      _ _ (by
        intro g v
        induction v using Submodule.Quotient.induction_on with
        | _ v => rfl)
  have hp : IsCover p := by
    refine ⟨?_, ?_, quotient_commutator_top ρ D hm⟩
    · intro w
      obtain ⟨v,rfl⟩ := U.toSubmodule.mkQ_surjective w
      exact ⟨D.toSubmodule.mkQ v,rfl⟩
    · intro w hw g
      induction w using Submodule.Quotient.induction_on with
      | _ v =>
        have hv : v ∈ U := (Submodule.Quotient.mk_eq_zero _).mp hw
        apply (Submodule.Quotient.eq D.toSubmodule).mpr
        change ρ g v - v ∈ D.toSubmodule
        exact ⟨U.toRepresentation g ⟨v,hv⟩ - ⟨v,hv⟩,
            Coinvariants.sub_mem_ker (ρ := U.toRepresentation) g ⟨v,hv⟩, rfl⟩
  have hdim := finrank_ker_le_H1_of_cover p hp
  have hz : Module.finrank (ZMod 2) (H1 U.quotientRepresentation.dual) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hinj : Function.Injective p := LinearMap.ker_eq_bot.mp
    (Submodule.finrank_eq_zero.mp (by omega))
  apply top_unique
  intro v _
  have hz : p (D.toSubmodule.mkQ v.val) = p 0 := by
    change U.toSubmodule.mkQ v.val = 0
    exact (Submodule.Quotient.mk_eq_zero _).mpr v.property
  have hv : v.val ∈ D := (Submodule.Quotient.mk_eq_zero _).mp (hinj hz)
  obtain ⟨w,hw,he⟩ := hv
  exact (Subtype.ext he : w = v) ▸ hw


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
/-- The actual natural binary chief factor has vanishing dual first cohomology. -/
theorem binary_natural_dual_H1 {d : ℕ} (hd : 4 ≤ d)
    (hn : IsLinearNatural ρ BinaryField.two d) : Subsingleton (H1 ρ.dual) := by
  obtain ⟨e⟩ := hn
  let := H1_linearNatural_subsingleton hd
  let := (dualNaturalEquiv d).H1_subsingleton
  exact (dualActionEquiv ρ e).H1_subsingleton

/-- Commutator generation descends across a literal natural chief section. -/
theorem binary_section_commutator_descent (C : Subgroup G)
    (U W : Subrepresentation ρ) (hUW : U ≤ W)
    (hm : Coinvariants.ker (W.toRepresentation.comp C.subtype) = ⊤)
    {d : ℕ} (hd : 4 ≤ d)
    (hn : IsLinearNatural ((sectionRepresentation ρ U W).comp C.subtype)
      BinaryField.two d) :
    Coinvariants.ker (U.toRepresentation.comp C.subtype) = ⊤ := by
  let S : Subrepresentation (W.toRepresentation.comp C.subtype) :=
    ⟨(sectionLower ρ U W).toSubmodule, fun g _ hv => U.apply_mem_toSubmodule g.val hv⟩
  have hH : Subsingleton (H1 S.quotientRepresentation.dual) :=
    binary_natural_dual_H1 _ hd hn
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

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A central quotient of a fully commutator-generated upper space is zero. -/
theorem eq_of_central_section (C : Subgroup G) (U W : Subrepresentation ρ) (hUW : U ≤ W)
    (hm : Coinvariants.ker (W.toRepresentation.comp C.subtype) = ⊤)
    (hc : subspaceCommutator (sectionRepresentation ρ U W) ⊤ C = ⊥) : U = W := by
  apply le_antisymm hUW
  intro w hw
  have hle : Coinvariants.ker (W.toRepresentation.comp C.subtype) ≤
      U.toSubmodule.comap W.toSubmodule.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨g,v⟩,rfl⟩
    exact (sectionRepresentation_trivial_iff ρ U W g.val).mp
      (fun s => (subspaceCommutator_eq_bot_iff _ ⊤ C).mp hc (by trivial) g) v v.property
  exact hle (hm ▸ (show (⟨w,hw⟩ : W.toSubmodule) ∈ (⊤ : Submodule (ZMod 2) W.toSubmodule) from
    Submodule.mem_top))


/-- All layers of a fully moved binary-natural chief flag are fully moved;
there are no central factors. This is the descending induction in B.5.1. -/
theorem binary_flag_no_central (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    (hm : Coinvariants.ker (ρ.comp C.subtype) = ⊤)
    (hn : ∀ i ∈ f.noncentral, ∃ d : ℕ, 4 ≤ d ∧
      IsLinearNatural ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype)
        BinaryField.two d) :
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
    obtain ⟨d,hd,hni⟩ := hn i hnc
    exact ⟨hnc,binary_section_commutator_descent ρ C _ _ (f.monotone (by omega)) hm hd hni⟩
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

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- Fixed vectors cannot survive a flag with fixed-point-free factors. -/
theorem flag_fixed_eq_bot (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    (hz : ∀ i < f.length,
      Representation.invariants ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype) = ⊥) :
    ∀ i ≤ f.length, Representation.invariants ((f.chain i).toRepresentation.comp C.subtype) = ⊥ := by
  intro i hi
  induction i with
  | zero =>
    rw [f.bottom]
    apply bot_unique
    intro v _
    apply Subtype.ext
    exact v.property
  | succ i ih =>
    have hi' : i < f.length := by omega
    have hprev := ih (by omega)
    apply bot_unique
    intro v hv
    have hq : (sectionLower ρ (f.chain i) (f.chain (i+1))).toSubmodule.mkQ v ∈
        Representation.invariants ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype) := by
      intro g
      change (sectionLower ρ (f.chain i) (f.chain (i+1))).toSubmodule.mkQ
        ((f.chain (i+1)).toRepresentation g.val v) = _
      exact congrArg (sectionLower ρ (f.chain i) (f.chain (i+1))).toSubmodule.mkQ (hv g)
    rw [hz i hi'] at hq
    have hmem : v.val ∈ f.chain i :=
      (Submodule.Quotient.mk_eq_zero (sectionLower ρ (f.chain i) (f.chain (i+1))).toSubmodule).mp hq
    have hv' : (⟨v.val,hmem⟩ : (f.chain i).toSubmodule) ∈
        Representation.invariants ((f.chain i).toRepresentation.comp C.subtype) := by
      intro g
      apply Subtype.ext
      exact congrArg (fun w : (f.chain (i+1)).toSubmodule => (w : V)) (hv g)
    rw [hprev] at hv'
    apply Subtype.ext
    exact congrArg (fun w : (f.chain i).toSubmodule => (w : V)) hv'

/-- The literal binary chief flag has no central factors, and all its terms
are commutator-generated and fixed-point-free. No semisimplicity is assumed. -/
theorem binary_flag_pure (C : Subgroup G) (f : ReducibleChiefFlag ρ C)
    (hm : Coinvariants.ker (ρ.comp C.subtype) = ⊤)
    (hn : ∀ i ∈ f.noncentral, ∃ d : ℕ, 4 ≤ d ∧
      IsLinearNatural ((sectionRepresentation ρ (f.chain i) (f.chain (i+1))).comp C.subtype)
        BinaryField.two d) :
    f.noncentral = Finset.range f.length ∧
      ∀ i ≤ f.length,
        Coinvariants.ker ((f.chain i).toRepresentation.comp C.subtype) = ⊤ ∧
          Representation.invariants ((f.chain i).toRepresentation.comp C.subtype) = ⊥ := by
  obtain ⟨hmoved,hindices⟩ := binary_flag_no_central ρ C f hm hn
  refine ⟨hindices,fun i hi => ⟨hmoved i hi, ?_⟩⟩
  apply flag_fixed_eq_bot ρ C f ?_ i hi
  intro j hj
  obtain ⟨d,hd,⟨e⟩⟩ := hn j (hindices ▸ Finset.mem_range.mpr hj)
  exact ExtensionConsequences.invariants_of_equiv e
    (ExtensionConsequences.linearNatural_invariants BinaryField.two (by omega))

/-- The original B.5.1 binary setup on a fully moved module discharges every
cohomological premise in the chief-flag purification. -/
theorem binary_source_flag_pure
    {K : CFSG.Quasithin.GroupClass} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    [IsQuasisimple (Theory.GroupTheory.generalizedFitting G)]
    (hsq : IsSQTK K (Theory.GroupTheory.generalizedFitting G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5)
    (mark : Theory.GroupTheory.generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (Theory.GroupTheory.generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : Theory.GroupTheory.generalizedFitting G ⊔ A = ⊤)
    (hm : Coinvariants.ker (ρ.comp (Theory.GroupTheory.generalizedFitting G).subtype) = ⊤) :
    f.noncentral = Finset.range f.length ∧
      ∀ i ≤ f.length,
        Coinvariants.ker ((f.chain i).toRepresentation.comp
          (Theory.GroupTheory.generalizedFitting G).subtype) = ⊤ ∧
        Representation.invariants ((f.chain i).toRepresentation.comp (Theory.GroupTheory.generalizedFitting G).subtype) = ⊥ := by
  apply binary_flag_pure ρ _ f hm
  intro i hi
  refine ⟨d,by omega,?_⟩
  exact (binary_flag_natural ρ hK earlier hsq hf hcore hd mark f A hA hgen i hi).2

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
/-- A faithful literal section makes every submodule containing its upper
space faithful, without any assumption on the section's lower kernel. -/
theorem faithful_submodule_of_section (U W X : Subrepresentation ρ) (hWX : W ≤ X)
    (hf : Function.Injective (sectionRepresentation ρ U W)) :
    Function.Injective X.toRepresentation := by
  intro g h hgh
  apply hf
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ w =>
    have he := LinearMap.congr_fun hgh (⟨w.val,hWX w.property⟩ : X.toSubmodule)
    have hv : W.toRepresentation g w = W.toRepresentation h w := by
      apply Subtype.ext
      exact congrArg (fun x : X.toSubmodule => (x : V)) he
    exact congrArg (sectionLower ρ U W).toSubmodule.mkQ hv

/-- Strict dimension recursion on an actual proper flag term. This applies
B.5.1 to the whole reducible term, not only to irreducible chief quotients. -/
theorem recursive_faithful_flag_term {K : CFSG.Quasithin.GroupClass.{u}}
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hcore : pCore 2 G = ⊥)
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    {A : Subgroup G} (hA : IsBestOffender ρ A)
    {i : ℕ} (hi : i < f.length)
    (hf : Function.Injective (f.chain i).toRepresentation) :
    LocalSourceConclusion (f.chain i).toRepresentation (generalizedFitting G) A := by
  have hlt : (f.chain i).toSubmodule < ⊤ := by
    have ht : f.chain i < f.chain f.length :=
      lt_of_lt_of_le (f.chief i hi).lt (f.monotone (by omega))
    rw [f.top] at ht
    exact ht
  have hdim : Module.finrank (ZMod 2) (f.chain i).toSubmodule < Module.finrank (ZMod 2) V := by
    simpa only [finrank_top] using Submodule.finrank_lt_finrank_of_lt hlt
  have hs := local_source_hypothesis (f.chain i).toRepresentation (generalizedFitting G)
    hsq rfl hcore hf (bestOffender_on_subrepresentation ρ (f.chain i) hA)
  exact ih ↥(generalizedFitting G ⊔ A) (f.chain i).toSubmodule
    ((f.chain i).toRepresentation.comp (generalizedFitting G ⊔ A).subtype)
    ((generalizedFitting G).subgroupOf (generalizedFitting G ⊔ A)) hdim hs

/-- The source binary flag supplies the strict induction hypotheses for every
nonzero proper term, including the maximal submodule used on printed p.101.
Its component action is fully moved and fixed-point-free. -/
theorem binary_source_flag_recursion
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hgen : generalizedFitting G ⊔ A = ⊤)
    (hm : Coinvariants.ker (ρ.comp (generalizedFitting G).subtype) = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < f.length) :
    Function.Injective (f.chain i).toRepresentation ∧
      Coinvariants.ker ((f.chain i).toRepresentation.comp (generalizedFitting G).subtype) = ⊤ ∧
      Representation.invariants ((f.chain i).toRepresentation.comp (generalizedFitting G).subtype) = ⊥ ∧
      LocalSourceConclusion (f.chain i).toRepresentation (generalizedFitting G) A := by
  obtain ⟨hindices,hpure⟩ := binary_source_flag_pure ρ hK earlier hsq hf hcore hd mark f A hA hgen hm
  have hzero : 0 ∈ f.noncentral := by
    rw [hindices]
    exact Finset.mem_range.mpr (by omega)
  have hf0 := binary_flag_factor_faithful ρ hd mark f hzero
  have hfi := faithful_submodule_of_section ρ (f.chain 0) (f.chain 1) (f.chain i)
    (f.monotone (by omega)) hf0
  exact ⟨hfi,(hpure i (by omega)).1,(hpure i (by omega)).2,
    recursive_faithful_flag_term ρ ih hsq hcore f hA.1 hi hfi⟩

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
