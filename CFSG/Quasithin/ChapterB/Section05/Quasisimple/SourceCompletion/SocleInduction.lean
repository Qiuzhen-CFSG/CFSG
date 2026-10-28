module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinaryWhole
public import Mathlib.RepresentationTheory.Semisimple

/-!
# Semisimple terms in the actual B.5.1 recursion

The strict induction conclusion supplies semisimplicity through its homogeneous
or natural-plus-dual alternatives. Actual action equivalences transport the
invariant-subspace lattices, and the literal moved quotient is identified with
the original action only after full commutator generation and absence of fixed
vectors have been proved. The binary chief-flag consumer discharges both facts
and applies the strict dimension induction to every nonzero proper term.

For the subsequent quotient reconstruction, two disjoint submodules with
semisimple quotients force semisimplicity of the original module: the diagonal
map embeds it in the product of those quotients. No splitting or classifier is
assumed by this criterion.

Source: Aschbacher--Smith, B.5.1, printed pp.101--102, maximal-submodule step
and case (B). The final natural-sum reconstruction remains separate.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MonoidAlgebra MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v w
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Two semisimple quotients by disjoint actual submodules make the original
module semisimple, via the injective diagonal map into their product. -/
theorem semisimple_of_disjoint_quotients (U W : Subrepresentation ρ)
    (hd : Disjoint U.toSubmodule W.toSubmodule)
    (hU : IsSemisimpleRepresentation U.quotientRepresentation)
    (hW : IsSemisimpleRepresentation W.quotientRepresentation) :
    IsSemisimpleRepresentation ρ := by
  let P : Bool → Subrepresentation ρ := fun b => if b then U else W
  let τ := fun b => (P b).quotientRepresentation
  let p (b : Bool) : ρ.IntertwiningMap (τ b) :=
    (P b).toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  let f : ρ.asModule →ₗ[(ZMod 2)[G]] (∀ b : Bool, (τ b).asModule) :=
    LinearMap.pi (fun b => IntertwiningMap.equivLinearMapAsModule ρ (τ b) (p b))
  have hi : Function.Injective f := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp hd (x-y)
    · exact (Submodule.Quotient.eq U.toSubmodule).mp (congrFun hxy true)
    · exact (Submodule.Quotient.eq W.toSubmodule).mp (congrFun hxy false)
  have ht (b : Bool) : IsSemisimpleRepresentation (τ b) := by
    cases b
    · exact hW
    · exact hU
  let : ∀ b : Bool, IsSemisimpleModule (ZMod 2)[G] (τ b).asModule := fun b =>
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule (τ b)).mp (ht b)
  exact (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mpr
    (IsSemisimpleModule.of_injective f hi)

/-- A faithful irreducible quotient is semisimple, in the exact literal
submodule convention used by the B.5.1 recursion. -/
theorem semisimple_of_irreducible (hi : IsIrreducible ρ) : IsSemisimpleRepresentation ρ := by
  let := hi
  let : IsSimpleModule (ZMod 2)[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp hi
  exact (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mpr inferInstance


variable {H : Type*} [Group H] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {σ : Representation (ZMod 2) H W}

/-- An actual action equivalence identifies the invariant-subspace lattices. -/
noncomputable def actionSubrepresentationOrderIso (e : ActionEquiv ρ σ) :
    Subrepresentation ρ ≃o Subrepresentation σ where
  toFun S := ⟨S.toSubmodule.map e.linearEquiv.toLinearMap, by
    rintro g w ⟨v,hv,rfl⟩
    refine ⟨ρ (e.groupEquiv.symm g) v, S.apply_mem_toSubmodule _ hv, ?_⟩
    change e.linearEquiv (ρ (e.groupEquiv.symm g) v) = σ g (e.linearEquiv v)
    rw [e.intertwines,e.groupEquiv.apply_symm_apply]⟩
  invFun T := ⟨T.toSubmodule.comap e.linearEquiv.toLinearMap, by
    intro g v hv
    change e.linearEquiv (ρ g v) ∈ T
    rw [e.intertwines]
    exact T.apply_mem_toSubmodule _ hv⟩
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.comap_map_eq_of_injective e.linearEquiv.injective S.toSubmodule
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    exact Submodule.map_comap_eq_of_surjective e.linearEquiv.surjective T.toSubmodule
  map_rel_iff' := by
    intro S T
    exact Submodule.map_le_map_iff_of_injective e.linearEquiv.injective _ _

theorem semisimple_of_actionEquiv (e : ActionEquiv ρ σ)
    (hs : IsSemisimpleRepresentation σ) : IsSemisimpleRepresentation ρ := by
  let := hs
  exact (actionSubrepresentationOrderIso ρ e).symm.complementedLattice

theorem semisimple_of_homogeneous (hh : IsHomogeneousAction ρ) :
    IsSemisimpleRepresentation ρ := by
  obtain ⟨r,hr,S,hi,f,hf⟩ := hh
  let := hi
  let τ := repeated S.toRepresentation r
  let p (i : Fin r) : τ.IntertwiningMap S.toRepresentation :=
    (LinearMap.proj i).intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  let j : τ.asModule →ₗ[(ZMod 2)[G]] (Fin r → S.toRepresentation.asModule) :=
    LinearMap.pi (fun i => IntertwiningMap.equivLinearMapAsModule _ _ (p i))
  have hj : Function.Injective j := fun _ _ h => h
  have hτ : IsSemisimpleRepresentation τ :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (IsSemisimpleModule.of_injective j hj)
  exact semisimple_of_actionEquiv ρ ⟨MulEquiv.refl G,f,hf⟩ hτ


variable {τ : Representation (ZMod 2) G W}

theorem semisimple_prod (hρ : IsSemisimpleRepresentation ρ)
    (hτ : IsSemisimpleRepresentation τ) : IsSemisimpleRepresentation (ρ.prod τ) := by
  let : IsSemisimpleModule (ZMod 2)[G] ρ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hρ
  let : IsSemisimpleModule (ZMod 2)[G] τ.asModule :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mp hτ
  have hsum := IsSemisimpleModule.sup
    (IsSemisimpleModule.range (LinearMap.inl (ZMod 2)[G] ρ.asModule τ.asModule))
    (IsSemisimpleModule.range (LinearMap.inr (ZMod 2)[G] ρ.asModule τ.asModule))
  rw [LinearMap.sup_range_inl_inr] at hsum
  let : IsSemisimpleModule (ZMod 2)[G] (ρ.asModule × τ.asModule) :=
    IsSemisimpleModule.congr Submodule.topEquiv.symm
  let p : (ρ.prod τ).IntertwiningMap ρ :=
    (LinearMap.fst (ZMod 2) V W).intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  let q : (ρ.prod τ).IntertwiningMap τ :=
    (LinearMap.snd (ZMod 2) V W).intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)
  let f : (ρ.prod τ).asModule →ₗ[(ZMod 2)[G]] (ρ.asModule × τ.asModule) :=
    (IntertwiningMap.equivLinearMapAsModule _ _ p).prod
      (IntertwiningMap.equivLinearMapAsModule _ _ q)
  have hf : Function.Injective f := fun _ _ h => h
  exact (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
    (IsSemisimpleModule.of_injective f hf)

theorem semisimple_of_naturalPlusDual {d : ℕ} (hd : 2 ≤ d)
    (hn : IsNaturalPlusDual ρ d) : IsSemisimpleRepresentation ρ := by
  obtain ⟨e⟩ := hn
  apply semisimple_of_actionEquiv ρ e
  apply semisimple_prod
  · exact semisimple_of_irreducible _ (ExtensionConsequences.linearNatural_irreducible _ hd)
  · exact semisimple_of_irreducible _ (ExtensionConsequences.irreducible_of_equiv
      (dualNaturalEquiv d) (ExtensionConsequences.linearNatural_irreducible _ hd))


/-- Clause (3) of the strict induction conclusion already forces semisimplicity
on a fully moved, fixed-point-free actual component action. -/
theorem semisimple_of_source_conclusion {L : Subgroup G}
    (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hm : moved ρ L = ⊤) (hz : fixedSpace ρ L = ⊥) :
    IsSemisimpleRepresentation (ρ.comp L.subtype) := by
  let S := c.sectionData
  have hs : S.space.toSubmodule = ⊤ := S.space_eq.trans hm
  let E : S.space.toSubmodule ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective S.space.toSubmodule.subtype
      ⟨Subtype.val_injective,fun v => ⟨⟨v,hs ▸ Submodule.mem_top⟩,rfl⟩⟩
  let e : ActionEquiv (S.space.toRepresentation.comp L.subtype) (ρ.comp L.subtype) :=
    ⟨MulEquiv.refl L,E,fun _ _ => rfl⟩
  apply semisimple_of_actionEquiv _ (ExtensionConsequences.actionSymm e)
  rcases c.clause_three with hh | ⟨d,hd,hn⟩
  · have hS : Representation.invariants (S.space.toRepresentation.comp L.subtype) = ⊥ :=
      ExtensionConsequences.invariants_of_equiv e hz
    apply semisimple_of_actionEquiv _
      (ExtensionConsequences.actionSymm (ExtensionConsequences.movedQuotientEquiv S hS))
    exact semisimple_of_homogeneous _ hh
  · exact semisimple_of_naturalPlusDual _ (by omega) hn


/-- Coinvariants use precisely the source commutator span. -/
theorem coinvariants_eq_moved (L : Subgroup G) :
    Coinvariants.ker (ρ.comp L.subtype) = moved ρ L := by
  apply congrArg (Submodule.span (ZMod 2))
  ext v
  constructor
  · rintro ⟨⟨g,w⟩,rfl⟩
    exact ⟨g.val,g.property,w,Submodule.mem_top,rfl⟩
  · rintro ⟨g,hg,w,_,rfl⟩
    exact ⟨(⟨g,hg⟩,w),rfl⟩

/-- The strict conclusion on the literal component/offender overgroup gives
semisimplicity for the same original component action. -/
theorem local_semisimple_of_conclusion (L A : Subgroup G)
    (hc : LocalSourceConclusion ρ L A)
    (hm : Coinvariants.ker (ρ.comp L.subtype) = ⊤)
    (hz : Representation.invariants (ρ.comp L.subtype) = ⊥) :
    IsSemisimpleRepresentation (ρ.comp L.subtype) := by
  obtain ⟨c⟩ := hc
  let H := L ⊔ A
  let C := L.subgroupOf H
  let σ := ρ.comp H.subtype
  let e : ActionEquiv (σ.comp C.subtype) (ρ.comp L.subtype) :=
    ⟨Subgroup.subgroupOfEquivOfLe (show L ≤ H from le_sup_left),
      LinearEquiv.refl _ _,fun _ _ => rfl⟩
  have hspan : moved σ C = Coinvariants.ker (ρ.comp L.subtype) := by
    apply congrArg (Submodule.span (ZMod 2))
    ext v
    constructor
    · rintro ⟨g,hg,w,_,rfl⟩
      exact ⟨(⟨g.val,hg⟩,w),rfl⟩
    · rintro ⟨⟨g,w⟩,rfl⟩
      exact ⟨⟨g.val,(show L ≤ H from le_sup_left) g.property⟩,g.property,w,Submodule.mem_top,rfl⟩
  have hs : IsSemisimpleRepresentation (σ.comp C.subtype) :=
    semisimple_of_source_conclusion σ c (hspan.trans hm)
      (ExtensionConsequences.invariants_of_equiv e hz)
  exact semisimple_of_actionEquiv _ (ExtensionConsequences.actionSymm e) hs

/-- The original binary source flag has semisimple proper nonzero terms by
strict dimension induction. This is the actual maximal-submodule step on p.101. -/
theorem binary_source_flag_semisimple [Finite G] [FiniteDimensional (ZMod 2) V]
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
    IsSemisimpleRepresentation ((f.chain i).toRepresentation.comp (generalizedFitting G).subtype) := by
  obtain ⟨_,hm,hz,hc⟩ := binary_source_flag_recursion ρ hK earlier ih hsq hf hcore
    hd mark f A hA hgen hm hi0 hi
  exact local_semisimple_of_conclusion _ _ _ hc hm hz

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
