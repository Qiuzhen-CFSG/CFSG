module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.Reduction
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FactorExtraction.EarlierSources
public import Theory.Representation.GeneralLinearNatural

/-!
# The binary natural upper extension on the literal fixed quotient

Suppose [V,D] is an actual natural SL₃(2)-module and does not supplement
C_V(D). Its zero fixed space makes it disjoint from C_V(D), so its image
in the literal quotient V/C_V(D) remains natural with the same marking.
Every displacement of a quotient-fixed lift lies in both these disjoint
spaces; hence the quotient has no fixed points. Its irreducible moved
submodule then forces indecomposability. The established first-cohomology
bound gives dimension four, and the natural submodule gives faithfulness.

Only after proving these hypotheses do we invoke the full universal
B.4.8(3) implication. The resulting source record retains the actual moved
space, the compatible natural identification, the full-axis offender
equivalence, ratio one and every involution assertion. Faithfulness and
the FF property of the original action need not be assumed again: the
actual natural moved action already suffices for this local construction.

`classified_factor_module` applies the construction to the precise binary
branch of `classified_factor_or_binary`. The earlier B.4.8(3) parameter
remains assigned to qt-b-04-natural-extensions, with its final discharge
owned by general-classification assembly. This module assumes no universal
classifier or rank-one extraction theorem.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.8(3)–(4),
printed p.91; B.5.1(5), p.99; B.5.8 and B.5.11, pp.106 and 109.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction.BinaryUpper
open QuasisimpleSource QuasisimpleSource.ExtensionConsequences
open ComponentReduction.ProductGeometry
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) D V}

/-- The full quotient image, retaining exactly the subtype used by `SourceFactorCase`. -/
noncomputable abbrev space (ρ : Representation (ZMod 2) D V) :
    Subrepresentation (fixed ρ).quotientRepresentation :=
  (fixed ρ).quotientImage (⊤ : Subrepresentation ρ)
/-- Its literal action restricted to the full subgroup of the original actor. -/
noncomputable abbrev action (ρ : Representation (ZMod 2) D V) :
    Representation (ZMod 2) (⊤ : Subgroup D) (space ρ).toSubmodule :=
  (space ρ).toRepresentation.comp (⊤ : Subgroup D).subtype

/-- The original quotient map, with codomain the required quotient image. -/
noncomputable def projection (ρ : Representation (ZMod 2) D V) :
    V →ₗ[ZMod 2] (space ρ).toSubmodule where
  toFun v := ⟨ρ.invariants.mkQ v, ⟨v, Submodule.mem_top, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem projection_surjective : Function.Surjective (projection ρ) := by
  rintro ⟨q, v, hv, rfl⟩
  exact ⟨v, rfl⟩

theorem projection_ker : (projection ρ).ker = ρ.invariants := by
  ext v
  change projection ρ v = 0 ↔ v ∈ ρ.invariants
  rw [← Subtype.val_inj]
  exact Submodule.Quotient.mk_eq_zero _

theorem projection_equivariant (g : (⊤ : Subgroup D)) (v : V) :
    projection ρ (ρ g v) = action ρ g (projection ρ v) := rfl

/-- The image of the actual moved space inside the required quotient carrier. -/
noncomputable def naturalSpace (s : MovedSection ρ ⊤) : Subrepresentation (action ρ) where
  toSubmodule := s.space.toSubmodule.map (projection ρ)
  apply_mem_toSubmodule g := by
    rintro _ ⟨v,hv,rfl⟩
    exact ⟨ρ g v, s.space.apply_mem_toSubmodule g hv, rfl⟩

theorem naturalSpace_moved (s : MovedSection ρ ⊤) :
    (naturalSpace s).toSubmodule = moved (action ρ) ⊤ := by
  change s.space.toSubmodule.map (projection ρ) = _
  rw [s.space_eq]
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    change projection ρ (ρ g v - v) ∈ moved (action ρ) ⊤
    rw [map_sub]
    exact Submodule.subset_span ⟨(⟨g, mem_top _⟩ : (⊤ : Subgroup D)), mem_top _,
      projection ρ v, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    obtain ⟨w,rfl⟩ := projection_surjective v
    exact ⟨ρ g w - w, Submodule.subset_span ⟨g, mem_top _,w,Submodule.mem_top,rfl⟩,
      (projection ρ).map_sub _ _⟩

theorem natural_disjoint (s : MovedSection ρ ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3)) : Disjoint s.space.toSubmodule ρ.invariants := by
  have hz := invariants_of_equiv e
    (linearNatural_invariants BinaryField.two (by decide : 2 ≤ 3))
  apply Submodule.disjoint_def.mpr
  intro v hv hc
  have ht : (⟨v,hv⟩ : s.space.toSubmodule) ∈
      Representation.invariants (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype) :=
    fun g => Subtype.ext (hc g)
  rw [hz] at ht
  exact congrArg Subtype.val ht

/-- Disjointness makes the original quotient projection an isomorphism on the moved space. -/
noncomputable def naturalEquiv (s : MovedSection ρ ⊤)
    (hd : Disjoint s.space.toSubmodule ρ.invariants) :
    s.space.toSubmodule ≃ₗ[ZMod 2] (naturalSpace s).toSubmodule := by
  let f : s.space.toSubmodule →ₗ[ZMod 2] (naturalSpace s).toSubmodule := {
    toFun := fun v => ⟨projection ρ v, ⟨v, v.property, rfl⟩⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  apply LinearEquiv.ofBijective f
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hmem : (v : V) ∈ ρ.invariants := by
      rw [← projection_ker]
      exact congrArg Subtype.val hv
    exact Subtype.ext ((disjoint_iff.mp hd).le ⟨v.property,hmem⟩)
  · rintro ⟨q,v,hv,rfl⟩
    exact ⟨⟨v,hv⟩,rfl⟩

theorem naturalEquiv_equivariant (s : MovedSection ρ ⊤)
    (hd : Disjoint s.space.toSubmodule ρ.invariants) (g : (⊤ : Subgroup D))
    (v : s.space.toSubmodule) :
    naturalEquiv s hd (s.space.toRepresentation g v) =
      (naturalSpace s).toRepresentation g (naturalEquiv s hd v) := rfl

/-- The quotient moved action retains the given natural group identification. -/
noncomputable def naturalAction (s : MovedSection ρ ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3)) :
    ActionEquiv (naturalSpace s).toRepresentation (linearNatural BinaryField.two 3) := by
  let q := naturalEquiv s (natural_disjoint s e)
  let a : ActionEquiv (naturalSpace s).toRepresentation
      (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype) := {
    groupEquiv := MulEquiv.refl _
    linearEquiv := q.symm
    intertwines := by
      intro g v
      apply q.injective
      rw [LinearEquiv.apply_symm_apply]
      exact ((naturalEquiv_equivariant s (natural_disjoint s e) g (q.symm v)).trans
        (congrArg ((naturalSpace s).toRepresentation g) (q.apply_symm_apply v))).symm }
  exact transAction a e

/-- The marking in the offender conclusion is the original natural marking. -/
theorem naturalAction_groupEquiv (s : MovedSection ρ ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3)) :
    (naturalAction s e).groupEquiv = e.groupEquiv := by
  ext g
  rfl

/-- A fixed quotient vector lifts to a fixed vector because its displacements
lie in both the natural moved space and the original fixed space. -/
theorem invariants_eq_bot (s : MovedSection ρ ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3)) : (action ρ).invariants = ⊥ := by
  apply bot_unique
  intro q hq
  obtain ⟨v,rfl⟩ := projection_surjective q
  have hv : v ∈ ρ.invariants := by
    intro g
    apply sub_eq_zero.mp
    apply Submodule.disjoint_def.mp (natural_disjoint s e) (ρ g v - v)
    · rw [s.space_eq]
      exact Submodule.subset_span ⟨g,mem_top _,v,Submodule.mem_top,rfl⟩
    · rw [← projection_ker]
      change projection ρ (ρ g v - v) = 0
      rw [map_sub, projection_equivariant (⟨g,mem_top _⟩ : (⊤ : Subgroup D)), hq]
      exact sub_self _
  change v ∈ (projection ρ).ker
  rwa [projection_ker]

/-- Failure of the fixed supplement contributes exactly one dimension above
the natural three-space, by the proved first-cohomology calculation. -/
theorem dimension [Finite D] [Module.Finite (ZMod 2) V]
    (s : MovedSection ρ ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3))
    (hs : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) :
    Module.finrank (ZMod 2) (space ρ).toSubmodule = 4 := by
  have he := (naturalThree_supplement_or_exceptional s BinaryField.two ⟨e⟩).resolve_left
    (by simpa only [fixedSpace_top] using hs)
  have hh := he.2
  change Module.finrank (ZMod 2) (V ⧸ (s.space.toSubmodule ⊔ fixedSpace ρ ⊤)) = 1 at hh
  rw [fixedSpace_top] at hh
  have hW : Module.finrank (ZMod 2) s.space.toSubmodule = 3 :=
    e.linearEquiv.finrank_eq.trans (show
      Module.finrank (ZMod 2) (Fin 3 → BinaryField.two.Carrier) = 3 from
        Module.finrank_fin_fun (ZMod 2))
  have hsup := s.space.toSubmodule.finrank_sup_add_finrank_inf_eq ρ.invariants
  rw [(natural_disjoint s e).eq_bot, finrank_bot, add_zero, hW] at hsup
  have hquot := (s.space.toSubmodule ⊔ ρ.invariants).finrank_quotient_add_finrank
  have hdim := (projection ρ).finrank_range_add_finrank_ker
  rw [projection_ker, LinearMap.range_eq_top.mpr projection_surjective,
    finrank_top] at hdim
  omega

private theorem eq_bot_of_disjoint_moved {E U : Type*} [Group E]
    [AddCommGroup U] [Module (ZMod 2) U] {σ : Representation (ZMod 2) E U}
    (hz : σ.invariants = ⊥) (A : Subrepresentation σ)
    (hd : Disjoint (moved σ ⊤) A.toSubmodule) : A = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  apply bot_unique
  intro a ha
  have hf : a ∈ σ.invariants := by
    intro g
    apply sub_eq_zero.mp
    exact Submodule.disjoint_def.mp hd (σ g a - a)
      (Submodule.subset_span ⟨g,Subgroup.mem_top _,a,Submodule.mem_top,rfl⟩)
      (A.toSubmodule.sub_mem (A.apply_mem_toSubmodule g ha) ha)
  rwa [hz] at hf

/-- Any invariant summand disjoint from the irreducible moved space is fixed,
and hence zero; therefore the quotient is indecomposable. -/
theorem indecomposable (s : MovedSection ρ ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3)) : IsIndecomposable (action ρ) := by
  let N := naturalSpace s
  let := irreducible_of_equiv (naturalAction s e)
    (linearNatural_irreducible BinaryField.two (by decide : 2 ≤ 3))
  let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
  let : Nontrivial (space ρ).toSubmodule :=
    Function.Injective.nontrivial N.toSubmodule.subtype_injective
  have hn : IsAtom N := Subrepresentation.irreducible_iff_isAtom N |>.mp inferInstance
  refine ⟨inferInstance, fun A B hc => ?_⟩
  by_cases hA : N ≤ A
  · right
    apply eq_bot_of_disjoint_moved (invariants_eq_bot s e) B
    rw [← naturalSpace_moved s]
    exact hc.disjoint.mono_left hA
  · left
    apply eq_bot_of_disjoint_moved (invariants_eq_bot s e) A
    rw [← naturalSpace_moved s]
    have hd := hn.not_le_iff_disjoint.mp hA
    rw [disjoint_iff] at hd ⊢
    exact congrArg Subrepresentation.toSubmodule hd

/-- Faithfulness follows from the actual natural moved submodule. -/
theorem faithful (s : MovedSection ρ ⊤)
    (e : ActionEquiv (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3)) : Function.Injective (action ρ) := by
  let n := naturalAction s e
  intro g h he
  apply n.groupEquiv.injective
  apply specialLinearNatural_injective 3
  apply LinearMap.ext
  intro v
  obtain ⟨w,rfl⟩ := n.linearEquiv.surjective v
  have hw : (naturalSpace s).toRepresentation g w = (naturalSpace s).toRepresentation h w :=
    Subtype.ext (LinearMap.congr_fun he w)
  exact (n.intertwines g w).symm.trans
    ((congrArg n.linearEquiv hw).trans (n.intertwines h w))

/-- The full B.4.8(3) output on the literal fixed quotient. All hypotheses of
the permitted universal earlier-source implication are proved here. -/
theorem source [Finite D] [Module.Finite (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (s : MovedSection ρ ⊤)
    (hn : IsLinearNatural (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      BinaryField.two 3)
    (hs : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) :
    Nonempty (FourDimensionalSource
      (((fixed ρ).quotientImage (⊤ : Subrepresentation ρ)).toRepresentation.comp
        (⊤ : Subgroup D).subtype)) := by
  obtain ⟨e⟩ := hn
  have hd := dimension s e hs
  have hi := indecomposable s e
  obtain ⟨ho,hq,ha⟩ := h48 (⊤ : Subgroup D) _ (action ρ) (faithful s e) hi hd
    (naturalSpace s) (naturalSpace_moved s) (naturalAction s e)
  exact ⟨⟨hd,hi,naturalSpace s,naturalSpace_moved s,naturalAction s e,ho,hq,ha⟩⟩

/-- The nonsupplemented binary branch gives B.5.6(3c), taking the full ambient
module as the required supplement. -/
theorem factor_module [Finite D] [Module.Finite (ZMod 2) V]
    (h48 : EarlierB48Three.{u,v}) (s : MovedSection ρ ⊤)
    (hn : IsLinearNatural (s.space.toRepresentation.comp (⊤ : Subgroup D).subtype)
      BinaryField.two 3)
    (hs : s.space.toSubmodule ⊔ ρ.invariants ≠ ⊤) :
    Nonempty (FactorModuleConclusion ρ) := by
  obtain ⟨h⟩ := source h48 s hn hs
  exact ⟨⟨⊤, top_sup_eq _, .exceptional le_top h⟩⟩

/-- Application to exactly the binary branch returned by the established
rank-one classification reduction. This discharges its upper-extension
obligation in B.5.8 and B.5.11; the earlier B.4.8(3) input remains explicit. -/
theorem classified_factor_module [Finite D] [Nontrivial D]
    (h48 : EarlierB48Three.{u,v}) {K : GroupClass.{u}} (hyp : FFHypothesis K ρ)
    (hr : primeRank 3 D ≤ 1) (h : AdequateAlternative ρ) :
    Nonempty (FactorModuleConclusion ρ) := by
  let := hyp.finite_module
  rcases classified_factor_or_binary hyp hr h with hf | ⟨s,hn,hs⟩
  · exact hf
  · exact factor_module h48 s hn hs

end CFSG.Quasithin.ChapterB.SourceInduction.FactorExtraction.BinaryUpper
