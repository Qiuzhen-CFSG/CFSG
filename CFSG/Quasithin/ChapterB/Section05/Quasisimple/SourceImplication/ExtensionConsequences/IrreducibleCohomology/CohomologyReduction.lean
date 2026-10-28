module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Reduction
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.CentralFixedPointCohomology
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.Representation.SL5TenDimensionalFirstCohomology
public import Theory.Representation.SL5TenDimensionalFirstCohomology.Classification
public import Theory.Representation.SL5TenDimensionalFirstCohomology.ExteriorVanishing
public import Theory.Representation.BinaryAlternatingNaturalCohomology
public import Theory.Representation.BinaryPermutationNaturalDuality
public import Theory.SpecificGroups.PSL3.OuterSolvable.Actions
public import Mathlib.FieldTheory.Finite.Trace
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.MovedSection
public import Theory.AtlasPort.LinearGroups.G2.Order

/-!
# Cohomology deductions for the actual irreducible moved section

The literal projection [V,L] → [V,L]/C_[V,L](L) is a perfect central
cover, by the commutator-generation clause of Irr⁺. Vanishing of dual H¹
makes this projection injective; vanishing of H¹ then gives a fixed
supplement. This connects the concrete cohomology calculations to the
original moved and fixed spaces, without any splitting hypothesis.

The odd alternating natural, four-dimensional A7, ten-dimensional SL5,
binary higher-linear, and larger-field SL3 rows all split. The SL5 proof
uses the exhaustive exterior-model classification and both cocycle
calculations. The SL3 dual comparison uses field trace and inverse
transpose. A nonidentity central element handles the triple cover without
using the incorrect projective-line convention in its legacy offender field.

The complete action list is thereby reduced to NonsplitNatural plus the
marked natural Sp4(2)' endpoint. Identifying that endpoint with the actual
A6 natural module is separate. The dual-extension offender calculations
needed to shorten the list in B.5.1(5) are also separate.

At L3(2), the retained outer-extension alternative forces G = L: normality
and a Sylow supplement give 2-power index, incompatible with the orders of
S5,...,S8 and G2(2). No cohomology, covering, or earlier-source implication
is left as a parameter of the results in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), I.1.5–6,
printed p.408, and B.5.1(2),(5), printed pp.99 and 102–103. The elementary
cover and trace arguments also occur in the repository's Chapter13
CentralExclusion.Cohomology and RankTwo.FieldDual/FieldGraph developments;
they are specialized here to avoid an upward chapter dependency.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
universe u v w z
variable {G : Type u} {H : Type v} [Group G] [Group H]
  {V : Type w} {W : Type z} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

private noncomputable def dualActionEquiv (e : ActionEquiv ρ σ) : ActionEquiv ρ.dual σ.dual where
  groupEquiv := e.groupEquiv
  linearEquiv := e.linearEquiv.symm.dualMap
  intertwines g f := by
    ext w
    change f (ρ g⁻¹ (e.linearEquiv.symm w)) = f (e.linearEquiv.symm (σ (e.groupEquiv g)⁻¹ w))
    congr 1
    apply e.linearEquiv.injective
    rw [e.intertwines, e.linearEquiv.apply_symm_apply, e.linearEquiv.apply_symm_apply,
      e.groupEquiv.map_inv]

private noncomputable def relabelActionEquiv (e : G ≃* H) :
    ActionEquiv ρ (ρ.comp e.symm.toMonoidHom) where
  groupEquiv := e
  linearEquiv := LinearEquiv.refl _ _
  intertwines g v := by change ρ g v = ρ (e.symm (e g)) v; rw [e.symm_apply_apply]

noncomputable def markedRestriction {L A : Subgroup G} {M : Subgroup H}
    (e : MarkedActionEquiv ρ A L σ M) : ActionEquiv (ρ.comp L.subtype) (σ.comp M.subtype) where
  groupEquiv := e.subgroupEquiv
  linearEquiv := e.action.linearEquiv
  intertwines g v := by
    have he := e.action.intertwines ⟨g, e.contained g.property⟩ v
    rw [e.compatible] at he
    exact he

private theorem irreducible_dual [FiniteDimensional (ZMod 2) V]
    [IsIrreducible ρ] : IsIrreducible ρ.dual := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  refine ⟨fun W => ?_⟩
  let U : Subrepresentation ρ :=
    { toSubmodule := W.toSubmodule.dualCoannihilator
      apply_mem_toSubmodule g v hv := by
        rw [Submodule.mem_dualCoannihilator] at hv ⊢
        intro f hf
        have h := hv (ρ.dual g⁻¹ f) (W.apply_mem_toSubmodule g⁻¹ hf)
        simpa only [dual_apply, Module.Dual.transpose_apply, LinearMap.comp_apply, inv_inv] using h }
  have hd : U.toSubmodule.dualAnnihilator = W.toSubmodule :=
    Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases eq_bot_or_eq_top U with h | h
  · right
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_bot
  · left
    apply Subrepresentation.toSubmodule_injective
    rw [← hd, h]
    exact Submodule.dualAnnihilator_top

private theorem faithful_dual (hf : Function.Injective ρ) : Function.Injective ρ.dual := by
  intro g h he
  apply inv_injective
  apply hf
  ext v
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp
  intro f
  have hh := congrArg (fun t : Module.End (ZMod 2) (Module.Dual (ZMod 2) V) => t f v) he
  change f (ρ g⁻¹ v) = f (ρ h⁻¹ v) at hh
  simpa only [map_sub] using sub_eq_zero.mpr hh

private theorem cover_injective_of_vanishing [Finite G]
    [FiniteDimensional (ZMod 2) V] [FiniteDimensional (ZMod 2) W]
    {τ : Representation (ZMod 2) G W} (p : τ.IntertwiningMap ρ) (hp : IsCover p)
    [Subsingleton (H1 ρ.dual)] : Function.Injective p := by
  let : FiniteDimensional (ZMod 2) (Module.Dual (ZMod 2) (cocycles ρ.dual)) :=
    Subspace.instModuleDualFiniteDimensional
  obtain ⟨q, hq, hqp⟩ := exists_universalCover_quotient p hp
  have hu : Function.Injective (universalCoverProjection ρ) := by
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    rw [finrank_ker_universalCoverProjection]
    exact Module.finrank_zero_of_subsingleton
  intro x y hxy
  obtain ⟨a, rfl⟩ := hq x
  obtain ⟨b, rfl⟩ := hq y
  exact congrArg q (hu (by rw [← hqp, ← hqp, hxy]))

private noncomputable def movedProjection {L : Subgroup G} (s : MovedSection ρ L) :
    Representation.IntertwiningMap (s.space.toRepresentation.comp L.subtype) (s.action.comp L.subtype) :=
  s.central.toSubmodule.mkQ.intertwiningMap_of_isIntertwiningMap _ _ (fun _ _ => rfl)

private theorem movedProjection_isCover {L : Subgroup G} (s : MovedSection ρ L)
    (hi : IsIrrPlus ρ L s.space.toSubmodule) : IsCover (movedProjection s) := by
  refine ⟨Submodule.mkQ_surjective _, ?_, ?_⟩
  · intro v hv g
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hv
    rw [s.central_eq] at hmem
    exact hmem g
  · let τ := s.space.toRepresentation.comp L.subtype
    have hm : s.space.toSubmodule ≤ (Coinvariants.ker τ).map s.space.toSubmodule.subtype := by
      conv_lhs => rw [← hi.choose_spec.1]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, hg, v, hv, rfl⟩
      exact ⟨τ ⟨g, hg⟩ ⟨v, hv⟩ - ⟨v, hv⟩, Coinvariants.sub_mem_ker _ _, rfl⟩
    apply top_unique
    intro v _
    obtain ⟨w, hw, he⟩ := hm v.property
    rwa [show w = v from Subtype.ext he] at hw

/-- Vanishing for the literal central quotient and its dual splits the moved
space off the fixed space. Both uses of cohomology are on the original L-action. -/
theorem moved_isCompl_of_cohomology [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    [Subsingleton (H1 (s.action.comp L.subtype))]
    [Subsingleton (H1 (Representation.dual (s.action.comp L.subtype)))] :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  have hp := cover_injective_of_vanishing (movedProjection s) (movedProjection_isCover s hi)
  have hd : Disjoint s.space.toSubmodule (fixedSpace ρ L) := by
    rw [Submodule.disjoint_def]
    intro v hv hc
    have hz : movedProjection s ⟨v, hv⟩ = 0 := by
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      rw [s.central_eq]
      intro g
      exact Subtype.ext (hc g)
    exact congrArg Subtype.val (hp (hz.trans (map_zero _).symm))
  let e : ActionEquiv (s.space.toRepresentation.comp L.subtype) (s.action.comp L.subtype) :=
    ⟨MulEquiv.refl _, LinearEquiv.ofBijective (movedProjection s).toLinearMap
      ⟨hp, Submodule.mkQ_surjective _⟩, fun _ _ => rfl⟩
  let U : Subrepresentation (ρ.comp L.subtype) :=
    ⟨s.space.toSubmodule, fun g _ hv => s.space.apply_mem_toSubmodule g hv⟩
  let : Subsingleton (H1 U.toRepresentation) := e.H1_subsingleton
  have ht : HasTrivialQuotient U := by
    intro g v
    change ρ g v - v ∈ s.space.toSubmodule
    rw [s.space_eq]
    exact Submodule.subset_span ⟨g, g.property, v, Submodule.mem_top, rfl⟩
  refine ⟨hd, codisjoint_iff.mpr (top_unique ?_)⟩
  intro v _
  exact (extensionClass_eq_zero_iff U ht v).mp (Subsingleton.elim _ _)

/-- The quotient with nontrivial center is excluded by actual central-element
cohomology, independently of any offender clause or dimension convention. -/
theorem moved_isCompl_of_central [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IrreducibleAlternative L s)
    (z : L) (hz : z ∈ center L) (hzn : z ≠ 1) :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let := hi.irreducible
  have hf : Function.Injective (s.action.comp L.subtype) := hi.faithful.comp Subtype.val_injective
  let := subsingleton_H1_of_faithful_irreducible_central _ hf z hz hzn
  let := irreducible_dual (ρ := s.action.comp L.subtype)
  let := subsingleton_H1_of_faithful_irreducible_central _ (faithful_dual hf) z hz hzn
  exact moved_isCompl_of_cohomology s hi.irrPlus

/-- In particular the genuine six-dimensional triple-cover row splits. Only
its nontrivial central group is used, never its legacy offender specification. -/
theorem tripleSix_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IrreducibleAlternative L s)
    (a : TripleSixAction s.action L) : IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let z := a.centerEquiv.symm (Multiplicative.ofAdd (1 : ZMod 3))
  apply moved_isCompl_of_central s hi z.val z.property
  intro hz
  have he : a.centerEquiv z = 1 := by rw [show z = 1 from Subtype.ext hz, map_one]
  have hz' : (Multiplicative.ofAdd (1 : ZMod 3)) = 1 :=
    (a.centerEquiv.apply_symm_apply _).symm.trans he
  exact one_ne_zero (show (1 : ZMod 3) = 0 from hz')

private theorem a7_vanishing [FiniteDimensional (ZMod 2) V]
    (e : G ≃* alternatingGroup (Fin 7)) [IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) V = 4) : Subsingleton (H1 ρ) := by
  let a := relabelActionEquiv (ρ := ρ) e
  let := irreducible_of_equiv (actionSymm a) inferInstance
  let := Module.finrank_zero_iff.mp
    (binaryAlternatingSeven_finrank_H1_eq_zero_of_irreducible_four (ρ.comp e.symm.toMonoidHom) hd)
  exact a.H1_subsingleton

/-- Every actual four-dimensional A7 row splits, for either dual orientation. -/
theorem alternatingSeven_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IrreducibleAlternative L s)
    (e : L ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 4) :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let := hi.irreducible
  let := a7_vanishing (ρ := s.action.comp L.subtype) e hd
  let := irreducible_dual (ρ := s.action.comp L.subtype)
  let := a7_vanishing (ρ := (Representation.dual (s.action.comp L.subtype))) e (by
    rw [Subspace.dual_finrank_eq]; exact hd)
  exact moved_isCompl_of_cohomology s hi.irrPlus

private theorem sl5_ten_vanishing [FiniteDimensional (ZMod 2) V]
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) [IsIrreducible ρ]
    (hd : Module.finrank (ZMod 2) V = 10) : Subsingleton (H1 ρ) := by
  let a := relabelActionEquiv (ρ := ρ) e
  let := irreducible_of_equiv (actionSymm a) inferInstance
  let := SL5TenDimensional.h1_subsingleton_of_model_identification (ρ.comp e.symm.toMonoidHom)
    (SL5TenDimensional.Classification.identification_of_finrank_ten (ρ.comp e.symm.toMonoidHom) hd)
    SL5TenDimensional.exteriorSquare_h1_subsingleton SL5TenDimensional.exteriorCube_h1_subsingleton
  exact a.H1_subsingleton

/-- The actual ten-dimensional SL5 row is excluded using the proved exhaustive
module classification and both concrete exterior-power cohomology calculations. -/
theorem exteriorFive_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IrreducibleAlternative L s)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hd : Module.finrank (ZMod 2) (s.space.toSubmodule ⧸ s.central.toSubmodule) = 10) :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let := hi.irreducible
  let := sl5_ten_vanishing (ρ := s.action.comp L.subtype) e hd
  let := irreducible_dual (ρ := s.action.comp L.subtype)
  let := sl5_ten_vanishing (ρ := (Representation.dual (s.action.comp L.subtype))) e (by
    rw [Subspace.dual_finrank_eq]; exact hd)
  exact moved_isCompl_of_cohomology s hi.irrPlus

/-- Transport the two vanishing assertions through the same actual action
identification, then apply them to the literal central quotient. -/
theorem moved_isCompl_of_equiv [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (e : ActionEquiv (s.action.comp L.subtype) σ)
    [Subsingleton (H1 σ)] [Subsingleton (H1 σ.dual)] :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let := e.H1_subsingleton
  let := (dualActionEquiv e).H1_subsingleton
  exact moved_isCompl_of_cohomology s hi

/-- The natural binary SL4 and SL5 rows admit no nonsplit central attachments. -/
theorem binaryLinear_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    {d : ℕ} (hd : 4 ≤ d)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural BinaryField.two d)) :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let := H1_linearNatural_subsingleton hd
  let := (dualNaturalEquiv d).H1_subsingleton
  exact moved_isCompl_of_equiv s hi e

private theorem alternating_odd_vanishing {n : ℕ} (hn : 3 ≤ n) (ho : Odd n) :
    Subsingleton (H1 (alternatingNatural n)) := by
  apply (Module.finrank_zero_iff (R := ZMod 2)).mp
  exact BinaryPermutation.alternatingNatural_finrank_H1_eq_zero_of_odd
    (Fin n) (by simpa using hn) (by simpa using ho)

private noncomputable def alternatingSelfDual {n : ℕ} (hn : 0 < n) :
    ActionEquiv (alternatingNatural n) (Representation.dual (alternatingNatural n)) := by
  let : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  exact ⟨MulEquiv.refl _, BinaryPermutation.naturalDualEquiv (Fin n),
    fun g v => BinaryPermutation.naturalDualEquiv_equivariant (Fin n) g.val v⟩

/-- The natural A5 and A7 constituents split, including those specified by
marked symmetric extensions in B.4.2. -/
theorem symmetricOdd_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    {n : ℕ} (hn : n = 5 ∨ n = 7)
    (e : MarkedActionEquiv s.action (offenderSubgroup s.action) L
      (BinaryPermutation.naturalRepresentation (Fin n)) (alternatingGroup (Fin n))) :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  have hlarge : 3 ≤ n := by rcases hn with rfl | rfl <;> decide
  have hodd : Odd n := by rcases hn with rfl | rfl <;> decide
  let := alternating_odd_vanishing hlarge hodd
  let := (actionSymm (alternatingSelfDual (by omega : 0 < n))).H1_subsingleton
  exact moved_isCompl_of_equiv (σ := alternatingNatural n) s hi (markedRestriction e)

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
private noncomputable def linearThreeGraphDual (F : BinaryField) :
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

/-- Larger-field natural SL3 rows split. The dual vanishing uses the trace
comparison, so there is no unproved self-duality or prime-field convention. -/
theorem linearThree_large_isCompl [Finite G] [FiniteDimensional (ZMod 2) V]
    {L : Subgroup G} (s : MovedSection ρ L) (hi : IsIrrPlus ρ L s.space.toSubmodule)
    (F : BinaryField) (hF : 1 < F.degree)
    (e : ActionEquiv (s.action.comp L.subtype) (linearNatural F 3)) :
    IsCompl s.space.toSubmodule (fixedSpace ρ L) := by
  let := H1_three_large F hF
  let := (actionSymm (linearThreeGraphDual F)).H1_subsingleton
  exact moved_isCompl_of_equiv s hi e

/-- The cohomology calculation reduces the complete B.4.2 list to exactly the
B.5.1 natural list and its marked Sp4(2)' endpoint. The latter still needs the
actual natural Sp4(2)'–A6 identification; a group tag is not used in its place. -/
theorem nonsplitNatural_or_symplecticTwo [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IrreducibleAlternative L s)
    (hn : ¬ IsCompl s.space.toSubmodule (fixedSpace ρ L)) :
    NonsplitNatural (s.action.comp L.subtype) ∨
      Nonempty (ActionEquiv (s.action.comp L.subtype) (symplecticDerivedNatural (k := ZMod 2) 2)) := by
  let := h.finite_module
  cases hi.source with
  | linearTwo F _ e _ _ => exact Or.inl (.linearTwo F ⟨e⟩)
  | linearThree F _ e _ =>
    by_cases hF : 1 < F.degree
    · exact False.elim (hn (linearThree_large_isCompl s hi.irrPlus F hF e))
    · have he : F.degree = 1 := by have h := F.degree_pos; omega
      let q := degreeOneNaturalEquiv F he 3
      exact Or.inl (.linearThree ⟨⟨e.groupEquiv.trans q.groupEquiv,
        e.linearEquiv.trans q.linearEquiv, fun g v =>
          (congrArg q.linearEquiv (e.intertwines g v)).trans (q.intertwines _ _)⟩⟩)
  | symplectic F _ _ e _ => exact Or.inl (.symplectic F ⟨e⟩)
  | symplecticTwo e _ => exact Or.inr ⟨markedRestriction e⟩
  | g2 F _ _ e _ _ => exact Or.inl (.g2 F ⟨e⟩)
  | g2Two e _ _ => exact Or.inl (.derivedG2 ⟨markedRestriction e⟩)
  | symmetric n hn' e _ _ => exact False.elim (hn (symmetricOdd_isCompl s hi.irrPlus hn' e))
  | alternatingSix _ e _ _ => exact Or.inl (.alternatingSix ⟨e⟩)
  | alternatingSeven _ _ e hd _ _ => exact False.elim (hn (alternatingSeven_isCompl s hi e hd))
  | tripleSix _ a _ => exact False.elim (hn (tripleSix_isCompl s hi a))
  | binaryLinear d hd _ e _ =>
    exact False.elim (hn (binaryLinear_isCompl s hi.irrPlus (by rcases hd with rfl | rfl <;> decide) e))
  | orthogonalSix _ _ e _ _ => exact Or.inl (.alternatingEight ⟨e⟩)
  | symmetricEight _ e _ => exact Or.inl (.alternatingEight ⟨markedRestriction e⟩)
  | exteriorFive _ _ e hd _ _ => exact False.elim (hn (exteriorFive_isCompl s hi e hd))


/-- The whole-actor conclusion at L3(2) uses the actual outer-extension list.
A normal Sylow supplement has 2-power index, whereas none of S5,...,S8 or
G2(2) has a subgroup of order 168 with such an index. -/
theorem linearThree_eq_top [Finite G]
    {K : CFSG.Quasithin.GroupClass.{u}} {L : Subgroup G}
    (h : QuasisimpleSourceHypothesis ρ K L) (s : MovedSection ρ L)
    (hi : IrreducibleAlternative L s)
    (he : Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2))) : L = ⊤ := by
  rcases hi.extension with hL | ⟨hsup, hout⟩
  · exact hL
  let := h.quasisimple
  let : L.Normal := component_normal_of_fitting_eq_sup_center L h.fitting
  obtain ⟨e⟩ := he
  have hcard : Nat.card L = 168 := by
    rw [Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv]
    exact Matrix.PSL3Two.card_SL
  let T : Sylow 2 G := Classical.choice inferInstance
  obtain ⟨m, hm⟩ := T.isPGroup'.exists_card_eq
  have hindex : L.index ∣ 2 ^ m := by
    rw [← hm]
    have htop := hsup T
    have hd := L.relIndex_dvd_card (T : Subgroup G)
    rwa [← Subgroup.relIndex_sup_left, htop, Subgroup.relIndex_top_right] at hd
  have hno : ¬ 3 ∣ L.index := by
    intro hthree
    have hp : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow (hthree.trans hindex)
    norm_num at hp
  have hmul := L.index_mul_card
  rw [hcard] at hmul
  unfold OuterNaturalAction at hout
  rcases hout with ⟨n, h5, h8, ⟨a⟩⟩ | ⟨a⟩
  · have hc : Nat.card G = n.factorial := by
      rw [Nat.card_congr a.groupEquiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm,
        Fintype.card_fin]
    rw [hc] at hmul
    interval_cases n <;> norm_num at hmul
    all_goals exfalso; apply hno; omega
  · obtain ⟨a⟩ := a
    have hc : Nat.card G = 12096 := by
      rw [Nat.card_congr a.groupEquiv.toEquiv, Atlas.G2.card_Model,
        Nat.card_eq_fintype_card, ZMod.card]
      norm_num
    rw [hc] at hmul
    exfalso
    apply hno
    omega

end CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
