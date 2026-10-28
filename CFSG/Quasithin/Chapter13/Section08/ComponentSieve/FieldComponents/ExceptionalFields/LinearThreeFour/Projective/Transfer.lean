module

public import CFSG.Quasithin.Defs
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.Replacement
public import Theory.Representation.Quotient
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.Quasithin.Rank
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# Faithful irreducible images for the projective L₃(4) exclusion

For a normal simple component L with a two-group quotient, pass from an
invariant Irr⁺ member I to the literal quotient I/C_I(L). The component
survives, hence is isomorphic to its image, and the action kernel centralizes
L. A quadratic actor faithful on L therefore retains its rank. Restriction
and quotient cannot increase its fixed codimension.

The kernel is a two-group because it embeds in G/L. Thus the faithful image
remains SQTK. Its irreducible action kills its two-core, and the actual
component image is its generalized Fitting subgroup. These facts justify the
application of the earlier irreducible representation bound; that bound is
never imposed on the original, potentially reducible module.

The two explicit earlier inputs are the existence and invariant-or-FF
consequence of A.1.42 and F.9.18(4), and the PSL₃(4) consequence of
B.4.2 and B.4.5. In F.9.18(4),
(i) and (ii) give invariance under KT; the natural representations in (iii)
give an FF-module on the central quotient for K. The FF branch below is
excluded using the same irreducible classification bound and the proved
Thompson replacement equivalence q ≤ 1. No assertion here proves those
representation classifications.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
13.8.20, printed p.955 (PDF p.972); F.9.18(2)--(4), pp.325--326;
A.1.40--42, pp.31--32; B.4.2 and B.4.5, pp.86--87. Concrete projective
carriers and their simplicity are reused from the attributed ATLAS port
in the imports.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped ENNReal MatrixGroups

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective
universe u v

/-- Earlier representation classification, specialized to the actual PSL₃(F₄)
component. Both the full actor and the component action have the hypotheses of
B.4.5. The FF alternatives are ruled out by B.4.2; the L₃(4) row of B.4.5 has
quadratic ratio strictly greater than two. To deduce this unconditional
bound from B.4.5, the contrary assumption `q ≤ 2` supplies its cubic-ratio
hypothesis via `q̂ ≤ q`. This is an explicit input, not a claim that Chapter B's
classification has already been formalized. -/
@[expose] def IrreducibleProjectiveBound (κ : GroupClass.{u}) (F : Type v) [Field F] [Finite F] : Prop :=
  Nat.card F = 4 →
  ∀ (X W : Type u) [Group X] [Finite X] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (σ : Representation (ZMod 2) X W) (L : Subgroup X),
    IsSQTK κ X → generalizedFitting X = L → IsQuasisimple L →
    Function.Injective σ → IsIrreducible (σ.comp L.subtype) →
    Nonempty (L ≃* PSL(3, F)) → 2 < quadraticRatio σ


variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- The existence consequence of A.1.42 and F.9.18(4) needed here, on the
actual subspaces and central quotient actions. Choose a member of the source's
Irr⁺(K,U,T), which has the additional homogeneous-component condition in
A.1.40. Cases (i),(ii) are invariant; the natural component representation in
(iii) is an FF-module. This statement only asks for one suitable member; it
does not assert the alternatives for every member of Irr⁺(K,U). -/
@[expose] def InvariantOrFF (ρ : Representation (ZMod 2) G V) (L : Subgroup G) : Prop :=
  ∃ (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I),
    (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I ∨
    IsFFModule (imageRepresentation (centralQuotientRepresentation ρ L I hI.choose))

variable [Finite G] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private noncomputable def factorFixed (L : Subgroup G) [L.Normal] (I : Subrepresentation ρ) :
    Subrepresentation I.toRepresentation where
  toSubmodule := (fixedSpace ρ L).comap I.toSubmodule.subtype
  apply_mem_toSubmodule g v hv :=
    (fixedSpace_stable_of_normal ρ L (mem_top g) v).2 hv

private noncomputable def factor (L : Subgroup G) [L.Normal] (I : Subrepresentation ρ) :
    Representation (ZMod 2) G (centralQuotient ρ L I.toSubmodule) :=
  (factorFixed ρ L I).quotientRepresentation

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem factor_component_irreducible (L : Subgroup G) [L.Normal]
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ L I.toSubmodule) :
    IsIrreducible ((factor ρ L I).comp L.subtype) := by
  exact hI.choose_spec.2

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem central_nontrivial (L : Subgroup G) (I : Submodule (ZMod 2) V)
    (hs : L ≤ subspaceStabilizer ρ I) (hI : IsIrrPlus ρ L I) :
    ¬ (⊤ : Subgroup L) ≤ (actionHom (centralQuotientRepresentation ρ L I hs)).ker := by
  intro hk
  apply hI.not_le_fixedSpace ρ
  rw [← hI.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, hv, rfl⟩
  have hfix := (actionHom_eq_one_iff _ ⟨l, hl⟩).mp (hk (mem_top _))
    (Submodule.Quotient.mk (⟨v, hv⟩ : I))
  exact (Submodule.Quotient.eq ((fixedSpace ρ L).comap I.subtype)).mp hfix


omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem irreducible_of_component (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [IsIrreducible (ρ.comp L.subtype)] : IsIrreducible ρ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp L.subtype) :=
    ⟨S.toSubmodule, fun l _ hv => S.apply_mem_toSubmodule l hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp L.subtype) => U.toSubmodule) h)

private theorem faithful_irreducible_core
    (ρ : Representation (ZMod 2) G V) [IsIrreducible ρ]
    (hf : Function.Injective ρ) : pCore 2 G = ⊥ := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_bot_iff.mp ((normal_p_subgroup_le_ker ρ (pCore 2 G) pCore_isPGroup).trans
    ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le)

private theorem image_structure
    {κ : GroupClass.{u}} (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] [IsQuasisimple L] [IsSimpleGroup L]
    (hG : IsSQTK κ G) (hquot : IsPGroup 2 (G ⧸ L))
    (hsurvive : ¬ L ≤ (actionHom ρ).ker)
    (hirr : IsIrreducible (ρ.comp L.subtype)) :
    ∃ _e : L ≃* actionSubgroup ρ L,
      IsSQTK κ (actionImage ρ) ∧
      generalizedFitting (actionImage ρ) = actionSubgroup ρ L ∧
      IsQuasisimple (actionSubgroup ρ L) ∧
      IsIrreducible ((imageRepresentation ρ).comp (actionSubgroup ρ L).subtype) ∧
      (actionHom ρ).ker ≤ centralizer (L : Set G) := by
  let f := actionHom ρ
  have hfaith : ∀ a ∈ L, (∀ v, ρ a v = v) → a = 1 := by
    have hk : (f.comp L.subtype).ker = ⊥ := by
      rcases (inferInstance : (f.comp L.subtype).ker.Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · exfalso
        apply hsurvive
        intro l hl
        exact (show (⟨l, hl⟩ : L) ∈ (f.comp L.subtype).ker from ht.symm ▸ mem_top _)
    intro a ha hfix
    have he : (f.comp L.subtype) ⟨a, ha⟩ = (f.comp L.subtype) 1 := by
      change f a = f 1
      rw [map_one]
      exact (actionHom_eq_one_iff ρ a).mpr hfix
    exact congrArg Subtype.val ((MonoidHom.ker_eq_bot_iff _).mp hk he)
  let e := faithfulActionEquiv ρ L hfaith
  let D := actionSubgroup ρ L
  let : D.Normal := Subgroup.Normal.map inferInstance f ρ.asGroupHom.rangeRestrict_surjective
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e
  have hDI : IsIrreducible ((imageRepresentation ρ).comp D.subtype) :=
    (irreducible_comp_surjective_iff (f.subgroupMap L) (f.subgroupMap_surjective L)
      ((imageRepresentation ρ).comp D.subtype)).mp hirr
  let := hDI
  let : IsIrreducible (imageRepresentation ρ) := irreducible_of_component _ D
  have hcore := faithful_irreducible_core (imageRepresentation ρ) (imageRepresentation_injective ρ)
  have hquo : IsPGroup 2 (actionImage ρ ⧸ D) := hquot.of_surjective
    (QuotientGroup.map L D f (Subgroup.le_comap_map _ _))
    (QuotientGroup.map_surjective_of_surjective L D f
      (QuotientGroup.mk_surjective.comp ρ.asGroupHom.rangeRestrict_surjective) _)
  have hkerTwo : IsPGroup 2 f.ker := by
    apply hquot.of_injective ((QuotientGroup.mk' L).comp f.ker.subtype)
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    exact hfaith x ((QuotientGroup.eq_one_iff _).mp hx)
      ((actionHom_eq_one_iff ρ x).mp x.property)
  have hSQ : IsSQTK κ (G ⧸ f.ker) := by
    refine ⟨?_, hG.isKGroup.quotient f.ker⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho f.ker hkerTwo).trans
      (hG.stronglyQuasithin p hp ho)
  refine ⟨e, (IsSQTK.equiv (QuotientGroup.quotientKerEquivOfSurjective f
    ρ.asGroupHom.rangeRestrict_surjective)).mp hSQ,
    generalizedFitting_eq_of_quasisimple_two_quotient D hquo hcore,
    inferInstance, hDI, ?_⟩
  have hc : IsComponent G L := ⟨(inferInstance : L.Normal).isSubnormal, inferInstance⟩
  have hcomm := (hc.normal_dichotomy f.ker).resolve_left hsurvive
  exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hcomm)


variable {F : Type v} [Field F] [Finite F] {κ : GroupClass.{u}}

private theorem bound_on_image (hclass : IrreducibleProjectiveBound κ F) (hF : Nat.card F = 4)
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [IsQuasisimple L]
    (hG : IsSQTK κ G) (hfit : generalizedFitting G = L)
    (hf : Function.Injective ρ) (hirr : IsIrreducible (ρ.comp L.subtype))
    (eL : L ≃* PSL(3, F)) : 2 < quadraticRatio (imageRepresentation ρ) := by
  have hfaith : ∀ a ∈ L, (∀ v, ρ a v = v) → a = 1 := by
    intro a _ ha
    apply hf
    apply LinearMap.ext
    simpa only [map_one, Module.End.one_apply] using ha
  let e : G ≃* actionImage ρ := MulEquiv.ofBijective (actionHom ρ)
    ⟨by
      intro x y h
      apply hf
      exact congrArg (imageRepresentation ρ) h,
      ρ.asGroupHom.rangeRestrict_surjective⟩
  let D := actionSubgroup ρ L
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv (faithfulActionEquiv ρ L hfaith)
  apply hclass hF (actionImage ρ) V (imageRepresentation ρ) D
    ((IsSQTK.equiv e).mp hG) _ inferInstance (imageRepresentation_injective ρ) _
    ⟨(faithfulActionEquiv ρ L hfaith).symm.trans eL⟩
  · exact (map_generalizedFitting_equiv e).symm.trans (congrArg (fun N => N.map e.toMonoidHom) hfit)
  · exact (irreducible_comp_surjective_iff ((actionHom ρ).subgroupMap L)
      ((actionHom ρ).subgroupMap_surjective L)
      ((imageRepresentation ρ).comp D.subtype)).mp hirr

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem central_faithful (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [IsSimpleGroup L] (I : Submodule (ZMod 2) V)
    (hs : L ≤ subspaceStabilizer ρ I) (hI : IsIrrPlus ρ L I) :
    Function.Injective (centralQuotientRepresentation ρ L I hs) := by
  let σ := centralQuotientRepresentation ρ L I hs
  have hk : (actionHom σ).ker = ⊥ := by
    rcases (inferInstance : (actionHom σ).ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (central_nontrivial ρ L I hs hI ht.ge).elim
  intro x y he
  apply (MonoidHom.ker_eq_bot_iff _).mp hk
  apply imageRepresentation_injective σ
  exact he


private theorem factor_small_actor (ρ : Representation (ZMod 2) G V)
    (L : Subgroup G) [L.Normal] (I : Subrepresentation ρ)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : ∀ a ∈ A, (∀ v, factor ρ L I a v = v) → a = 1) :
    quadraticRatio (imageRepresentation (factor ρ L I)) ≤ 2 := by
  let σ := factor ρ L I
  have hqσ : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection I.toRepresentation σ
      (factorFixed ρ L I).toSubmodule.mkQ
      (factorFixed ρ L I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ I hq)
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨actionSubgroup σ A, hA.actionSubgroup σ hfaith, ?_, ?_⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
    exact hqσ x hx y hy v
  · rw [fixedCodim_actionSubgroup, actionSubgroup_rank σ A hfaith]
    exact (fixedCodim_le_of_equivariant_surjection I.toRepresentation σ
      (factorFixed ρ L I).toSubmodule.mkQ
      (factorFixed ρ L I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans
        ((fixedCodim_subrepresentation_le ρ I A).trans hc)


/-- The conditional projective exclusion. The quadratic actor is retained on
an actual faithful irreducible section, with SQTK and F* proved for its action
image. The two representation-classification implications remain explicit. -/
theorem projective_exclusion_of_representation_inputs (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
    [L.Normal]
    (hG : IsSQTK κ G) (hquot : IsPGroup 2 (G ⧸ L))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) (hAC : Disjoint A (centralizer (L : Set G)))
    (eL : L ≃* PSL(3, F)) (hF : Nat.card F = 4)
    (hselect : InvariantOrFF ρ L)
    (hclass : IrreducibleProjectiveBound κ F) : False := by
  let : IsSimpleGroup PSL(3, F) := Atlas.psl_simple_high_rank 3 (by decide)
  let : Group.IsPerfect PSL(3, F) := Atlas.psl_perfect 3 (by decide)
  let : IsSimpleGroup L := eL.isSimpleGroup
  let : Group.IsPerfect L := Group.IsPerfect.ofSurjective
    (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp ht)).elim
  let : IsQuasisimple L := {
    simple := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup }
  obtain ⟨I, hI, hcases⟩ := hselect
  rcases hcases with hstable | hFF
  · let S : Subrepresentation ρ := ⟨I, fun g _ hv => (hstable (mem_top g) _).2 hv⟩
    let σ := factor ρ L S
    have hsurvive : ¬ L ≤ (actionHom σ).ker := by
      intro h
      apply central_nontrivial ρ L I hI.choose hI
      intro l _
      apply (actionHom_eq_one_iff _ l).mpr
      exact (actionHom_eq_one_iff σ l).mp (h l.property)
    obtain ⟨e, hSQ, hfit, hqs, hirr, hker⟩ := image_structure σ L hG hquot hsurvive
      (factor_component_irreducible ρ L S hI)
    have hfaithA : ∀ a ∈ A, (∀ v, σ a v = v) → a = 1 := by
      intro a ha hfix
      exact (disjoint_iff_inf_le.mp hAC) ⟨ha,
        hker ((actionHom_eq_one_iff σ a).mpr hfix)⟩
    have hsmall := factor_small_actor ρ L S A hA hq hc hfaithA
    have hlarge := hclass hF (actionImage σ) (centralQuotient ρ L I)
      (imageRepresentation σ) (actionSubgroup σ L) hSQ hfit hqs
      (imageRepresentation_injective σ) hirr ⟨e.symm.trans eL⟩
    exact (not_lt_of_ge hsmall) hlarge
  · let σ := centralQuotientRepresentation ρ L I hI.choose
    let : IsQuasisimple (⊤ : Subgroup L) := IsQuasisimple.of_mulEquiv Subgroup.topEquiv.symm
    have hfitL : generalizedFitting L = ⊤ := top_unique
      (component_le_generalizedFitting L ⊤ ⟨(inferInstance : (⊤ : Subgroup L).Normal).isSubnormal,
        inferInstance⟩)
    have hi : IsIrreducible (σ.comp (⊤ : Subgroup L).subtype) :=
      (irreducible_comp_surjective_iff (⊤ : Subgroup L).subtype
        Subgroup.topEquiv.surjective σ).mpr hI.choose_spec.2
    have hlarge := bound_on_image hclass hF σ ⊤ (hG.subgroup L) hfitL
      (central_faithful ρ L I hI.choose hI) hi (Subgroup.topEquiv.trans eL)
    have hsmall := (isFFModule_iff_quadraticRatio_le_one (imageRepresentation σ)).mp hFF
    exact (not_lt_of_ge (hsmall.trans (by norm_num : (1 : ℝ≥0∞) ≤ 2))) hlarge


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective
