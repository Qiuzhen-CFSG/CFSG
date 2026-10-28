module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Suzuki.NaturalSections.RatioRecognition
public import Theory.Representation.BinaryOffender.AmbientSectionTransport
public import Theory.Representation.BinaryOffender.InvariantAction
public import Theory.Representation.Quotient
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.Quasithin.Rank

/-!
# Recognizing invariant Suzuki central sections

An invariant Irr⁺ section I is kept as the literal I/C_I(K). On the
faithful action image of this quotient, the surviving component is
quasisimple and is the entire generalized Fitting subgroup. Its kernel
meets K trivially: the concrete Suzuki commutant and perfectness imply
Z(K)=1. The remaining kernel is a two-group, so the SQTK hypothesis
passes to the faithful image. The actual quadratic actor gives the
ratio bound there, and the complete B.4.2/B.4.5 implications identify the
natural Suzuki action, including a compatible group marking.

The subgroup version permits the actual relative overgroup K*T* and
transports its literal central quotient back to the ambient action.
Invariance and the Irr⁺ property must still be derived from F.9.18 by
the source assembly. No splitting of I is asserted.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.18(3–4), printed pp.325–326, B.4.2/B.4.5, pp.86–87, and
13.8.16(2), p.953.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open CFSG.Quasithin.Chapter13.Section08.Components.Suzuki
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.SectionRecognition

variable {D : Type*} [Group D] [Group.IsPerfect D] {m : ℕ}

/-- The scalar commutant and perfectness force the Suzuki center to vanish. -/
theorem center_eq_bot_of_equiv_suzuki (e : D ≃* SuzukiMatrixGroup m) : center D = ⊥ := by
  let δ : D →* (BinaryGaloisField (2 * m + 1))ˣ :=
    (Matrix.GeneralLinearGroup.det.comp (SuzukiMatrixSubgroup m).subtype).comp e.toMonoidHom
  let : Group.IsPerfect δ.range := Group.IsPerfect.range δ
  have hdet (x : D) : δ x = 1 := congrArg Subtype.val
    (Subsingleton.elim (⟨δ x, x, rfl⟩ : δ.range) 1)
  apply bot_unique
  intro x hx
  have hc (g : SuzukiMatrixGroup m) (v) :
      natural m (e x) (natural m g v) = natural m g (natural m (e x) v) := by
    have he : e x * g = g * e x := by
      simpa using congrArg e (mem_center_iff.mp hx (e.symm g)).symm
    simpa only [map_mul, Module.End.mul_apply] using
      congrArg (fun z => natural m z v) he
  obtain ⟨a, ha⟩ := commuting_endomorphism_scalar m (natural m (e x)) hc
  have hmat : (e x).val.val = a • (1 : Matrix (Fin 4) (Fin 4) _) := by
    ext i j
    have h := congrFun (ha (Pi.single j 1)) i
    simpa [natural_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, Matrix.one_apply,
      Pi.single_apply, eq_comm] using h
  have ha4 : a ^ 4 = 1 := by
    have h := congrArg Units.val (hdet x)
    change Matrix.det (e x).val.val = 1 at h
    simpa only [hmat, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one] using h
  have ha1 : a = 1 := by
    have hi := frobenius_inj (BinaryGaloisField (2 * m + 1)) 2
    apply hi
    apply hi
    simpa only [frobenius_def, ← pow_mul, one_pow] using ha4
  have he : e x = 1 := by
    apply Subtype.ext
    apply Units.ext
    simpa [ha1] using hmat
  exact e.injective (he.trans e.map_one.symm)


universe u
variable {G V : Type u} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private def factorFixed (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (I : Subrepresentation ρ) : Subrepresentation I.toRepresentation where
  toSubmodule := (fixedSpace ρ K).comap I.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := (fixedSpace_stable_of_normal ρ K (mem_top g) v).2 hv

private def factor (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (I : Subrepresentation ρ) : Representation (ZMod 2) G (centralQuotient ρ K I.toSubmodule) :=
  (factorFixed ρ K I).quotientRepresentation

private theorem central_nontrivial (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) (I : Submodule (ZMod 2) V)
    (hs : K ≤ subspaceStabilizer ρ I) (hI : IsIrrPlus ρ K I) :
    ¬ (⊤ : Subgroup K) ≤ (actionHom (centralQuotientRepresentation ρ K I hs)).ker := by
  intro hk
  apply hI.not_le_fixedSpace ρ
  rw [← hI.choose_spec.1]
  apply Submodule.span_le.mpr
  rintro _ ⟨l, hl, v, hv, rfl⟩
  have hfix := (actionHom_eq_one_iff _ ⟨l, hl⟩).mp (hk (mem_top _))
    (Submodule.Quotient.mk (⟨v, hv⟩ : I))
  exact (Submodule.Quotient.eq ((fixedSpace ρ K).comap I.subtype)).mp hfix

private theorem irreducible_of_component (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) [IsIrreducible (ρ.comp K.subtype)] : IsIrreducible ρ := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial (ρ.comp K.subtype)
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, fun S => ?_⟩
  let T : Subrepresentation (ρ.comp K.subtype) :=
    ⟨S.toSubmodule, fun l _ hv => S.apply_mem_toSubmodule l hv⟩
  rcases eq_bot_or_eq_top T with h | h
  · left
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp K.subtype) => U.toSubmodule) h)
  · right
    exact Subrepresentation.toSubmodule_injective
      (congrArg (fun U : Subrepresentation (ρ.comp K.subtype) => U.toSubmodule) h)

variable [Finite G] [FiniteDimensional (ZMod 2) V]

private instance imageComponent_normal (σ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] : (actionSubgroup σ K).Normal :=
  Subgroup.Normal.map inferInstance (actionHom σ) σ.asGroupHom.rangeRestrict_surjective

private theorem image_structure (σ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] [IsQuasisimple K]
    (hquot : IsPGroup 2 (G ⧸ K))
    (hsurvive : ¬ K ≤ (actionHom σ).ker)
    (hirr : IsIrreducible (σ.comp K.subtype)) :
    IsQuasisimple (actionSubgroup σ K) ∧
    IsIrreducible ((imageRepresentation σ).comp (actionSubgroup σ K).subtype) ∧
    generalizedFitting (actionImage σ) = actionSubgroup σ K ∧
    IsPGroup 2 (actionImage σ ⧸ actionSubgroup σ K) ∧
    (actionHom σ).ker ≤ centralizer (K : Set G) := by
  let f := actionHom σ
  let L := actionSubgroup σ K
  let : L.Normal := Subgroup.Normal.map inferInstance f σ.asGroupHom.rangeRestrict_surjective
  let : Nontrivial L := (nontrivial_iff_ne_bot _).2
    (fun h => hsurvive ((map_eq_bot_iff K).mp h))
  let : IsQuasisimple L := IsQuasisimple.of_surjective (f.subgroupMap K) (f.subgroupMap_surjective K)
  have hLI : IsIrreducible ((imageRepresentation σ).comp L.subtype) :=
    (irreducible_comp_surjective_iff (f.subgroupMap K) (f.subgroupMap_surjective K)
      ((imageRepresentation σ).comp L.subtype)).mp hirr
  let := hLI
  let : IsIrreducible (imageRepresentation σ) := irreducible_of_component _ L
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcore : pCore 2 (actionImage σ) = ⊥ := le_bot_iff.mp
    ((normal_p_subgroup_le_ker (imageRepresentation σ) (pCore 2 (actionImage σ)) pCore_isPGroup).trans
      ((MonoidHom.ker_eq_bot_iff _).mpr (imageRepresentation_injective σ)).le)
  have hquo : IsPGroup 2 (actionImage σ ⧸ L) := hquot.of_surjective
    (QuotientGroup.map K L f (Subgroup.le_comap_map _ _))
    (QuotientGroup.map_surjective_of_surjective K L f
      (QuotientGroup.mk_surjective.comp σ.asGroupHom.rangeRestrict_surjective) _)
  refine ⟨inferInstance, hLI, generalizedFitting_eq_of_quasisimple_two_quotient L hquo hcore, hquo, ?_⟩
  have hc : IsComponent G K := ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  have hcomm := (hc.normal_dichotomy f.ker).resolve_left hsurvive
  exact commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm _ _).trans hcomm)

omit [FiniteDimensional (ZMod 2) V] in
private theorem image_sqtk_faithful {κ : GroupClass.{u}}
    (σ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal]
    (hG : IsSQTK κ G) (hq : IsPGroup 2 (G ⧸ K))
    (hf : Function.Injective ((actionHom σ).subgroupMap K)) : IsSQTK κ (actionImage σ) := by
  let f := actionHom σ
  have hkerTwo : IsPGroup 2 f.ker := by
    apply hq.of_injective ((QuotientGroup.mk' K).comp f.ker.subtype)
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply le_bot_iff.mp
    intro x hx
    apply Subtype.ext
    have hxK : (x : G) ∈ K := (QuotientGroup.eq_one_iff _).mp hx
    have he : f.subgroupMap K ⟨x, hxK⟩ = f.subgroupMap K 1 := by
      apply Subtype.ext
      change f x = f 1
      rw [map_one]
      exact x.property
    exact congrArg (fun k : K => (k : G)) (hf he)
  have hSQ : IsSQTK κ (G ⧸ f.ker) := by
    refine ⟨?_, hG.isKGroup.quotient f.ker⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho f.ker hkerTwo).trans
      (hG.stronglyQuasithin p hp ho)
  exact (IsSQTK.equiv (QuotientGroup.quotientKerEquivOfSurjective f
    σ.asGroupHom.rangeRestrict_surjective)).mp hSQ

private theorem factor_small_actor (ρ : Representation (ZMod 2) G V)
    (K : Subgroup G) [K.Normal] (I : Subrepresentation ρ)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hfaith : ∀ a ∈ A, (∀ v, factor ρ K I a v = v) → a = 1) :
    quadraticRatio (imageRepresentation (factor ρ K I)) ≤ 2 := by
  let σ := factor ρ K I
  have hqσ : IsQuadratic σ A :=
    quadratic_of_equivariant_surjection I.toRepresentation σ
      (factorFixed ρ K I).toSubmodule.mkQ
      (factorFixed ρ K I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation ρ I hq)
  apply (quadraticRatio_le_two_iff _).mpr
  refine ⟨actionSubgroup σ A, hA.actionSubgroup σ hfaith, ?_, ?_⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ v
    exact hqσ x hx y hy v
  · rw [fixedCodim_actionSubgroup, actionSubgroup_rank σ A hfaith]
    exact (fixedCodim_le_of_equivariant_surjection I.toRepresentation σ
      (factorFixed ρ K I).toSubmodule.mkQ
      (factorFixed ρ K I).toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans
        ((fixedCodim_subrepresentation_le ρ I A).trans hc)

/-- The full B.4 classifications recognize the literal central quotient of
an invariant Irr⁺ section. No natural-module identification is an input. -/
theorem invariant_natural_section {κ : GroupClass.{u}}
    (ρ : Representation (ZMod 2) G V) (K : Subgroup G) [K.Normal] [IsQuasisimple K]
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hG : IsSQTK κ G) (hquot : IsPGroup 2 (G ⧸ K))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hstable : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ I)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A)
    (hAC : Disjoint A (centralizer (K : Set G)))
    (hB42 : CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.FullB42.{u,u} κ)
    (hB45 : RatioRecognition.SmallRatioSource.FullB45.{u,u} κ) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K I hI.choose) (natural m)) := by
  let S : Subrepresentation ρ := ⟨I, fun g _ hv => (hstable (mem_top g) _).2 hv⟩
  let σ := factor ρ K S
  have hsurvive : ¬ K ≤ (actionHom σ).ker := by
    intro h
    apply central_nontrivial ρ K I hI.choose hI
    intro k _
    apply (actionHom_eq_one_iff _ k).mpr
    exact (actionHom_eq_one_iff σ k).mp (h k.property)
  have hi : IsIrreducible (σ.comp K.subtype) := hI.choose_spec.2
  obtain ⟨hqs, hirr, hfit, hquo, hker⟩ := image_structure σ K hquot hsurvive hi
  let L := actionSubgroup σ K
  let τ := imageRepresentation σ
  let : IsQuasisimple L := hqs
  have hfaithA : ∀ a ∈ A, (∀ v, σ a v = v) → a = 1 := by
    intro a ha hfix
    exact (disjoint_iff_inf_le.mp hAC) ⟨ha,
      hker ((actionHom_eq_one_iff σ a).mpr hfix)⟩
  have hsmall := factor_small_actor ρ K S A hA hq hc hfaithA
  let f := (actionHom σ).subgroupMap K
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro k hk
    have hk' : (k : G) ∈ (actionHom σ).ker := congrArg Subtype.val hk
    have hcK : k ∈ center K := by
      rw [mem_center_iff]
      intro l
      exact Subtype.ext (mem_centralizer_iff.mp (hker hk') l l.property)
    simpa only [center_eq_bot_of_equiv_suzuki eK] using hcK
  let e : K ≃* L := MulEquiv.ofBijective f ⟨hf, (actionHom σ).subgroupMap_surjective K⟩
  have hSQ := image_sqtk_faithful σ K hG hquot hf
  let eF : generalizedFitting (actionImage σ) ≃* L := MulEquiv.subgroupCongr hfit
  have hquasi : IsQuasisimple (generalizedFitting (actionImage σ)) :=
    IsQuasisimple.of_mulEquiv eF.symm
  have hirrF : IsIrreducible (τ.comp (generalizedFitting (actionImage σ)).subtype) := by
    change IsIrreducible ((imageRepresentation σ).comp (generalizedFitting (actionImage σ)).subtype)
    rw [hfit]
    exact hirr
  obtain ⟨a⟩ := RatioRecognition.natural_of_quadraticRatio_le_two τ hB42 hB45
    hSQ (imageRepresentation_injective σ) hquasi hirrF hsmall hm
    (eF.trans (e.symm.trans eK))
  refine ⟨⟨(e.trans eF.symm).trans a.groupEquiv, a.linearEquiv, ?_⟩⟩
  intro k v
  exact a.intertwines (eF.symm (e k)) v

/-- Recognition inside a relative overgroup, transported back to the
literal ambient central quotient. In the source the overgroup is K*T*. -/
theorem invariant_natural_section_in_subgroup {κ : GroupClass.{u}}
    (ρ : Representation (ZMod 2) G V) (K D : Subgroup G) (hKD : K ≤ D)
    [(K.subgroupOf D).Normal] [IsQuasisimple K]
    {m : ℕ} (hm : 0 < m) (eK : K ≃* SuzukiMatrixGroup m)
    (hD : IsSQTK κ D) (hquot : IsPGroup 2 (D ⧸ K.subgroupOf D))
    (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ K I)
    (hstable : D ≤ subspaceStabilizer ρ I)
    (A : Subgroup D) (hA : IsElementaryTwo A) (hq : IsQuadratic (ρ.comp D.subtype) A)
    (hc : fixedCodim (ρ.comp D.subtype) A ≤ 2 * rank A)
    (hAC : Disjoint A (centralizer (K.subgroupOf D : Set D)))
    (hB42 : CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.FullB42.{u,u} κ)
    (hB45 : RatioRecognition.SmallRatioSource.FullB45.{u,u} κ) :
    Nonempty (ActionEquiv (centralQuotientRepresentation ρ K I hI.choose) (natural m)) := by
  let f : K.subgroupOf D ≃* K := subgroupOfEquivOfLe hKD
  let : IsQuasisimple (K.subgroupOf D) := IsQuasisimple.of_mulEquiv f.symm
  have hI' := (IsIrrPlus.subgroupOf_iff ρ K D hKD I).mpr hI
  have hs : (⊤ : Subgroup D) ≤ subspaceStabilizer (ρ.comp D.subtype) I := by
    intro d _
    exact hstable d.property
  obtain ⟨a⟩ := invariant_natural_section (ρ.comp D.subtype) (K.subgroupOf D)
    hm (f.trans eK) hD hquot I hI' hs A hA hq hc hAC hB42 hB45
  let q := subgroupCentralQuotientEquiv ρ K D hKD I
  have hqact (k : K) (v : centralQuotient (ρ.comp D.subtype) (K.subgroupOf D) I) :
      q (centralQuotientRepresentation (ρ.comp D.subtype) (K.subgroupOf D) I
        hI'.choose (f.symm k) v) =
      centralQuotientRepresentation ρ K I hI.choose k (q v) := by
    induction v using Submodule.Quotient.induction_on with | _ v => rfl
  refine ⟨⟨f.symm.trans a.groupEquiv, q.symm.trans a.linearEquiv, ?_⟩⟩
  intro k v
  obtain ⟨v, rfl⟩ := q.surjective v
  change a.linearEquiv (q.symm (centralQuotientRepresentation ρ K I hI.choose k (q v))) =
    natural m (a.groupEquiv (f.symm k)) (a.linearEquiv (q.symm (q v)))
  rw [← hqact, q.symm_apply_apply, q.symm_apply_apply]
  exact a.intertwines (f.symm k) v

end CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.NaturalSections.SectionRecognition

end
