module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Residual.Multiplicity.Thompson
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Statements

/-!
# Natural multiplicity in the Thompson-moving branch

The actual component moves the entire full normalizer orbit. The complete
B.5.6 alternatives therefore leave the quasisimple case, without any
assumption about its three-rank or the parity of the defining degree.
B.5.1 then gives either one natural constituent or component quadratic
ratio at most one. The exact repeated-natural ratio s/2 bounds s by two.

This retains the original SL₃ quotient marking and its full center. The
Doubling.Source consumer turns strict seed enlargement into the literal
sum of two natural modules required in 11.2.1.
Source: Aschbacher--Smith, B.5.1 and B.5.6, pp.99--110, and 11.2.1, p.767.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups ENNReal IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter3.Section02.ChosenSource325
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling
open Preliminary

private theorem irrPlus_or_component_ratio
    {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
    (ρ : Representation (ZMod 2) H W)
    (h : ChapterB.SourceInduction.FFHypothesis CFSG.KnownSimple.IsKnownSimple ρ)
    {K : Subgroup H} (hK : IsComponent H K) (hm : moved ρ K = ⊤)
    (F : BinaryField) (e : K ≃* SL(3,F.Carrier)) :
    IsIrrPlus ρ K ⊤ ∨ quadraticRatio (ρ.comp K.subtype) ≤ 1 := by
  let : IsQuasisimple K := hK.2
  let : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK.isCComponent.ne_bot
  let : Nontrivial H := K.subtype_injective.nontrivial
  cases ChapterB.SourceInduction.nontrivialAdequateAlternative_knownSimple ρ h with
  | quasisimple hq c =>
    have he : K = generalizedFitting H := hK.eq_of_le
      ⟨(inferInstance : (generalizedFitting H).Normal).isSubnormal,hq⟩
      (component_le_generalizedFitting H K hK)
    subst K
    have hs : c.sectionData.space.toSubmodule = ⊤ := c.sectionData.space_eq.trans hm
    cases c.clause_one with
    | irreducible hi _ _ _ _ => exact Or.inl (hs ▸ hi)
    | doubleThree _ whole _ _ hq =>
      right
      let a : H ≃* generalizedFitting H := (MulEquiv.subgroupCongr whole).trans topEquiv |>.symm
      have hh := quadraticRatio_le_of_injective_equivariant ρ
        (ρ.comp (generalizedFitting H).subtype) a.toMonoidHom a.injective
        (LinearEquiv.refl (ZMod 2) W) (fun _ _ => rfl)
      exact hh.trans_eq hq
    | naturalDual d hd _ hn =>
      obtain ⟨a⟩ := hn
      exact (SourceCompletion.no_linearThree_binary_equiv F hd (e.symm.trans a.groupEquiv)).elim
    | repeatedNatural d s hd _ _ _ hn =>
      obtain ⟨a⟩ := hn
      exact (SourceCompletion.no_linearThree_binary_equiv F hd (e.symm.trans a.groupEquiv)).elim
  | symmetricThree c =>
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
      (f := c.equiv.toMonoidHom) c.equiv.injective
    exact (Group.IsPerfect.not_isSolvable K inferInstance).elim
  | twoFactors c => exact (not_twoFactors_of_full_component ρ K hK hm c).elim
  | outerSixThree c => exact (not_outerSixThree_of_full_component ρ h hK hm c).elim
  | hyperplane c => exact (not_hyperplane_of_full_component ρ K hm c).elim

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
private theorem fullAction_component_moved :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    moved (imageRepresentation ρ)
      ((L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)) = ⊤ := by
  let := fullModule_elementary D S
  let U := componentOrbit V (normalizer (L : Set G))
  let ρ := fullModuleConjugation D S
  let f := actionHom ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map f
  let W := moved (imageRepresentation ρ) K
  let C := W.toAddSubgroup.toSubgroup'.map U.subtype
  have hc : ⁅U,L⁆ ≤ C := by
    apply commutator_le.mpr
    intro u hu l hl
    let w : Additive U := Additive.ofMul ⟨u,hu⟩
    let a := f (inclusion L.le_normalizer ⟨l,hl⟩)
    have ha : a ∈ K := mem_map_of_mem f hl
    have hw : w - imageRepresentation ρ a w ∈ W := by
      apply W.neg_mem_iff.mp
      rw [neg_sub]
      exact Submodule.subset_span ⟨a,ha,w,Submodule.mem_top,rfl⟩
    refine ⟨(w - imageRepresentation ρ a w).toMul,hw,?_⟩
    change u / (l * u * l⁻¹) = ⁅u,l⁆
    rw [commutatorElement_def]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv,mul_assoc]
  have hUC : U ≤ C := (fullModule_eq_commutator D S).le.trans hc
  apply top_unique
  intro v _
  obtain ⟨w,hw,he⟩ := hUC v.toMul.property
  have he' : w = v.toMul := Subtype.ext he
  change Additive.ofMul w ∈ W at hw
  rw [he'] at hw
  exact hw

private theorem sl3_irrPlus_or_component_ratio_of_component_le_offender
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hKO : letI := fullModule_elementary D S
      let ρ := fullModuleConjugation D S
      (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ) ≤
        offenderSubgroup (imageRepresentation ρ)) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let τ := imageRepresentation ρ
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    IsIrrPlus τ K ⊤ ∨ quadraticRatio (τ.comp K.subtype) ≤ 1 := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let τ := imageRepresentation ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  let O := offenderSubgroup τ
  let σ := τ.comp O.subtype
  let K₀ := K.subgroupOf O
  let a : K₀ ≃* K := subgroupOfEquivOfLe hKO
  have hf : ChapterB.SourceInduction.FFHypothesis CFSG.KnownSimple.IsKnownSimple σ :=
    ChapterB.InternalThompsonAction.offender_hypothesis τ (actionHom ρ)
      ρ.asGroupHom.rangeRestrict_surjective (normalizer_sqtk D S)
      (imageRepresentation_injective ρ) (fullAction_twoCore_eq_bot D S)
  have hm : moved σ K₀ = ⊤ := by
    rw [moved,subspaceCommutator_comp_map,map_subgroupOf_eq_of_le hKO]
    exact fullAction_component_moved D S
  obtain ⟨e,_⟩ := sl3_fullAction_component_marking D S m
  rcases irrPlus_or_component_ratio σ hf
      ((sl3_fullAction_component_isComponent D S m).subgroupOf hKO) hm S.field
      (a.trans e) with hi | hq
  · exact Or.inl ((IsIrrPlus.subgroupOf_iff τ K O hKO ⊤).mp hi)
  · right
    exact (quadraticRatio_le_of_injective_equivariant (σ.comp K₀.subtype)
      (τ.comp K.subtype) a.toMonoidHom a.injective
      (LinearEquiv.refl _ _) (fun _ _ => rfl)).trans hq

private theorem fullModule_component_copies
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {s : ℕ} (h : FullModuleNaturalCopies D S m s) :
    letI := fullModule_elementary D S
    let ρ := fullModuleConjugation D S
    let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
    Nonempty (ActionEquiv ((imageRepresentation ρ).comp K.subtype)
      (repeated (linearNatural S.field 3) s)) := by
  let := fullModule_elementary D S
  obtain ⟨e,he⟩ := sl3_fullAction_component_marking D S m
  obtain ⟨b,hb⟩ := h
  refine ⟨⟨e,b,?_⟩⟩
  rintro ⟨k,l,hl,rfl⟩ v
  change (l : G) ∈ L at hl
  have hh := he ⟨l,hl⟩
  exact (hb ⟨l,hl⟩ v).trans (congrArg (fun g => repeated (linearNatural S.field 3) s g (b v)) hh.symm)

private theorem fullModule_copies_le_one_of_irrPlus
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {s : ℕ} (hs : 0 < s) (h : FullModuleNaturalCopies D S m s)
    (hi : letI := fullModule_elementary D S
      let ρ := fullModuleConjugation D S
      IsIrrPlus (imageRepresentation ρ)
        ((L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)) ⊤) : s ≤ 1 := by
  let := fullModule_elementary D S
  let ρ := fullModuleConjugation D S
  let τ := imageRepresentation ρ
  let K := (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ)
  obtain ⟨e⟩ := fullModule_component_copies D S m h
  let j : (Fin 3 → S.field.Carrier) →ₗ[ZMod 2]
      Additive (componentOrbit V (normalizer (L : Set G))) :=
    e.linearEquiv.symm.toLinearMap.comp (LinearMap.single (R := ZMod 2) (φ := fun _ : Fin s => Fin 3 → S.field.Carrier) ⟨0,hs⟩)
  have hj : Function.Injective j := by
    intro v w hh
    have hh' := congrFun (e.linearEquiv.symm.injective hh) ⟨0,hs⟩
    simpa using hh'
  have hjs : K ≤ subspaceStabilizer τ j.range := by
    apply le_subspaceStabilizer
    rintro k hk w ⟨v,rfl⟩
    refine ⟨(linearNatural S.field 3) (e.groupEquiv ⟨k,hk⟩) v,?_⟩
    apply e.linearEquiv.injective
    have hh := e.intertwines ⟨k,hk⟩ (j v)
    change e.linearEquiv (τ k (j v)) = _ at hh
    rw [hh]
    change e.linearEquiv (e.linearEquiv.symm _) = _
    simp only [LinearEquiv.apply_symm_apply]
    funext i
    by_cases hi : i = ⟨0,hs⟩
    · subst i; simp [repeated,j]
    · simp [repeated,hi,j]
  have hn : j.range ≠ ⊥ := by
    intro hz
    have hj0 := LinearMap.range_eq_bot.mp hz
    obtain ⟨v,hv⟩ := exists_ne (0 : Fin 3 → S.field.Carrier)
    exact hv (hj (by rw [hj0]; rfl))
  have ht : j.range = ⊤ := (hi.eq_or_le_fixedSpace τ hjs le_top).resolve_right (fun hh =>
    hn (bot_unique (hh.trans_eq (sl3_fullAction_component_fixedSpace_eq_bot D S m))))
  have hd := LinearMap.finrank_le_finrank_of_surjective (LinearMap.range_eq_top.mp ht)
  have hF := NaturalMultiplicity.natural_finrank S.field 1
  have hF' : Module.finrank (ZMod 2) (Fin 3 → S.field.Carrier) = 3 * S.field.degree := by
    simpa only [Module.finrank_pi_fintype,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul,one_mul] using hF
  rw [h.finrank,hF'] at hd
  nlinarith [S.field.degree_pos]

/-- B.5 bounds the original full natural multiplicity by two once its
marked component lies in the actual offender subgroup. -/
theorem copies_le_two_of_component_le_offender
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hKO : letI := fullModule_elementary D S
      let ρ := fullModuleConjugation D S
      (L.subgroupOf (normalizer (L : Set G))).map (actionHom ρ) ≤
        offenderSubgroup (imageRepresentation ρ))
    {s : ℕ} (hs : 0 < s) (h : FullModuleNaturalCopies D S m s) : s ≤ 2 := by
  let := fullModule_elementary D S
  rcases sl3_irrPlus_or_component_ratio_of_component_le_offender D S m hKO with hi | hq
  · exact (fullModule_copies_le_one_of_irrPlus D S m hs h hi).trans (by decide)
  · obtain ⟨e⟩ := fullModule_component_copies D S m h
    have hh := quadraticRatio_le_of_injective_equivariant _ _ e.groupEquiv.toMonoidHom
      e.groupEquiv.injective e.linearEquiv e.intertwines
    rw [NaturalMultiplicity.natural_quadraticRatio S.field hs] at hh
    have hb : (s : ℝ≥0∞) / 2 ≤ 1 := hh.trans hq
    have hb' : (s : ℝ≥0∞) ≤ 2 := by
      simpa using (ENNReal.div_le_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num)).mp hb
    exact_mod_cast hb'

/-- The genuine Thompson identity, via B.2.7 and B.5, bounds the natural
multiplicity of the original full orbit by two. -/
theorem copies_le_two_of_thompson
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (hcomm : L = ⁅L, Stellmacher.elementaryAbelianMaxJ (T : Subgroup G)⁆)
    {s : ℕ} (hs : 0 < s) (h : FullModuleNaturalCopies D S m s) : s ≤ 2 :=
  copies_le_two_of_component_le_offender D S m
    (fullAction_component_le_offender_of_thompson D S hcomm) hs h


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.Doubling
