module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOrbitRatio
public import Theory.Representation.BinaryOffender.TwoSectionBudget
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.SourceBound
public import Theory.Representation.BinaryOffender.MovedDimension
public import Theory.Representation.BinaryOffender.CubicSection
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCubicModels

/-!
# Cubic constituent collapse for the original PSL₃(4) component

A small cubic actor has rank at most four in Aut(PSL₃(4)), hence fixed
codimension at most eight. A faithful simple component constituent has
dimension at least nine, so its translates cannot be distinct. If this
constituent were proper, a second faithful section would survive in the
quotient. Both sections are non-FF by the faithful quadratic exclusion;
adding their fixed codimensions contradicts the cubic budget.

Thus a faithful irreducible whole action restricts irreducibly to the
component. For an arbitrary faithful action, a literal irreducible
subquotient detecting the component is faithful and inherits the cubic
bound. The B.4/K.3 model sieve then gives Hermitian coordinates, contradicted
by the original diagram element acting on that very subquotient.

This supplies a specialized D.3.10/B.4 replacement for the PSL₃(4) branch of
Aschbacher--Smith 5.1.23, printed p.646, `refs/quasithin.pdf`. It neither
assumes irreducibility of the original orbit nor a strict-ratio callback.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
open ChapterK.Linear.Recognition
universe u v
variable {X : Type u} [Group X] [Finite X]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]

omit [Finite X] in
private theorem simple_facts (K : Subgroup X) (hm : ClassicalGroup.IsPSL K 3 4) :
    IsQuasisimple K ∧ IsSimpleGroup K ∧ ¬ IsMulCommutative K := by
  obtain ⟨hq,hz,_⟩ := PSL3FourExclusion.model_facts hm
  let := hq
  let := hq.simple
  let hs : IsSimpleGroup K :=
    (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm).isSimpleGroup
  refine ⟨hq,hs,?_⟩
  intro ha
  have he := center_eq_top_iff.mpr ha
  rw [hz] at he
  exact bot_ne_top he

private theorem rank_bound (K : Subgroup X) [K.Normal]
    (hm : ClassicalGroup.IsPSL K 3 4) (hc : centralizer (K : Set X) = ⊥)
    (A : Subgroup X) (hA : IsElementaryTwo A) : rank A ≤ 4 := by
  let := hA.2
  let : CommGroup A := IsMulCommutative.instCommGroup
  let f := (MulAut.conjNormal : X →* MulAut K).comp A.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro a ha
    apply Subtype.ext
    have he : (a:X) ∈ (MulAut.conjNormal : X →* MulAut K).ker := ha
    rwa [MulAut.conjNormal_ker_eq_centralizer,hc,mem_bot] at he
  have hr := primeRank_ge_of_elementary_embedding
    (fun a : A => elemPow_eq_one_of_isElementaryAbelian (a:X) a.property |> Subtype.ext)
    hA.card_eq_two_pow_rank f hf
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have he := primeRank_congr 2 (MulAut.congr e)
  have hb := Matrix.PSL3Even.automorphism_two_rank_eq F (n := 2) (by decide) hF
  omega

private theorem constituent_stable (ρ : Representation (ZMod 2) X W)
    (K A : Subgroup X) [K.Normal] (hm : ClassicalGroup.IsPSL K 3 4)
    (hc : centralizer (K : Set X) = ⊥)
    (hA : IsElementaryTwo A) (hd : fixedCodim ρ A ≤ 2 * rank A)
    (J : Subrepresentation (ρ.comp K.subtype))
    (hj : J.toRepresentation.IsIrreducible) (hf : Function.Injective J.toRepresentation) :
    A ≤ subspaceStabilizer ρ J.toSubmodule := by
  obtain ⟨hqs,hs,_⟩ := simple_facts K hm
  let := hs
  let := hj
  have hr := rank_bound K hm hc A hA
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨k,hk⟩ := exists_ne (1 : K)
  have hdim := Representation.PSL3Four.finrank_ge_nine_of_equiv hF e J.toRepresentation
    ⟨k,fun he => hk (hf (he.trans J.toRepresentation.map_one.symm))⟩
  intro a ha
  apply (subspace_map_eq_iff ρ J.toSubmodule a).mp
  by_contra hne
  let c := conjugateSubrepresentationOrderIso ρ K a
  have hJa : IsAtom J := (Subrepresentation.irreducible_iff_isAtom J).mp hj
  have hca : IsAtom (c J) := (c.isAtom_iff J).mpr hJa
  have hne' : c J ≠ J := by
    intro he
    apply hne
    simpa only [c,conjugateSubrepresentationOrderIso_toSubmodule] using
      congrArg Subrepresentation.toSubmodule he
  have hdj : Disjoint J.toSubmodule (J.toSubmodule.map (ρ a)) := by
    rw [disjoint_iff]
    have he := congrArg Subrepresentation.toSubmodule (hca.disjoint_of_ne hJa hne').symm.eq_bot
    change J.toSubmodule ⊓ (c J).toSubmodule = ⊥ at he
    simpa only [c,conjugateSubrepresentationOrderIso_toSubmodule] using he
  have hh := finrank_le_fixedCodim_of_disjoint_map ρ J.toSubmodule ha hdj
  omega

omit [Finite X] [FiniteDimensional (ZMod 2) W] in
private theorem faithful_section (ρ : Representation (ZMod 2) X W)
    (K : Subgroup X) [K.Normal] (hm : ClassicalGroup.IsPSL K 3 4)
    (hc : centralizer (K : Set X) = ⊥) (hn : ¬ K ≤ ρ.ker) :
    Function.Injective ρ := by
  obtain ⟨hq,hs,_⟩ := simple_facts K hm
  let := hq
  have hk : IsComponent X K := ⟨(inferInstance : K.Normal).isSubnormal,hq⟩
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  rcases hk.normal_dichotomy ρ.ker with he | he
  · exact (hn he).elim
  · exact bot_unique ((le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp he)).trans hc.le)

/-- A faithful irreducible whole action with a small cubic actor restricts
irreducibly to the original normal PSL₃(4). -/
theorem component_irreducible_of_small_cubic
    (ρ : Representation (ZMod 2) X W) (K : Subgroup X) [K.Normal]
    (κ : GroupClass.{u}) (hsq : IsSQTK κ X) (hm : ClassicalGroup.IsPSL K 3 4)
    (hquot : IsPGroup 2 (X ⧸ K)) (hcore : pCore 2 X = ⊥)
    (hf : Function.Injective ρ) (hi : ρ.IsIrreducible)
    (hq : cubicRatio ρ ≤ 2) : Representation.IsIrreducible (ρ.comp K.subtype) := by
  obtain ⟨hqs,hs,hnc⟩ := simple_facts K hm
  let := hqs
  let := hs
  have hc := centralizer_eq_bot_of_simple_two_quotient K hnc hquot hcore
  obtain ⟨A,hA,_hcu,hd⟩ := (cubicRatio_le_nat_iff ρ 2).mp hq
  obtain ⟨J,hJ,hfJ⟩ := exists_faithful_normal_simple_constituent ρ hf hi K
  have hAJ := constituent_stable ρ K A hm hc hA hd J hJ hfJ
  let H := K ⊔ A
  let K₀ := K.subgroupOf H
  have hKH : K ≤ H := le_sup_left
  let eK : K₀ ≃* K := subgroupOfEquivOfLe hKH
  let : IsQuasisimple K₀ := IsQuasisimple.of_mulEquiv eK.symm
  have hm₀ : ClassicalGroup.IsPSL K₀ 3 4 := hm.of_mulEquiv eK
  have hc₀ : centralizer (K₀ : Set H) = ⊥ := by
    apply bot_unique
    intro x hx
    apply Subtype.ext
    have hx' : (x:X) ∈ centralizer (K : Set X) := by
      intro k hk
      exact congrArg Subtype.val (hx ⟨k,hKH hk⟩ hk)
    exact mem_bot.mp (hc ▸ hx')
  have hquot₀ : IsPGroup 2 (H ⧸ K₀) := isPGroup_quotient_subgroupOf K H hquot
  have hcore₀ : pCore 2 H = ⊥ := by
    obtain ⟨_,hz,_⟩ := PSL3FourExclusion.model_facts hm₀
    exact (centralizer_eq_twoCore_of_centerless_quasisimple_quotient K₀ hz hquot₀).symm.trans hc₀
  let τ := ρ.comp H.subtype
  let U : Subrepresentation τ := ⟨J.toSubmodule,by
    intro x v hv
    exact ((sup_le (le_constituent_stabilizer ρ K J) hAJ) x.property v).2 hv⟩
  have hfu : Function.Injective U.toRepresentation :=
    MonoidHom.injective_of_injective_normal_inclusion K H hKH U.toRepresentation hfJ hc
  have hnU : ¬ IsFFModule U.toRepresentation :=
    PSL3FourExclusion.not_isFFModule_of_faithful
      (hsq.subgroup H) hm₀ hquot₀ hcore₀ hfu
  have hJtop : J = ⊤ := by
    by_contra hJne
    have hfull : subspaceCommutator ρ ⊤ K = ⊤ := by
      let M : Subrepresentation ρ := ⟨subspaceCommutator ρ ⊤ K,by
        intro x v hv
        exact ((subspaceCommutator_invariant_normalizer ρ
          (show (⊤ : Subgroup X) ≤ subspaceStabilizer ρ ⊤ from
            le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => Submodule.mem_top))
          (show (⊤ : Subgroup X) ≤ normalizer (K : Set X) by rw [normalizer_eq_top]))
          (mem_top x) v).2 hv⟩
      rcases hi.eq_bot_or_eq_top M with hb | ht
      · have hb' : subspaceCommutator ρ ⊤ K = ⊥ := congrArg Subrepresentation.toSubmodule hb
        have hfix := (subspaceCommutator_eq_bot_iff ρ ⊤ K).mp hb'
        have hk : K = ⊥ := by
          apply bot_unique
          intro k hk
          apply mem_bot.mpr
          apply hf
          ext v
          have hv := hfix (x := v) Submodule.mem_top ⟨k,hk⟩
          change ρ k v = v at hv
          simpa only [map_one,Module.End.one_apply] using hv
        exact ((nontrivial_iff_ne_bot K).mp inferInstance hk).elim
      · exact congrArg Subrepresentation.toSubmodule ht
    have hnq : ¬ K₀ ≤ U.quotientRepresentation.ker := by
      intro hh
      have hle : subspaceCommutator ρ ⊤ K ≤ J.toSubmodule := by
        apply Submodule.span_le.mpr
        rintro _ ⟨k,hk,v,_,rfl⟩
        have he := LinearMap.congr_fun (hh (show (⟨k,hKH hk⟩ : H) ∈ K₀ from hk))
          (U.toSubmodule.mkQ v)
        exact (Submodule.Quotient.eq U.toSubmodule).mp he
      exact hJne (Subrepresentation.toSubmodule_injective (top_unique (hfull ▸ hle)))
    obtain ⟨Q,N,hiQ,hnQ⟩ :=
      QuadraticFourGroup.exists_irreducible_section_surviving_perfect K₀ hnq
    have hfQ := faithful_section N.quotientRepresentation K₀ hm₀ hc₀ hnQ
    have hrQ := PSL3FourExclusion.quadraticRatio_gt_two_of_faithful
      (ρ := N.quotientRepresentation) (hsq.subgroup H) hm₀ hquot₀ hcore₀ hfQ
    have hA₀ : IsElementaryTwo (A.subgroupOf H) := by
      let := hA.2
      refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)⟩
      intro he
      exact hA.1 (by rw [← map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),he,Subgroup.map_bot])
    have hUc : rank (A.subgroupOf H) < fixedCodim U.toRepresentation (A.subgroupOf H) := by
      by_contra! he
      exact hnU ⟨A.subgroupOf H,hA₀,he⟩
    have hQc : rank (A.subgroupOf H) < fixedCodim N.quotientRepresentation (A.subgroupOf H) := by
      by_contra! he
      have hff : IsFFModule N.quotientRepresentation := ⟨A.subgroupOf H,hA₀,he⟩
      exact not_le_of_gt hrQ
        (((isFFModule_iff_quadraticRatio_le_one _).mp hff).trans (by norm_num))
    have hqsub := fixedCodim_subrepresentation_le U.quotientRepresentation Q (A.subgroupOf H)
    have hqn := fixedCodim_quotient_add_subrepresentation_le Q.toRepresentation N (A.subgroupOf H)
    have huq := fixedCodim_quotient_add_subrepresentation_le τ U (A.subgroupOf H)
    rw [fixedCodim_subgroupOf ρ (show A ≤ H from le_sup_right)] at huq
    rw [rank_subgroupOf (show A ≤ H from le_sup_right)] at hUc hQc
    omega
  have ht := (Subrepresentation.irreducible_iff_isAtom ⊤).mpr
    (hJtop ▸ (Subrepresentation.irreducible_iff_isAtom J).mp hJ)
  let e : RepEquiv (⊤ : Subrepresentation (ρ.comp K.subtype)).toRepresentation
      (ρ.comp K.subtype) :=
    { toLinearEquiv := Submodule.topEquiv
      isIntertwining' := by intro k; ext v; rfl }
  exact (RepEquiv.irreducible_euqiv e).mp ht

open Representation.HermitianTensorThree.ImageOuter
open Matrix.PSL3.LinearThree.OuterExtensions

/-- The same diagram actor excludes small cubic ratios on arbitrary faithful
modules, by detecting the component on an invariant irreducible subquotient. -/
theorem cubicRatio_gt_two_of_diagram
    (ρ : Representation (ZMod 2) X W) (K : Subgroup X) [K.Normal]
    (κ : GroupClass.{u}) (hsq : IsSQTK κ X) (hm : ClassicalGroup.IsPSL K 3 4)
    (hquot : IsPGroup 2 (X ⧸ K)) (hcore : pCore 2 X = ⊥)
    (hf : Function.Injective ρ)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (e : K ≃* PSL(3,F)) (t : X) (a : MulAut K) (b : MulAut PSL(3,F))
    (ha : ∀ k : K, (a k : X) = t * k * t⁻¹)
    (hb : ∀ k, e (a k) = b (e k)) (hd : b ∉ diagramTrivial F) :
    2 < cubicRatio ρ := by
  apply lt_of_not_ge
  intro hq
  obtain ⟨hqs,hs,hnc⟩ := simple_facts K hm
  let := hqs
  let := hs
  obtain ⟨hfit,hcent,_⟩ := simple_two_quotient_structure K hnc hquot hcore
  have hn : ¬ K ≤ ρ.ker := by
    intro he
    have he' : K = ⊥ := bot_unique
      (he.trans ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le)
    exact (nontrivial_iff_ne_bot K).mp inferInstance he'
  obtain ⟨U,N,hiN,hnN⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect K hn
  have hfN := faithful_section N.quotientRepresentation K hm hcent hnN
  have hqN := cubicRatio_quotient_le_nat U.toRepresentation N 2
    (cubicRatio_subrepresentation_le_nat ρ U 2 hq)
  have hiK := component_irreducible_of_small_cubic N.quotientRepresentation K
    κ hsq hm hquot hcore hfN hiN hqN
  exact not_hermitian_of_diagram_action N.quotientRepresentation K hF e t a b ha hb hd
    (hermitian_coordinates_of_small_cubic N.quotientRepresentation K κ hsq hfit hm hfN hiK hqN)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.CubicEscape.SpanAction
