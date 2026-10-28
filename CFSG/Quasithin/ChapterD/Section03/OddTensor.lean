module
public import CFSG.Quasithin.ChapterD.Section03.ConstituentDrop
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import Theory.Representation.BinaryOffender.SquareNormalizerActors
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.BinaryOffender.CubicSection
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Eleven
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.PrimeDegreeEight
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.Seventeen
public import CFSG.Quasithin.ChapterD.Section03.PreservingConstituent
public import Theory.Representation.SL2.OddSquareExchange
public import Theory.SpecificGroups.SL2.SmallOddComparisons
/-!
# Odd-prime tensor exclusion with the full linear normalizer

For PSL₂(p), p at least eleven, the actual constituent action cannot have
cubic ratio at most two, by the proved prime-field parameter sieve and its
small-prime exclusions. An irreducible commuting pair in a larger actor
admits a proper invariant constituent with strictly smaller ratio. Thus
factor-preserving cubic actors are excluded even when they induce outer
diagonal automorphisms.

The previous exchange-displacement bound excludes the other actors.
Transport to the common normalizer of the two literal factor images then
proves that the full square normalizer has cubic ratio greater than two.
The original Chapter10 seed is the consumer; only the actual factor carries
the SQTK hypothesis, with no hypothesis on its entire linear normalizer.
Source: Aschbacher--Smith D.3.7, printed pp.197--199, and K.2, p.453.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterD
open ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion
private theorem odd_prime_parameters
    {A V : Type*} [Group A] [Finite A] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) A V} {S : Subgroup A}
    (h : ChapterK.RankOne.SourceHypotheses ρ S) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (S ⧸ center S) 2 p) : p = 5 ∨ p = 7 := by
  have hp3 : p ≠ 3 := by
    intro hp3
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let := h.quasisimple
    let : Group.IsPerfect (S ⧸ center S) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center S))
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three
      (hc.trans hp3) inferInstance
  have hlo : 4 ≤ p ^ 1 := by
    obtain ⟨k,hk⟩ := ho
    have := hp.two_le
    simp only [pow_one]
    omega
  rcases h with ⟨hsq,hfit,hquasi,hfaith,hirr,hratio⟩
  subst S
  let h : SourceAction ρ :=
    ⟨hsq,hquasi,hfaith,hirr⟩
  have hhi := RankOneSize.source_field_order_le_twentyFive
    ρ h hp ho (Or.inl rfl : 1 = 1 ∨ 1 = 2) hlo (by simpa only [pow_one] using hm) hratio
  have hcases : p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by
    norm_num only [pow_one] at hlo hhi
    interval_cases p
    all_goals norm_num at hp
    all_goals norm_num
  rcases hcases with h5 | h7 | h11 | h13 | h17 | h19 | h23
  · exact Or.inl h5
  · exact Or.inr h7
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.Eleven.two_lt_cubicRatio ρ h hm))
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.source_prime_exclusion ρ h (Or.inl rfl) hm))
  · subst p
    have hd := RankOneSmall.source_seventeen_degree_eq_eight ρ h hm hratio
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.Seventeen.two_lt_cubicRatio_of_degree_le_eight ρ h hm hd.le))
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inl rfl)) hm))
  · subst p
    exact False.elim ((not_lt_of_ge hratio)
      (RankOneSmall.source_prime_exclusion ρ h (Or.inr (Or.inr rfl)) hm))

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

variable {p : ℕ} [Fact p.Prime] [IsQuasisimple PSL(2,ZMod p)]

theorem odd_prime_constituent_actor_ratio
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L : Subgroup G) [L.Normal]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hi : IsIrreducible (ρ.comp L.subtype))
    (e : L ≃* PSL(2,ZMod p))
    (A : Subgroup G) (hA : IsElementaryTwo A) (hc : IsCubic ρ A) :
    2 < actionRatio ρ A := by
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  by_contra! hsmall
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  let : IsElementaryAbelian 2 A := hA.2
  let : IsIrreducible (ρ.comp L.subtype) := hi
  let := Subrepresentation.irreducible_module_nontrivial (ρ.comp L.subtype)
  let H := L ⊔ A
  let N := L.subgroupOf H
  let C := A.subgroupOf H
  let eN : N ≃* L := subgroupOfEquivOfLe (show L ≤ H from le_sup_left)
  let : IsQuasisimple N := IsQuasisimple.of_mulEquiv eN.symm
  let τ : Representation (ZMod 2) H V := ρ.comp H.subtype
  have hτ : Function.Injective τ := hf.comp H.subtype_injective
  have hirr : IsIrreducible (τ.comp N.subtype) :=
    (irreducible_comp_surjective_iff eN.toMonoidHom eN.surjective (ρ.comp L.subtype)).mpr hi
  have hquot : IsPGroup 2 (H ⧸ N) :=
    quotient_isPGroup_of_sup_eq_top C N
      ((IsElementaryAbelian.isPGroup 2 A).of_injective
        (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).toMonoidHom
        (subgroupOfEquivOfLe (show A ≤ H from le_sup_right)).injective)
      ((sup_comm C N).trans (codisjoint_subgroupOf_sup L A).eq_top)
  have hcore : pCore 2 H = ⊥ := by
    let : τ.IsIrreducible := irreducible_of_subgroup_restriction τ N hirr
    have hk := normal_p_subgroup_le_ker τ (pCore 2 H) pCore_isPGroup
    exact bot_unique (hk.trans (τ.ker_eq_bot_iff.mpr hτ).le)
  have hN : IsSQTK KnownSimple.IsKnownSimple N := (IsSQTK.equiv eN).mpr hL
  have hH : IsSQTK KnownSimple.IsKnownSimple H :=
    ChapterB.QuasisimpleSource.IrreducibleBranch.sqtk_of_twoGroup_quotient
      ChapterB.ComponentRecognition.SQTKSectionImage.knownSimple_containsSimpleTwoGroups N hquot hN
  have hC : IsElementaryTwo C := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf (show A ≤ H from le_sup_right)⟩
    intro he
    change A.subgroupOf H = ⊥ at he
    exact hA.1 (by rw [←map_subgroupOf_eq_of_le (show A ≤ H from le_sup_right),he,Subgroup.map_bot])
  have hratio : actionRatio τ C = actionRatio ρ A := by
    unfold actionRatio
    rw [fixedCodim_subgroupOf ρ (show A ≤ H from le_sup_right),
      rank_subgroupOf (show A ≤ H from le_sup_right)]
  have hbound : cubicRatio τ ≤ actionRatio ρ A := by
    rw [←hratio]
    exact iInf_le_of_le C (iInf_le_of_le ⟨hC,fun a ha b hb c hc' v => hc a ha b hb c hc' v⟩ le_rfl)
  have hs : ChapterK.RankOne.SourceHypotheses τ N :=
    ⟨hH,generalizedFitting_eq_of_quasisimple_two_quotient N hquot hcore,
      inferInstance,hτ,hirr,hbound.trans hsmall⟩
  have hZ : center N = ⊥ := by
    let : IsSimpleGroup N := (eN.trans e).isSimpleGroup
    exact (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun hh => Group.IsPerfect.not_isMulCommutative N (center_eq_top_iff.mp hh))
  let eQ : (N ⧸ center N) ≃* PSL(2,ZMod p) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      ((QuotientGroup.quotientBot (G := N)).trans (eN.trans e))
  have hm : ClassicalGroup.IsPSL (N ⧸ center N) 2 p :=
    ⟨ZMod p,inferInstance,inferInstance,by simp,⟨eQ⟩⟩
  rcases odd_prime_parameters hs (Fact.out : p.Prime)
    ((Fact.out : p.Prime).odd_of_ne_two (by omega)) hm with h | h <;> omega

theorem odd_prime_subspace_actor_ratio
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (e : L ≃* PSL(2,ZMod p))
    (U : Subrepresentation (ρ.comp L.subtype)) (hi : U.toRepresentation.IsIrreducible)
    (hf : Function.Injective U.toRepresentation)
    (C : Subgroup (subspaceActionImage ρ U.toSubmodule))
    (hC : C ∈ Qhat (subspaceImageRepresentation ρ U.toSubmodule)) :
    2 < actionRatio (subspaceImageRepresentation ρ U.toSubmodule) C := by
  let f := subgroupActionHom ρ U.toSubmodule L (le_constituent_stabilizer ρ L U)
  have hfi : Function.Injective f := by
    intro x y h
    apply hf
    exact congrArg (subspaceImageRepresentation ρ U.toSubmodule) h
  let N := restrictedSubgroup ρ U.toSubmodule L
  let eN : L ≃* N := (MonoidHom.ofInjective hfi).trans
    (MulEquiv.subgroupCongr (subgroupActionHom_range ρ U.toSubmodule L _))
  let : N.Normal := Normal.map inferInstance (subspaceActionHom ρ U.toSubmodule)
    (stabilizerRepresentation ρ U.toSubmodule).asGroupHom.rangeRestrict_surjective
  have hN : IsSQTK KnownSimple.IsKnownSimple N := hL.knownSimple_of_equiv eN
  have hirr : IsIrreducible ((subspaceImageRepresentation ρ U.toSubmodule).comp N.subtype) := by
    apply (irreducible_comp_surjective_iff eN.toMonoidHom eN.surjective _).mp
    exact hi
  exact odd_prime_constituent_actor_ratio hp (subspaceImageRepresentation ρ U.toSubmodule)
    (subspaceImageRepresentation_injective ρ U.toSubmodule) N hN hirr
    (eN.symm.trans e) C hC.1 hC.2.1


private theorem odd_prime_pair_moved_actor_false
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L K : Subgroup G) [L.Normal] [K.Normal]
    [Group.IsPerfect K] [Nontrivial K]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (e : L ≃* PSL(2,ZMod p))
    (hi : IsIrreducible (ρ.comp (L ⊔ K).subtype))
    (hc : K ≤ centralizer (L : Set G))
    (A : Subgroup G) (hA : A ∈ QhatStar ρ)
    (hsmall : cubicRatio ρ ≤ 2) (hmove : ¬ A ≤ centralizer (L : Set G)) : False := by
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv e.symm
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  let : IsSimpleGroup L := e.isSimpleGroup
  let : IsIrreducible ρ := irreducible_of_subgroup_restriction ρ (L ⊔ K) hi
  obtain ⟨U,hU,_,hC,hd⟩ := exists_constituent_drop_of_irreducible_pair ρ L K hi hf hc A hA hmove
  have hLn : L ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot L).mp inferInstance
  have hfix : Representation.invariants (ρ.comp L.subtype) = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf inferInstance L hLn
  have hfaith := simple_subrepresentation_faithful_of_fixed_eq_bot (ρ.comp L.subtype)
    hfix U ((Subrepresentation.irreducible_iff_isAtom U).mp hU).ne_bot
  have hb := odd_prime_subspace_actor_ratio hp ρ L hL e U hU hfaith _ hC
  exact (not_lt_of_ge hsmall) (hb.trans hd)

/-- A faithful irreducible pair of odd prime-field PSL₂ groups has no small
cubic actor preserving both factors. Ambient outer automorphisms are allowed. -/
theorem odd_prime_pair_cubicRatio_gt
    (hp : 11 ≤ p)
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L K : Subgroup G) [L.Normal] [K.Normal]
    (hS : IsSQTK KnownSimple.IsKnownSimple PSL(2,ZMod p))
    (eL : L ≃* PSL(2,ZMod p)) (eK : K ≃* PSL(2,ZMod p))
    (hi : IsIrreducible (ρ.comp (L ⊔ K).subtype))
    (hc : K ≤ centralizer (L : Set G)) : 2 < cubicRatio ρ := by
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv eL.symm
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv eK.symm
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  let : Nontrivial L := eL.surjective.nontrivial
  let : Nontrivial K := eK.surjective.nontrivial
  by_contra! hsmall
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hsmall
  rcases pair_actor_moves_factor ρ L K hi hf A hA.1.2.1 with hmove | hmove
  · exact odd_prime_pair_moved_actor_false hp ρ hf L K (hS.knownSimple_of_equiv eL.symm)
      eL hi hc A hA hsmall hmove
  · exact odd_prime_pair_moved_actor_false hp ρ hf K L (hS.knownSimple_of_equiv eK.symm)
      eK (by rwa [sup_comm]) (le_centralizer_iff.mp hc) A hA hsmall hmove

/-- A preserving cubic actor is excluded using its actual factor images. -/
theorem odd_prime_square_preserving_actor_false
    (hp : 11 ≤ p)
    (hS : IsSQTK KnownSimple.IsKnownSimple PSL(2,ZMod p))
    (σ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryTwo A)
    (hcubic : IsCubic (normalizerRepresentation σ) A)
    (hsmall : fixedCodim (normalizerRepresentation σ) A ≤ 2 * rank A)
    (hleft : ∀ a ∈ A, a.val ∈ normalizer
      (((⊤ : Subgroup PSL(2,ZMod p)).prod ⊥).map σ.asGroupHom : Set _))
    (hright : ∀ a ∈ A, a.val ∈ normalizer
      (((⊥ : Subgroup PSL(2,ZMod p)).prod ⊤).map σ.asGroupHom : Set _)) : False := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let S := PSL(2,ZMod p)
  let P : Subgroup (S × S) := (⊤ : Subgroup S).prod ⊥
  let Q : Subgroup (S × S) := (⊥ : Subgroup S).prod ⊤
  let J : Subgroup (Module.End (ZMod 2) V)ˣ := P.map σ.asGroupHom
  let K : Subgroup (Module.End (ZMod 2) V)ˣ := Q.map σ.asGroupHom
  let H := normalizer (J : Set (Module.End (ZMod 2) V)ˣ) ⊓
    normalizer (K : Set (Module.End (ZMod 2) V)ˣ)
  have hJH : J ≤ H := by
    rintro _ ⟨g,hg,rfl⟩
    exact ⟨P.le_normalizer_map σ.asGroupHom ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩,
      Q.le_normalizer_map σ.asGroupHom ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩⟩
  have hKH : K ≤ H := by
    rintro _ ⟨g,hg,rfl⟩
    exact ⟨P.le_normalizer_map σ.asGroupHom ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩,
      Q.le_normalizer_map σ.asGroupHom ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩⟩
  let L := J.subgroupOf H
  let R := K.subgroupOf H
  let : L.Normal := (normal_subgroupOf_iff_le_normalizer hJH).mpr inf_le_left
  let : R.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr inf_le_right
  let ρ : Representation (ZMod 2) H V := (Units.coeHom _).comp H.subtype
  have hρ : Function.Injective ρ := fun _ _ h => Subtype.ext (Units.ext h)
  let j : S × S →* H := σ.asGroupHom.codRestrict H (fun g =>
    ⟨P.le_normalizer_map σ.asGroupHom ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩,
      Q.le_normalizer_map σ.asGroupHom ⟨g,by rw [normalizer_eq_top]; trivial,rfl⟩⟩)
  have hj : Function.Injective j := fun _ _ h => hf (congrArg (fun x : H => x.val.val) h)
  have hjrange : j.range = L ⊔ R := by
    apply le_antisymm
    · rintro _ ⟨⟨x,y⟩,rfl⟩
      have he : j (x,y) = j (x,1) * j (1,y) := by rw [←map_mul]; simp
      rw [he]
      exact (L ⊔ R).mul_mem (mem_sup_left ⟨(x,1),⟨mem_top _,rfl⟩,rfl⟩)
        (mem_sup_right ⟨(1,y),⟨rfl,mem_top _⟩,rfl⟩)
    · apply sup_le
      · rintro x ⟨g,_,hg⟩
        exact ⟨g,Subtype.ext hg⟩
      · rintro x ⟨g,_,hg⟩
        exact ⟨g,Subtype.ext hg⟩
  let eN : (S × S) ≃* ↥(L ⊔ R) :=
    (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hjrange)
  have hirr : IsIrreducible (ρ.comp (L ⊔ R).subtype) :=
    (irreducible_comp_surjective_iff eN.toMonoidHom eN.surjective _).mp hi
  let jL : S →* L := (j.comp (MonoidHom.inl S S)).codRestrict L
    (fun x => ⟨(x,1),⟨mem_top _,rfl⟩,rfl⟩)
  let jR : S →* R := (j.comp (MonoidHom.inr S S)).codRestrict R
    (fun x => ⟨(1,x),⟨rfl,mem_top _⟩,rfl⟩)
  have heL : Function.Bijective jL := by
    constructor
    · intro x y h
      exact congrArg Prod.fst (hj (congrArg Subtype.val h))
    · rintro ⟨z,g,hg,hz⟩
      refine ⟨g.1,Subtype.ext (Subtype.ext ?_)⟩
      change σ.asGroupHom (g.1,1) = z.val
      have he : (g.1,1) = g := Prod.ext rfl (mem_bot.mp hg.2).symm
      exact (congrArg σ.asGroupHom he).trans hz
  have heR : Function.Bijective jR := by
    constructor
    · intro x y h
      exact congrArg Prod.snd (hj (congrArg Subtype.val h))
    · rintro ⟨z,g,hg,hz⟩
      refine ⟨g.2,Subtype.ext (Subtype.ext ?_)⟩
      change σ.asGroupHom (1,g.2) = z.val
      have he : (1,g.2) = g := Prod.ext (mem_bot.mp hg.1).symm rfl
      exact (congrArg σ.asGroupHom he).trans hz
  have hcomm : R ≤ centralizer (L : Set H) := by
    intro k hk l hl
    obtain ⟨x,hx⟩ := heL.2 ⟨l,hl⟩
    obtain ⟨y,hy⟩ := heR.2 ⟨k,hk⟩
    have hx' : j (x,1) = l := congrArg Subtype.val hx
    have hy' : j (1,y) = k := congrArg Subtype.val hy
    rw [←hx',←hy',←map_mul,←map_mul]
    simp
  let f : A →* H := ((linearNormalizer σ).subtype.comp A.subtype).codRestrict H
    (fun a => ⟨hleft a a.property,hright a a.property⟩)
  have hfi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => z.val) h
  let E := f.range
  let : IsElementaryAbelian 2 A := hA.2
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hE : IsElementaryTwo E := by
    refine ⟨?_,inferInstance⟩
    intro hz
    have hh : ∀ a : A, a = 1 := fun a => hfi ((mem_bot.mp (hz ▸ (show f a ∈ E from ⟨a,rfl⟩))).trans f.map_one.symm)
    apply hA.1
    exact bot_unique (fun a ha => congrArg (fun b : A => b.val) (hh ⟨a,ha⟩))
  have hcod : fixedCodim ρ E = fixedCodim (normalizerRepresentation σ) A := by
    have he : fixedSpace ρ E = fixedSpace (normalizerRepresentation σ) A := by
      ext v
      constructor
      · intro hv a
        exact hv ⟨f a,⟨a,rfl⟩⟩
      · rintro hv ⟨_,a,rfl⟩
        exact hv a
    unfold fixedCodim
    rw [he]
  have hrank : rank E = rank A := (congrArg (Nat.log 2) (Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv)).symm
  have hb : cubicRatio ρ ≤ 2 := by
    apply (cubicRatio_le_nat_iff ρ 2).mpr
    refine ⟨E,hE,?_,?_⟩
    · rintro _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ _ ⟨c,rfl⟩ v
      exact hcubic a a.property b b.property c c.property v
    · rw [hcod,hrank]
      exact hsmall
  exact (not_le_of_gt (odd_prime_pair_cubicRatio_gt hp ρ hρ L R hS
    (MulEquiv.ofBijective jL heL).symm (MulEquiv.ofBijective jR heR).symm hirr hcomm)) hb

/-- The full linear normalizer of an irreducible faithful odd-prime square
has cubic ratio greater than two. No factor-preservation premise remains. -/
theorem odd_prime_square_normalizer_cubicRatio_gt
    (hp : 11 ≤ p)
    (hS : IsSQTK KnownSimple.IsKnownSimple PSL(2,ZMod p))
    (σ : Representation (ZMod 2) (PSL(2,ZMod p) × PSL(2,ZMod p)) V)
    (hi : σ.IsIrreducible) (hf : Function.Injective σ) :
    2 < cubicRatio (normalizerRepresentation σ) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  by_contra! hsmall
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation σ) 2).mp hsmall
  let : IsElementaryAbelian 2 A := hA.2
  have hleft := SL2.odd_prime_square_small_actor_preserves hp σ hi hf A hd
  let S := PSL(2,ZMod p)
  let δ : MulAut (S × S) := MulEquiv.prodComm
  let τ : Representation (ZMod 2) (S × S) V := σ.comp δ.toMonoidHom
  have himage : actionImage τ = actionImage σ := by
    ext x
    constructor
    · rintro ⟨g,rfl⟩
      exact ⟨δ g,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨g,rfl⟩ := δ.surjective g
      exact ⟨g,Units.ext rfl⟩
  have hn : linearNormalizer σ ≤ linearNormalizer τ := by
    unfold linearNormalizer
    rw [himage]
  let j := inclusion hn
  let C := A.map j
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.map j
  have hiτ : τ.IsIrreducible :=
    (irreducible_comp_surjective_iff δ.toMonoidHom δ.surjective σ).mpr hi
  have hfτ : Function.Injective τ := hf.comp δ.injective
  have hcod : fixedCodim (normalizerRepresentation τ) C =
      fixedCodim (normalizerRepresentation σ) A :=
    (fixedCodim_map_equivariant (normalizerRepresentation σ) (normalizerRepresentation τ)
      j (LinearEquiv.refl _ _) (fun _ _ => rfl) A).symm
  have hrank : rank C = rank A := rank_map_injective j (inclusion_injective hn) A
  have hτ := SL2.odd_prime_square_small_actor_preserves hp τ hiτ hfτ C (by
    rw [hcod,hrank]
    exact hd)
  have hfactor : ((⊤ : Subgroup S).prod ⊥).map τ.asGroupHom =
      ((⊥ : Subgroup S).prod ⊤).map σ.asGroupHom := by
    ext x
    constructor
    · rintro ⟨⟨g,h⟩,hg,rfl⟩
      exact ⟨(h,g),⟨hg.2,hg.1⟩,Units.ext rfl⟩
    · rintro ⟨⟨g,h⟩,hg,rfl⟩
      exact ⟨(h,g),⟨hg.2,hg.1⟩,Units.ext rfl⟩
  have hright : ∀ a ∈ A, a.val ∈ normalizer
      (((⊥ : Subgroup S).prod ⊤).map σ.asGroupHom : Set _) := by
    intro a ha
    have hh := hτ (j a) (mem_map_of_mem j ha)
    rwa [hfactor] at hh
  exact odd_prime_square_preserving_actor_false hp hS σ hi hf A hA hc hd hleft hright

end CFSG.Quasithin.ChapterD
