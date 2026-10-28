module
public import CFSG.Quasithin.ChapterD.Section03.ConstituentDrop
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.IrreducibleBranch.LocalGroups
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SQTKSectionImage
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.JankoOneExclusion
public import Theory.Representation.BinaryOffender.SquareNormalizerActors
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.QuasisimpleRestrictionFitting
public import Theory.Representation.BinaryOffender.CubicSection

/-!
# Exclusion of a J₁ tensor on the original seed

A cubic actor on a faithful irreducible J₁ constituent is excluded by the
checked order-nineteen commutator bound, including ambient automorphisms.
Strict constituent descent therefore excludes the component-preserving
actors on a faithful irreducible J₁ square. The full normalizer has no
additional small actors: its involutory factor automorphisms are inner,
while an exchange has rank at most four and displacement at least nine.

The original Chapter10 seed application retains the actual quotient maps
and both possible seed orientations. Source: Aschbacher--Smith D.3.7,
printed pp.197--199, and K.4, printed p.457.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
private theorem janko_quasisimple : IsQuasisimple Janko1.Model := {
  toIsPerfect := inferInstance
  simple := ((QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_simple_perfect (G := Janko1.Model))).trans
      (QuotientGroup.quotientBot (G := Janko1.Model))).isSimpleGroup }
attribute [local instance] janko_quasisimple
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

theorem janko_constituent_actor_ratio
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (L : Subgroup G) [L.Normal]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (hi : IsIrreducible (ρ.comp L.subtype))
    (e : L ≃* Janko1.Model)
    (A : Subgroup G) (hA : IsElementaryTwo A) (hc : IsCubic ρ A) :
    2 < actionRatio ρ A := by
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
  let eQ : (N ⧸ center N) ≃* Janko1.Model :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      ((QuotientGroup.quotientBot (G := N)).trans (eN.trans e))
  have hsource : ChapterK.SporadicCatalogue.SourceHypotheses τ := {
    sqtk := hs.sqtk
    quasisimple := hs.fitting.symm ▸ hs.quasisimple
    faithful := hs.faithful
    irreducible := hs.fitting.symm ▸ hs.irreducible
    cubic_le_two := hs.smallCubic }
  apply ChapterK.SporadicCatalogue.sourceExclusion_j1 τ hsource
  exact (congrArg (fun J : Subgroup H => Nonempty (J ⧸ center J ≃* Janko1.Model))
    hs.fitting).mpr ⟨eQ⟩
end CFSG.Quasithin.ChapterD

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
attribute [local instance] janko_quasisimple
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The same lower bound on the literal faithful image of a constituent. -/
theorem janko_subspace_actor_ratio
    (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
    (hL : IsSQTK KnownSimple.IsKnownSimple L)
    (e : L ≃* Janko1.Model)
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
  exact janko_constituent_actor_ratio (subspaceImageRepresentation ρ U.toSubmodule)
    (subspaceImageRepresentation_injective ρ U.toSubmodule) N hN hirr
    (eN.symm.trans e) C hC.1 hC.2.1
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
attribute [local instance] janko_quasisimple
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A faithful irreducible J₁ square has no cubic actor of ratio at most two. -/
theorem janko_square_cubicRatio_gt
    (hS : IsSQTK KnownSimple.IsKnownSimple (Janko1.Model))
    (ρ : Representation (ZMod 2) (Janko1.Model × Janko1.Model) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) : 2 < cubicRatio ρ := by
  let S := Janko1.Model
  have hZ : center S = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal _ inferInstance).resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative S (center_eq_top_iff.mp h))
  by_contra! hsmall
  obtain ⟨A,hA⟩ := (QhatStar_nonempty_iff ρ).mpr hsmall
  obtain ⟨J,hJ,U,hU,_,hC,hd⟩ := square_actor_constituent_drop hZ ρ hi hf A hA
  have hnormal : J.Normal := by
    rcases hJ with rfl | rfl <;> infer_instance
  let := hnormal
  have he : Nonempty (J ≃* S) := by
    rcases hJ with rfl | rfl
    · exact ⟨{
        toFun x := x.val.1
        invFun x := ⟨(x,1),mem_top x,rfl⟩
        left_inv x := Subtype.ext (Prod.ext rfl (mem_bot.mp x.property.2).symm)
        right_inv _ := rfl
        map_mul' _ _ := rfl }⟩
    · exact ⟨{
        toFun x := x.val.2
        invFun x := ⟨(1,x),rfl,mem_top x⟩
        left_inv x := Subtype.ext (Prod.ext (mem_bot.mp x.property.1).symm rfl)
        right_inv _ := rfl
        map_mul' _ _ := rfl }⟩
  let e : J ≃* S := he.some
  let : IsSimpleGroup J := e.isSimpleGroup
  have hJn : J ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot J).mp inferInstance
  have hfix : Representation.invariants (ρ.comp J.subtype) = ⊥ :=
    fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hf hi J hJn
  have hfaith := simple_subrepresentation_faithful_of_fixed_eq_bot (ρ.comp J.subtype)
    hfix U ((Subrepresentation.irreducible_iff_isAtom U).mp hU).ne_bot
  have hb := janko_subspace_actor_ratio ρ J ((IsSQTK.equiv e).mpr hS)
    e U hU hfaith _ hC
  exact (not_lt_of_ge hsmall) (hb.trans hd)
end CFSG.Quasithin.ChapterD

namespace CFSG.Quasithin.ChapterD
attribute [local instance] janko_quasisimple

private theorem janko_automorphism_rank_le_three : primeRank 2 (MulAut Janko1.Model) ≤ 3 := by
  have hi : Function.Injective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model) :=
    MulAut.conj_injective_of_center_eq_bot center_eq_bot_of_simple_perfect
  let e := MulEquiv.ofBijective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model)
    ⟨hi,Janko1.OuterCertificate.aut_inner⟩
  have hc : Nat.card (MulAut Janko1.Model) = 175560 :=
    (Nat.card_congr e.toEquiv).symm.trans Janko1.card_model
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro A hA
  let := hA
  have hd := A.card_subgroup_dvd_card
  rw [hc] at hd
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hn3 : n ≤ 3 := by
    by_contra! hn3
    have h16 : 16 ∣ 175560 :=
      (show 16 ∣ 2 ^ n from pow_dvd_pow 2 (by omega : 4 ≤ n)).trans (hn ▸ hd)
    norm_num at h16
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hn3

private theorem janko_prime_degree : orderOf (2 : ZMod 19) = 18 := by
  apply (orderOf_eq_iff (by decide : 0 < 18)).mpr
  constructor
  · decide
  · intro m hm hpos
    interval_cases m <;> norm_num at * <;> decide

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every small elementary actor in the full J₁-square normalizer belongs
 to the literal square image, including actors with twisted exchanges. -/
theorem janko_square_small_actor_le_image
    (ρ : Representation (ZMod 2) (Janko1.Model × Janko1.Model) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ)
    (A : Subgroup (linearNormalizer ρ)) [IsElementaryAbelian 2 A]
    (hsmall : fixedCodim (normalizerRepresentation ρ) A ≤ 2 * rank A) :
    A ≤ (actionImage ρ).subgroupOf (linearNormalizer ρ) := by
  apply small_actor_le_square_image center_eq_bot_of_simple_perfect
    (fun α _ => (Janko1.OuterCertificate.aut_inner α).imp (fun _ h => h.symm))
    (by decide : Nat.Prime 19) (by decide)
    (Janko1.a * Janko1.b * Janko1.a * Janko1.b ^ 2) Janko1.orderOf_abab_sq
    (by rw [janko_prime_degree]; have := janko_automorphism_rank_le_three; omega)
    ρ hi hf A hsmall

/-- The whole linear normalizer of a faithful irreducible J₁ square has
 cubic ratio above two. -/
theorem janko_square_normalizer_cubicRatio_gt
    (hS : IsSQTK KnownSimple.IsKnownSimple (Janko1.Model))
    (ρ : Representation (ZMod 2) (Janko1.Model × Janko1.Model) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) :
    2 < cubicRatio (normalizerRepresentation ρ) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  by_contra! hsmall
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation ρ) 2).mp hsmall
  let : IsElementaryAbelian 2 A := hA.2
  have hle := janko_square_small_actor_le_image ρ hi hf A hd
  let N := (actionImage ρ).subgroupOf (linearNormalizer ρ)
  let E : N ≃* (Janko1.Model × Janko1.Model) :=
    (subgroupOfEquivOfLe (actionImage ρ).le_normalizer).trans
      (PerfectNormalizer.imageEquiv ρ hf).symm
  let C := A.subgroupOf N
  have hC : IsElementaryTwo C := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hle⟩
    intro he
    change A.subgroupOf N = ⊥ at he
    apply hA.1
    rw [←map_subgroupOf_eq_of_le hle,he,Subgroup.map_bot]
  have hsmallN : cubicRatio ((normalizerRepresentation ρ).comp N.subtype) ≤ 2 := by
    apply (cubicRatio_le_nat_iff _ 2).mpr
    refine ⟨C,hC,?_,?_⟩
    · intro a ha b hb c hc' v
      exact hc a ha b hb c hc' v
    · rw [fixedCodim_subgroupOf (normalizerRepresentation ρ) hle,rank_subgroupOf hle]
      exact hd
  have hinner : cubicRatio ρ ≤ 2 :=
    cubicRatio_comp_equiv_le_nat ((normalizerRepresentation ρ).comp N.subtype) E.symm 2 hsmallN
  exact (not_le_of_gt (janko_square_cubicRatio_gt hS ρ hi hf)) hinner
end CFSG.Quasithin.ChapterD
