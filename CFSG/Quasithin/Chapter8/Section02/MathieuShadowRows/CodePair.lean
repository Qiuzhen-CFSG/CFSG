module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.Cubic
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeTorus
public import Theory.Mathieu.SmallModuleRanks.M24
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessTorus

/-!
# Degree-two exclusion for an original M24 code pair

The full original automizer bounds the elementary selected actor by rank six.
For degree two its rank is even and at least four. At rank four the source
cubic has a five-dimensional fixed space, whose pointwise kernel is exactly
the cubic; the actor cannot lie in that kernel. At rank six the cubic has a
three-dimensional fixed space, contradicting the native sextet/trio fixed-space
calculation. All markings and fixed spaces refer to the original whole module.

Consequently the remaining geometric degrees are one and three. The comparison
with the ambient E-generation parameter is a separate source obligation; it is
not inferred from the quotient model here.

Source: Aschbacher--Smith H.16.6--7 and 8.2.3, printed pp.404--405,715--716,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
open ChapterE Offenders.Parabolic Offenders.Parabolic.Construction
open BenderSuzuki.PFAppendixIII BenderSuzuki.Converse BenderSuzuki.MatrixGroups
open Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G]
  {H T M V I : Subgroup G} [IsElementaryAbelian 2 V]
  {k : ℕ} {i : I} {S : Sylow 2 I}

private theorem original_actor_normalizes (s : GeometricSelected H T M V I k i S) :
    V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ≤
      normalizer (V : Set G) := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  rw [← selected_actor_image I M V hVI S i s.twoConjugate]
  rintro _ ⟨a,ha,rfl⟩
  have hn := s.twoConjugate.sylow_le_normalizer (DihedralCubic.A_le_sylow s.twoConjugate ha)
  rw [←subgroupOf_normalizer_eq hVI] at hn
  exact hn

/-- The full original automizer bounds the original selected actor. -/
theorem m24_actor_rank_le_six (s : GeometricSelected H T M V I k i S)
    (a : Automizer V ≃* M24) :
    rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) ≤ 6 := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 (inducedAutomizer V A) :=
    inducedAutomizer_elementary V A (original_actor_normalizes s)
  exact (offender_rank_le_primeRank _).trans
    ((_root_.primeRank_le_of_injective 2 a.toMonoidHom a.injective).trans m24_twoRank_le_six)

/-- This bound uses the actual actor, without a degree/generation divisibility premise. -/
theorem m24_parameter_le_three (s : GeometricSelected H T M V I k i S)
    (a : Automizer V ≃* M24) : k ≤ 3 := by
  have hl := s.actor_rank_ge_twice_parameter
  have hu := s.m24_actor_rank_le_six a
  omega

private theorem fixed_group_rank (X : Subgroup (Automizer V)) :
    rank (automizerFixedGroup V X) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) X) := by
  rw [rank,automizerFixedGroup,card_map_of_injective V.subtype_injective]
  change Nat.log 2 (Nat.card (fixedSpace (automizerRepresentation V) X)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)]

theorem m24_code_not_rank_four
    (s : GeometricSelected H T M V I 2 i S)
    (a : Automizer V ≃* M24) (E : Additive V ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) = codeRepresentation (a b) (E v))
    (hr : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) = 4) : False := by
  have hm : ∃ ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2), True := by
    rcases s.models with ⟨_,ξ,_⟩ | ⟨m,hm,hk,_⟩ | ⟨hk,_⟩
    · exact ⟨ξ,trivial⟩
    · omega
    · omega
  obtain ⟨ξ,_⟩ := hm
  obtain ⟨y,x,_,_,_,_,ho,hfix⟩ := s.linear_exists_torus_fixed (by decide) ξ
  have hx : orderOf x = 3 := ho
  have hc : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers,hx]
  have hd := s.actor_rank_identity
  dsimp only at hd
  have hv : rank V = 11 :=
    (Chapter7.log_card_eq_finrank V).trans (E.finrank_eq.trans finrank_code)
  rw [hr,hv] at hd
  have hz : Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 5 := by
    rw [← fixed_group_rank,hfix]
    omega
  have hsum := fixedCodim_add_finrank (automizerRepresentation V) (zpowers x)
  have hdim := E.finrank_eq.trans finrank_code
  have hcod : fixedCodim (automizerRepresentation V) (zpowers x) = 6 := by omega
  have hk := NormalizedShadowRows.Cubic.fixedSpace_kernel_eq_equivariant
    (automizerRepresentation V) a E hE (zpowers x) hc hcod
  have hle : inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype) ≤ zpowers x := by
    rw [← hk]
    intro b hb
    refine ⟨mem_top _,?_⟩
    intro v hvs
    exact (s.fixedSpace_le_actor x hfix hvs) ⟨b,hb⟩
  have hl := Nat.log_mono_right (b := 2) (Subgroup.card_le_of_le hle)
  change rank _ ≤ Nat.log 2 (Nat.card (zpowers x)) at hl
  rw [hr,hc] at hl
  norm_num at hl

/-- The original rank-six actor contradicts the native cubic fixed-space calculation. -/
theorem m24_code_not_rank_six
    (s : GeometricSelected H T M V I 2 i S)
    (a : Automizer V ≃* M24) (E : Additive V ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) = codeRepresentation (a b) (E v))
    (hr : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) = 6) : False := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let B := inducedAutomizer V A
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 B := inducedAutomizer_elementary V A (original_actor_normalizes s)
  let : IsElementaryAbelian 2 (B.map a.toMonoidHom) := IsElementaryAbelian.map _
  have hm : ∃ ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2), True := by
    rcases s.models with ⟨_,ξ,_⟩ | ⟨m,hm,hk,_⟩ | ⟨hk,_⟩
    · exact ⟨ξ,trivial⟩
    · omega
    · omega
  obtain ⟨ξ,_⟩ := hm
  obtain ⟨y,x,_,_,_,hx,ho,hfix⟩ := s.linear_exists_torus_fixed (by decide) ξ
  have hxr : orderOf x = 3 := ho
  have hd := s.actor_rank_identity
  dsimp only at hd
  have hv : rank V = 11 :=
    (Chapter7.log_card_eq_finrank V).trans (E.finrank_eq.trans finrank_code)
  rw [hr,hv] at hd
  have hz : Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 3 := by
    rw [← fixed_group_rank,hfix]
    omega
  have hmap (D : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) D).map E.toLinearMap =
        fixedSpace codeRepresentation (D.map a.toMonoidHom) :=
    fixedSpace_map_equivariant _ _ a.toMonoidHom E hE D
  have hX : (zpowers x).map a.toMonoidHom = zpowers (a x) := MonoidHom.map_zpowers _ _
  apply NormalizedShadowRows.CodeTorus.no_cubic_fixed_three_of_rank_six
    (B.map a.toMonoidHom)
    (by rw [rank_map_injective a.toMonoidHom a.injective]; exact hr) (a x)
    ((a.orderOf_eq x).trans hxr)
  · exact B.le_normalizer_map a.toMonoidHom
      (mem_map_of_mem a.toMonoidHom (s.normalizes_actor hx))
  · rw [←hX,←hmap,←hmap]
    exact Submodule.map_mono (s.fixedSpace_le_actor x hfix)
  · rw [←hX,←hmap,LinearEquiv.finrank_map_eq]
    exact hz

/-- H.16.6--7 exclude degree two on the original selected M24 code pair. -/
theorem m24_code_degree_two_impossible
    (s : GeometricSelected H T M V I 2 i S)
    (a : Automizer V ≃* M24) (E : Additive V ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) = codeRepresentation (a b) (E v)) : False := by
  have hm : ∃ ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2), True := by
    rcases s.models with ⟨_,ξ,_⟩ | ⟨m,hm,hk,_⟩ | ⟨hk,_⟩
    · exact ⟨ξ,trivial⟩
    · omega
    · omega
  obtain ⟨ξ,_⟩ := hm
  have hl := s.actor_rank_ge_twice_parameter
  have hu := s.m24_actor_rank_le_six a
  have hdiv := s.linear_actor_rank_dvd (by decide) ξ
  have hr : rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) = 4 ∨
      rank (inducedAutomizer V
      (V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype)) = 6 := by omega
  rcases hr with hr | hr
  · exact s.m24_code_not_rank_four a E hE hr
  · exact s.m24_code_not_rank_six a E hE hr

/-- The only remaining geometric degrees of a whole M24 code pair are one and three.
Degree three still needs the source comparison with the ambient generation bound. -/
theorem m24_code_parameter_one_or_three
    (s : GeometricSelected H T M V I k i S)
    (a : Automizer V ≃* M24) (E : Additive V ≃ₗ[ZMod 2] Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) = codeRepresentation (a b) (E v)) :
    k = 1 ∨ k = 3 := by
  have hp := s.positive
  have hu := s.m24_parameter_le_three a
  have hn : k ≠ 2 := by
    intro he
    subst k
    exact s.m24_code_degree_two_impossible a E hE
  omega

end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
