module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeTorus
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22PairRanks
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceWitnessTorus
public import CFSG.Quasithin.ChapterK.Section01To04.Mathieu.OctadGeometry.Reduction

/-!
# Degree one for the original M22 code pair

The full automizer bounds the selected elementary actor by rank five.
In degree two, its even rank is therefore four. The original quotient's
cubic fixes exactly the central intersection, of rank four, and the actor
fixes that space. Its native image contains an inner involution, contradicting
the cubic fixed-space kernel calculation. Thus the actual degree is one.
The covering quotient, internal conjugator and whole-module marking are retained.
Source: Aschbacher--Smith 8.2.3 and H.16.7, printed pp.715--716,405,
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

private theorem actor_normalizes (s : GeometricSelected H T M V I k i S) :
    V.map (MulAut.conj i.val⁻¹).toMonoidHom ⊓ (pCore 2 I).map I.subtype ≤
      normalizer (V : Set G) := by
  have hVI : V ≤ I := s.generate ▸ le_sup_left
  rw [← selected_actor_image I M V hVI S i s.twoConjugate]
  rintro _ ⟨a,ha,rfl⟩
  have hn := s.twoConjugate.sylow_le_normalizer (DihedralCubic.A_le_sylow s.twoConjugate ha)
  rw [←subgroupOf_normalizer_eq hVI] at hn
  exact hn

private theorem fixed_group_rank (X : Subgroup (Automizer V)) :
    rank (automizerFixedGroup V X) =
      Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) X) := by
  rw [rank,automizerFixedGroup,card_map_of_injective V.subtype_injective]
  change Nat.log 2 (Nat.card (fixedSpace (automizerRepresentation V) X)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Nat.log_pow (by decide : 1 < 2)]

/-- The actual degree-two pair contradicts the native cubic fixed-space calculation. -/
theorem m22_code_degree_two_impossible
    (s : GeometricSelected H T M V I 2 i S)
    (ha : primeRank 2 (Automizer V) ≤ 5)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (hinj : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) = m22OuterCodeRepresentation (a b) (E v)) : False := by
  let W := V.map (MulAut.conj i.val⁻¹).toMonoidHom
  let A := W ⊓ (pCore 2 I).map I.subtype
  let B := inducedAutomizer V A
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_le (show A ≤ W from inf_le_left)
  let : IsElementaryAbelian 2 B := inducedAutomizer_elementary V A (actor_normalizes s)
  let : IsElementaryAbelian 2 (B.map a) := IsElementaryAbelian.map _
  have hm : ∃ ξ : (I ⧸ pCore 2 I) ≃* PSL2 (BinaryGaloisField 2), True := by
    rcases s.models with ⟨_,ξ,_⟩ | ⟨m,hm,hk,_⟩ | ⟨hk,_⟩
    · exact ⟨ξ,trivial⟩
    · omega
    · omega
  obtain ⟨ξ,_⟩ := hm
  have hl := s.actor_rank_ge_twice_parameter
  have hu := (offender_rank_le_primeRank B).trans ha
  have hdiv := s.linear_actor_rank_dvd (by decide) ξ
  have hr : rank B = 4 := by change 4 ≤ rank B at hl; change 2 ∣ rank B at hdiv; omega
  obtain ⟨_,x,_,_,_,_,ho,hfix⟩ := s.linear_exists_torus_fixed (by decide) ξ
  have hx : orderOf x = 3 := ho
  have hc : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers,hx]
  have hi := s.actor_rank_identity
  have hv : rank V = 10 :=
    (Chapter7.log_card_eq_finrank V).trans (E.finrank_eq.trans finrank_m22Code)
  change rank (V ⊓ W) + 2 + rank B = rank V at hi
  rw [hr,hv] at hi
  have hz : Module.finrank (ZMod 2) (fixedSpace (automizerRepresentation V) (zpowers x)) = 4 := by
    rw [←fixed_group_rank,hfix]
    change rank (V ⊓ W) = 4
    omega
  have hsum := fixedCodim_add_finrank (automizerRepresentation V) (zpowers x)
  have hdim := E.finrank_eq.trans finrank_m22Code
  have hcod : fixedCodim (automizerRepresentation V) (zpowers x) = 6 := by omega
  have hmap (C : Subgroup (Automizer V)) :
      (fixedSpace (automizerRepresentation V) C).map E.toLinearMap =
        fixedSpace m22OuterCodeRepresentation (C.map a) :=
    fixedSpace_map_equivariant _ _ a E hE C
  have hlarge : rank (B.map a) = 4 := by rw [rank_map_injective a hinj,hr]
  have hB : IsElementaryTwo (B.map a) := ⟨by
    intro he; rw [he,Representation.BinaryOffender.rank_bot] at hlarge; omega,inferInstance⟩
  obtain ⟨y,hy,hy2,hyi⟩ := ChapterK.Mathieu.OctadGeometry.m22_exists_inner_involution
    (B.map a) hB (by omega)
  apply NormalizedShadowRows.M22CodeTorus.no_inner_involution_in_cubic_kernel
    ((zpowers x).map a) (by rw [card_map_of_injective hinj,hc])
    (by rw [←fixedCodim_map_equivariant _ _ a E hE]; exact hcod) y hy2
    ((m22ToPairStabilizer_mem_range_iff_fixed_zero y).mpr hyi)
  have hle : fixedSpace m22OuterCodeRepresentation ((zpowers x).map a) ≤
      fixedSpace m22OuterCodeRepresentation (B.map a) := by
    rw [←hmap,←hmap]
    exact Submodule.map_mono (s.fixedSpace_le_actor x hfix)
  intro v hv
  exact (hle hv) ⟨y,hy⟩

/-- The original geometric M22 code pair has degree one. -/
theorem m22_code_parameter_one
    (s : GeometricSelected H T M V I k i S)
    (ha : primeRank 2 (Automizer V) ≤ 5)
    (a : Automizer V →* MathieuCode.m22PairStabilizer) (hinj : Function.Injective a)
    (E : Additive V ≃ₗ[ZMod 2] M22Code)
    (hE : ∀ b v, E (automizerRepresentation V b v) = m22OuterCodeRepresentation (a b) (E v)) : k = 1 := by
  rcases s.parameter_one_or_two_of_rank_five ha with hk | hk
  · exact hk
  · subst k
    exact (s.m22_code_degree_two_impossible ha a hinj E hE).elim

end CFSG.Quasithin.Chapter8.Section02.HermitianSource.GeometricSelected
