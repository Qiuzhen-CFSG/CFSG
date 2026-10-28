module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuFiveBounds
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.StrictCode
public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.Octad.SourceInvolutions

/-!
# The strict quadratic bound needed by the original M24 parabolics

A rank-two elementary cocode actor cannot have fixed codimension four:
the pointwise stabilizer of a Sylow-central involution's fixed space is its
order-two cyclic group. The other involution class already has codimension
five. Combining this with the proved quadratic-actor order bound gives q > 2.
The existing strict code bound and literal equivariant markings cover both
M24 rows. No additional finite computation is required.

NonFFSourceMathieuM24Parabolic uses the bound to prove escape from every
outside H-star two-core and establish the genuine E.2.8 setup on that H.
Source: Aschbacher--Smith H.15.2(5), Table B.4.5 and 8.2.2(1), printed
pp.398--399,714--715, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterE
open Sporadic.Mathieu MathieuCode MathieuCode.QuadraticActors
open MathieuCode.CocodeOctad.Involutions
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuQuadratic

/-- A noncyclic elementary subgroup moves at least five cocode dimensions. -/
theorem cocode_rank_two_fixedCodim (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hr : rank A = 2) : 5 ≤ fixedCodim cocodeRepresentation A := by
  let := hA.2
  obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ho : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  have hle := fixedCodim_mono cocodeRepresentation (zpowers_le.mpr ha)
  rcases M24InvolutionCentralizers.involution_classes a ho with hz | ht
  · have hd := fixedCodim_of_isConj_z a hz
    by_contra hsmall
    have heq : fixedSpace cocodeRepresentation A =
        fixedSpace cocodeRepresentation (zpowers a) := by
      apply Submodule.eq_of_le_of_finrank_eq (Representation.BinaryOffender.fixedSpace_antitone _ (zpowers_le.mpr ha))
      have h1 := fixedCodim_add_finrank cocodeRepresentation A
      have h2 := fixedCodim_add_finrank cocodeRepresentation (zpowers a)
      omega
    have hsub : A ≤ subspaceKernel cocodeRepresentation
        (fixedSpace cocodeRepresentation (zpowers a)) ⊤ := by
      rw [←heq]
      intro b hb
      exact ⟨mem_top b,fun v hv => hv ⟨b,hb⟩⟩
    rw [pointwiseCentralizer_of_isConj_z a hz] at hsub
    have hc := card_le_of_le hsub
    rw [hA.card_eq_two_pow_rank,hr,Nat.card_zpowers,ho] at hc
    norm_num at hc
  · rw [fixedCodim_of_isConj_t a ht] at hle
    exact hle

/-- The native M24 cocode has strict quadratic ratio greater than two. -/
theorem cocode_quadraticRatio_gt_two : 2 < quadraticRatio cocodeRepresentation := by
  by_contra! hle
  obtain ⟨A,hA,hq,hsmall⟩ := (quadraticRatio_le_iff cocodeRepresentation (by simp)).mp hle
  have hdim := (actionRatio_le_nat_iff cocodeRepresentation hA 2).mp hsmall
  let := hA.2
  have hr : rank A ≤ 2 :=
    (Nat.log_mono_right (m24_cocode_card_le_four A hq) : Nat.log 2 (Nat.card A) ≤ Nat.log 2 4)
  by_cases he : rank A = 2
  · have hb := cocode_rank_two_fixedCodim A hA he
    omega
  · have hp := hA.rank_pos
    obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ho : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hd := m24_cocode_involution_gt_two a ho
    have hb := fixedCodim_mono cocodeRepresentation (zpowers_le.mpr ha)
    omega

/-- The strict bound transports through either actual M24 module marking. -/
theorem marked_quadraticRatio_gt_two
    {X E : Type*} [Group X] [Finite X] [AddCommGroup E] [Module (ZMod 2) E]
    (ρ : Representation (ZMod 2) X E) (hm : MathieuSmall.IsM24ToddOrDual ρ) :
    2 < quadraticRatio ρ := by
  obtain ⟨a,hc | hd⟩ := hm
  · obtain ⟨F⟩ := hc
    exact cocode_quadraticRatio_gt_two.trans_le
      (quadraticRatio_le_of_injective_equivariant ρ cocodeRepresentation
        a.toMonoidHom a.injective F.toLinearEquiv
        (fun g v => LinearMap.congr_fun (F.isIntertwining' g) v))
  · obtain ⟨F⟩ := hd
    exact StrictCode.code_quadraticRatio_gt_two.trans_le
      (quadraticRatio_le_of_injective_equivariant ρ codeRepresentation
        a.toMonoidHom a.injective F.toLinearEquiv
        (fun g v => LinearMap.congr_fun (F.isIntertwining' g) v))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuQuadratic
