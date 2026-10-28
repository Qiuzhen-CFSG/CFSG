module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.ResidualCoordinates.MarkedDual
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.NaturalAction
public import Theory.Representation.PSL3Two.NaturalDualMarking
public import Theory.GroupTheory.PlaneConjugateSpan
public import Theory.GroupTheory.CommutatorPreimage.Membership
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableNormalizer.LocalSylow

/-!
# The original seed in compatible natural and dual coordinates

The original plane and the H-fixed factor imply that the dual seed is fixed
by the literal local Sylow. Its nonvanishing follows from the suitable
index-two condition. A simultaneous change of basis then normalizes the
natural point and places this same dual seed in its annihilator plane.
The final application constructs the residual eight-group, rank four, and
escape from M through `source_residual_span_of_marked_dual`.

The genuine single-L3(2) supports, separation from the fixed factor, full
paired action, and decomposition of the same seed remain explicit earlier
source inputs. Their producer is qt-e-terminal-natural-support-decomposition;
a generic hatted direct sum or central overlap does not supply them. This
module is a conditional source implication, not original 14.6.24 by itself.
The precise residual-placement premise is retained; its discharge through
the single component and 14.6.23 belongs to qt-e-terminal-component-alternatives
and the final assembly qt-e-suitable-component-marking. Final residual assembly
remains qt-e-terminal-dual-residual-coordinates.

Source: Aschbacher--Smith, 14.6.20--24 and printed pp.1038--1042, especially
the final seed decomposition on p.1042. All subgroups and residual maps are
literal, with H=Mc and P the quotient centralizer of the same suitable u.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)

/-- The dual factor of the same seed is fixed by the literal local Sylow.
This uses fixation of the original plane, u, and the whole fixed factor. -/
theorem seed_dual_factor_fixed
    (hcard : Nat.card D.V = 4) (hVU : D.V ≤ D.UH) (C : Subgroup G) (hCU : C ≤ D.UH)
    (hfixed : ∀ x ∈ D.H, ∀ c ∈ C, ⁅c,x⁆ ∈ D.V₁)
    (u b c v : G) (hu : u ∈ D.UH) (hc : c ∈ C)
    (hv : v ∈ D.V) (hseed : v*(u*b*c)⁻¹ ∈ D.V₁) :
    ∀ x ∈ suitableQuotientCentralizer h u, ⁅b,x⁆ ∈ D.V₁ := by
  let S := suitableQuotientCentralizer h u
  let J := commutatorPreimage D.UH S D.V₁
  have hZU : D.V₁ ≤ D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hUZ : D.UH ≤ normalizer (D.V₁ : Set G) :=
    h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hZJ : D.V₁ ≤ J := by
    apply le_commutatorPreimage hZU
    apply commutator_le.mpr
    intro z hz x hx
    have hxz : Commute z x := h.H_centralizes (h.T_le_H hx.1) z hz
    rw [hxz.commutator_eq]
    exact D.V₁.one_mem
  have hVJ : D.V ≤ J := le_commutatorPreimage hVU
    ((commutator_mono le_rfl inf_le_left).trans
      (plane_line_commutator D.V D.V₁ (D.T : Subgroup G)
        (h.point_lt.le.trans h.plus_le) hcard h.point_card h.T_normalizes_V h.normalizes_point))
  have hCJ : C ≤ J := le_commutatorPreimage hCU (commutator_le.mpr
    (fun x hx t ht => hfixed t (h.T_le_H ht.1) x hx))
  have huJ : u ∈ J := by
    apply (Subgroup.mem_commutatorPreimage_iff D.UH S D.V₁ hUZ u).mpr
    refine ⟨hu,?_⟩
    intro x hx
    exact ((h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mp hx.2).2
      u (mem_zpowers u)
  have hbJ : b ∈ J := by
    have hx := J.mul_mem (J.inv_mem (hZJ hseed)) (hVJ hv)
    have hy := J.mul_mem (J.mul_mem (J.inv_mem huJ) hx) (J.inv_mem (hCJ hc))
    convert hy using 1
    group
  intro x hx
  exact commutator_commutatorPreimage_le D.UH S D.V₁ hUZ
    (commutator_mem_commutator hbJ hx)

/-- The dual factor of the original seed cannot vanish modulo Z: otherwise
T fixes u modulo Z, contradicting the suitable element's index-two condition. -/
theorem seed_dual_factor_not_mem_line
    (hcard : Nat.card D.V = 4) (hVU : D.V ≤ D.UH) (C : Subgroup G) (hCU : C ≤ D.UH)
    (hfixed : ∀ x ∈ D.H, ∀ c ∈ C, ⁅c,x⁆ ∈ D.V₁)
    (u b c v : G) (hu : u ∈ D.UH) (hc : c ∈ C)
    (hv : v ∈ D.V) (hseed : v*(u*b*c)⁻¹ ∈ D.V₁)
    (hindex : (suitableQuotientCentralizer h u).relIndex (D.T : Subgroup G) = 2) :
    b ∉ D.V₁ := by
  intro hb
  let J := commutatorPreimage D.UH (D.T : Subgroup G) D.V₁
  have hZU : D.V₁ ≤ D.UH := h.point_lt.le.trans (le_conjugateSpanBy _ _)
  have hUZ : D.UH ≤ normalizer (D.V₁ : Set G) :=
    h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  have hZJ : D.V₁ ≤ J := by
    apply le_commutatorPreimage hZU
    apply commutator_le.mpr
    intro z hz t ht
    have htz : Commute z t := h.H_centralizes (h.T_le_H ht) z hz
    rw [htz.commutator_eq]
    exact D.V₁.one_mem
  have hVJ : D.V ≤ J := le_commutatorPreimage hVU
    (plane_line_commutator D.V D.V₁ (D.T : Subgroup G)
      (h.point_lt.le.trans h.plus_le) hcard h.point_card h.T_normalizes_V h.normalizes_point)
  have hCJ : C ≤ J := le_commutatorPreimage hCU (commutator_le.mpr
    (fun x hx t ht => hfixed t (h.T_le_H ht) x hx))
  have huJ : u ∈ J := by
    have hx := J.mul_mem (J.inv_mem (hZJ hseed)) (hVJ hv)
    have hy := J.mul_mem hx (J.inv_mem (J.mul_mem (hZJ hb) (hCJ hc)))
    convert hy using 1
    group
  have hTP : (D.T : Subgroup G) ≤ h.kernel (zpowers u) := by
    intro t ht
    apply (h.mem_kernel_iff (zpowers_le.mpr (h.UH_le_H hu))).mpr
    refine ⟨h.T_le_H ht,?_⟩
    have htz : ∀ a ∈ zpowers u, ⁅a,t⁆ ∈ D.V₁ := by
      intro a ha
      exact commutator_commutatorPreimage_le D.UH (D.T : Subgroup G) D.V₁ hUZ
        (commutator_mem_commutator ((zpowers_le.mpr huJ) ha) ht)
    exact htz
  have he : suitableQuotientCentralizer h u = (D.T : Subgroup G) := inf_eq_left.mpr hTP
  rw [he,relIndex_self] at hindex
  omega
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair

namespace CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Matrix.PSL3Two.NaturalDualMarking
variable {G : Type*} [Group G] [Finite G]

/-- Conditional source application retaining the original seed and full marking.
The support separation, fixed factor and seed factors are the specialized
14.6.22--24 inputs, not consequences of an arbitrary hatted direct sum. -/
theorem source_residual_span_of_natural_dual_seed
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (A B C : Subgroup G)
    (hAU : A ≤ conjugateSpanBy (localModule T M) Mc)
    (hBU : B ≤ conjugateSpanBy (localModule T M) Mc)
    (hCU : C ≤ conjugateSpanBy (localModule T M) Mc)
    (hsep : A ⊓ (B ⊔ C) ≤ centralInvolutions T)
    (hpair : ∀ x ∈ Mc, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B)
    (q : (Mc ⊓ normalizer (A : Set G) : Subgroup G) →* BinaryLinear.GL Space)
    (hq : Function.Surjective q)
    (n : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) A (centralInvolutions T)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q))
    (d : BinaryConjugationSection (Mc ⊓ normalizer (A : Set G)) B (centralInvolutions T)
      (Representation.dual (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp q)))
    (hcover : ∀ v ∈ conjugateSpanBy (localModule T M) Mc,
      ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, v = a*b*c)
    (hfixed : ∀ x ∈ Mc, ∀ c ∈ C, ⁅c,x⁆ ∈ centralInvolutions T)
    (u b c v : G) (huA : u ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (hv : v ∈ localModule T M) (hvZ : v ∉ centralInvolutions T)
    (hseed : v * (u*b*c)⁻¹ ∈ centralInvolutions T) :
    let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let P := h.kernel (zpowers u)
    let R := (pResidual 2 P).map P.subtype
    ComponentSupports.Suitable h Mc u →
    R ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc →
    Nonempty (SourceParabolicAction P) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ coords : SourceResidualSpanCoordinates (localModule T M) (centralInvolutions T) R,
        coords.W = ⁅B,R⁆ ∧ coords.a = u*c ∧ coords.b = b ∧
        primeRank 2 (conjugateSpanBy (localModule T M) R) = 4 ∧ ¬R ≤ M := by
  dsimp only
  intro hu hRF
  let h := ComponentSupports.terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let P := h.kernel (zpowers u)
  have hbZ := seed_dual_factor_not_mem_line h hcard (le_conjugateSpanBy _ _) C hCU hfixed u b c v hu.1 hc hv hseed hu.2.2.1
  have hsep' : A ⊓ B ≤ centralInvolutions T :=
    (inf_le_inf_left A (show B ≤ B ⊔ C from le_sup_left)).trans hsep
  obtain ⟨hpa,hquot,a,hpoint,hactor⟩ := source_parabolic_action_of_natural_pair
    hG T hempty hM hunique hmany hcard e hab A B C hsep' hpair q hq n d hcover hfixed u huA hu
  have huz : u ∉ centralInvolutions T := by
    intro hz
    apply hu.2.2.2.1
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (h.H_centralizes (pCoreIn_le 2 Mc hx) u hz).symm
  let := h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hu2 : u ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u hu.1
  have hPL : P ≤ Mc ⊓ normalizer (A : Set G) :=
    point_kernel_le_support_normalizer h A B (n.section_le.trans inf_le_left)
      n.kernel_le hsep' hpair u huA huz hu2
  have hBP : B ≤ P := by
    intro x hx
    apply (mem_point_kernel_iff h u (h.UH_le_H hu.1) hu2 x).mpr
    refine ⟨h.UH_le_H (hBU hx),?_⟩
    have hcU : conjugateSpanBy (localModule T M) Mc ≤
        centralizer (conjugateSpanBy (localModule T M) Mc : Set G) :=
      le_centralizer_iff_isMulCommutative.mpr inferInstance
    have hxu : Commute u x := hcU (hBU hx) u hu.1
    rw [hxu.commutator_eq]
    exact (centralInvolutions T).one_mem
  have hr : (q.comp (inclusion hPL)).range =
      MulAction.stabilizer (BinaryLinear.GL Space) (n.coordinates ⟨u,huA⟩).toAdd := by
    have he : q.comp (inclusion hPL) = a.actor := by
      apply MonoidHom.ext
      intro x
      exact (hactor x (hPL x.property)).symm
    rw [he, a.image, hpoint]
  obtain ⟨t,ht,f,hf,hfcompat,d',hd'⟩ := normalized_action q d hPL hBP
    (n.coordinates ⟨u,huA⟩).toAdd (by
      intro he
      exact huz ((n.coordinates_eq_one_iff ⟨u,huA⟩).mp he))
    hr
  obtain ⟨S,hS⟩ := suitable_quotient_sylow_of_local_normalizer h u Mc le_rfl hu.2.2.2.2.2
  have hbplane : (d'.coordinates ⟨b,hb⟩).toAdd 0 = 0 := by
    apply section_sylow_fixed_mem_plane f hf d' S
    intro x hx
    apply seed_dual_factor_fixed h hcard (le_conjugateSpanBy _ _) C hCU hfixed u b c v hu.1 hc hv hseed
    rw [← hS]
    exact ⟨x,hx,rfl⟩
  have hbzero : d'.coordinates ⟨b,hb⟩ ≠ 1 := by
    intro he
    exact hbZ ((d'.coordinates_eq_one_iff ⟨b,hb⟩).mp he)
  refine ⟨hpa,hquot,?_⟩
  exact source_residual_span_of_marked_dual hG T hempty hM hunique hmany hcard e hab
    A B C hAU hBU hCU hsep hfixed u b c v huA hb hc hv hvZ hseed hu hRF
    f hf d' hbplane hbzero
end CFSG.Quasithin.Chapter14.Section06.ComponentCriticalPair
