module
public import CFSG.Quasithin.Chapter13.Section08.SourceCompletion.Terminal
public import CFSG.Quasithin.Chapter13.Section08.A6Endgame.PointNormalizer
public import Theory.GroupTheory.SubgroupPartitionCounting
public import Mathlib.GroupTheory.IndexNormal
import Mathlib.Tactic.Group
/-!
# Nonfixedness of the actual terminal quotient point

If the image of the critical involution in U_H/V₁ were fixed by H*,
its centralizer in H would have index at most two. This centralizer is
H intersect Gγ. Since H and Gγ are conjugate, that intersection also
has index at most two in Gγ, and is therefore normal there. The normal
binary subgroup U_H lies in its two-core and hence in O₂(Gγ), contrary
to the strict denominator D_H < U_H. This argument retains the full
quotient, including any constant line, and applies to every supplied
literal StarAction.

Source: Aschbacher--Smith, final paragraph of 13.8.1, printed pp.968--969;
the endpoint normalizer and denominator identities are 13.8.27(2) and F.9.13.
-/
public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
open CriticalGeometry TransvectionRecognition.Component.ModelExtension
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_index_dvd_two
    (H Z : Subgroup G) (hZ : Nat.card Z = 2) (hZH : Z ≤ H) (hz : H ≤ centralizer (Z : Set G))
    (u : G) (hc : ∀ h ∈ H, ⁅h,u⁆ ∈ Z) :
    (centralizer ({u} : Set G)).relIndex H ∣ 2 := by
  let f : H →* Z := {
    toFun h := ⟨⁅(h : G), u⁆, hc h h.property⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := by
      intro h k
      apply Subtype.ext
      change ⁅(h : G) * (k : G),u⁆ = ⁅(h : G),u⁆ * ⁅(k : G),u⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hfix := mem_centralizer_iff.mp (hz h.property) _ (hc k k.property)
      rw [← hfix]
      simp only [mul_inv_cancel_right]
      exact mem_centralizer_iff.mp (hz (hZH (hc h h.property))) _ (hc k k.property) }
  have hker : f.ker = (centralizer ({u} : Set G)).subgroupOf H := by
    ext h
    change (⟨⁅(h : G),u⁆, _⟩ : Z) = 1 ↔ _
    rw [Subtype.ext_iff]
    exact commutatorElement_eq_one_iff_mul_comm.trans mem_centralizer_singleton_iff.symm
  change ((centralizer ({u} : Set G)).subgroupOf H).index ∣ 2
  rw [← hker, index_ker, ← hZ]
  exact f.range.card_subgroup_dvd_card

variable {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H : Subgroup G}

/-- A fixed quotient point would give a normal intersection of index at most
 two in both conjugate point centralizers, contradicting the strict denominator. -/
theorem critical_point_nonfixed
    (d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (hHz : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M)
    (hF9 : (Section07.ConjugateIntersections.sourceSetup T L V V₃ V₁ H).Hypothesis)
    (c : CriticalPair L (T : Subgroup G) H V) (hH : H = G₁)
    (hs : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (a : letI := d.uh_elementary hHz
      SolvableExclusion.Five.StarAction H (Source.UH H V₃) V₁)
    (u : Source.UH H V₃) (hu : (u : G) ∈ c.Aone V₁) (hu1 : (u : G) ≠ 1) :
    letI := d.uh_elementary hHz
    ∃ g, a.action g (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u) ≠
      QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u := by
  let : IsElementaryAbelian 2 (Source.UH H V₃) := d.uh_elementary hHz
  by_contra! hf
  let J := vertexGroup L (T : Subgroup G) H c.gamma
  let I := H ⊓ J
  have hJ : J = centralizer ({(u : G)} : Set G) := by
    change vertexGroup L (T : Subgroup G) H c.gamma = _
    rw [Terminal.endpoint_eq_line_normalizer d c hH]
    apply A6Endgame.PointNormalizer.normalizer_eq_point_centralizer (c.Aone V₁) _ (u : G) hu hu1
    rw [CriticalPair.Aone, card_map_of_injective (MulAut.conj _).injective, d.line_card]
  have hzH : V₁ ≤ H := (d.line_le_uh H).trans hF9.UH_le_H
  have hc (h : H) : ⁅(h : G),(u : G)⁆ ∈ V₁ := by
    let v : Source.UH H V₃ := ⟨(h : G) * (u : G) * (h : G)⁻¹,
      (mem_normalizer_iff.mp (a.normalizes h.property) u).mp u.property⟩
    have he : QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) v =
        QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u :=
      (a.conjugation h u).symm.trans (hf _)
    have hh : QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) (v * u⁻¹) = 1 := by
      rw [map_mul, map_inv, he, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff (N := V₁.subgroupOf (Source.UH H V₃)) (v * u⁻¹)).mp hh
  have hiH : I.relIndex H ∣ 2 := by
    rw [show I = H ⊓ centralizer ({(u : G)} : Set G) from congrArg (H ⊓ ·) hJ,
      inf_relIndex_left]
    exact centralizer_index_dvd_two H V₁ d.line_card hzH hF9.H_centralizes u
      (fun x hx => hc ⟨x,hx⟩)
  have hcard : Nat.card H = Nat.card J := by
    rw [show J = H.map (MulAut.conj (c.gb : G)).toMonoidHom from c.vertexGroup_gamma,
      card_map_of_injective (MulAut.conj _).injective]
  have hiJ : I.relIndex J ∣ 2 := by
    have h₁ := relIndex_mul_card_of_le (show I ≤ H from inf_le_left)
    have h₂ := relIndex_mul_card_of_le (show I ≤ J from inf_le_right)
    have hp : 0 < Nat.card I := Nat.card_pos
    have he : I.relIndex H = I.relIndex J := Nat.eq_of_mul_eq_mul_right hp (h₁.trans (hcard.trans h₂.symm))
    rwa [← he]
  have hIn : (I.subgroupOf J).Normal := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hiJ with h | h
    · exact normal_of_index_eq_one h
    · exact normal_of_index_eq_two h
  have hUI : Source.UH H V₃ ≤ I := by
    apply le_inf hF9.UH_le_H
    rw [hJ]
    intro v hv
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨v,hv⟩ : Source.UH H V₃) u)
  have hUQ : Source.UH H V₃ ≤ J.pCoreIn 2 :=
    (le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 _) hUI
      (inf_le_left.trans (le_normalizer_conjugateSpanBy V₃ H))).trans
      (pCoreIn_mono_of_normalizes inf_le_right
        ((normal_subgroupOf_iff_le_normalizer inf_le_right).mp hIn))
  have hg := local_earlierGeometry d hF9 c
  have hQ : J.pCoreIn 2 = c.Qgamma := by
    rw [show J = H.map (MulAut.conj (c.gb : G)).toMonoidHom from c.vertexGroup_gamma,
      ← map_pCoreIn_of_injective 2 H _ (MulAut.conj _).injective]
    rfl
  apply hs.ne
  rw [hg.DH_kernel, ← hQ, inf_eq_left.mpr hUQ]

end CFSG.Quasithin.Chapter13.Section08.SourceCompletion.TerminalPoint
