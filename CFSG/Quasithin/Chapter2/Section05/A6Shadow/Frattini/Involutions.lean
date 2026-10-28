module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Transport
public import Theory.Frattini.PGroup

/-!
# The distinguished involutions from the Frattini obstruction

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 2.5.25,
printed p.568. If tˣ does not lie in K, normality and the line Z(S) ∩ S_Cˣ
force S_K ∩ S_Cˣ = 1. Thus the crossed core centralizes S_K, and its faithful
actual action embeds S_C in the checked elementary-four centralizer in the
Sylow subgroup of Aut(A₆). This contradicts nontrivial Φ(S_C).

Consequently tˣ belongs to the central involution line of S_K, giving tˣ = zK.
The earlier equality tˣ = tz then gives z = tzK. Nontrivial Frattini remains
an explicit premise: this file proves 2.5.25 from 2.5.24, not 2.5.24 itself.
All conjugation identities use the source's right-conjugation convention.
-/

public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}
namespace EarlierSetup
variable (d : EarlierSetup κ G)

private theorem mem_zpowers_two {z a : G} (hz : orderOf z = 2) :
    a ∈ zpowers z ↔ a = 1 ∨ a = z := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hz]
  constructor
  · intro ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    have hnlt : n < 2 := Finset.mem_range.mp hn
    interval_cases n <;> simp
  · rintro (rfl | rfl)
    · exact Finset.mem_image.mpr ⟨0, by simp, by simp⟩
    · exact Finset.mem_image.mpr ⟨1, by simp, by simp⟩

theorem crossing_center :
    centerIn d.S ⊓ rightConjugate d.x d.SC = zpowers (d.x⁻¹ * d.t * d.x) := by
  have he := congrArg (Subgroup.map (MulAut.conj d.x⁻¹).toMonoidHom) d.center_sc
  rw [Subgroup.map_inf _ _ _ (MulAut.conj d.x⁻¹).injective,
    centerIn_map_equiv, MonoidHom.map_zpowers] at he
  change centerIn (rightConjugate d.x d.S) ⊓ rightConjugate d.x d.SC = _ at he
  rw [d.rightConjugate_s] at he
  simpa using he

theorem crossing_order : orderOf (d.x⁻¹ * d.t * d.x) = 2 := by
  have he := (MulAut.conj d.x⁻¹).orderOf_eq d.t
  simpa using he.trans d.t_order

/-- The normal intersection is trivial unless tˣ lies in K. -/
theorem disjoint_sk_crossing_of_not_mem
    (htx : d.x⁻¹ * d.t * d.x ∉ d.K) :
    Disjoint (d.S ⊓ d.K) (rightConjugate d.x d.SC) := by
  let X := rightConjugate d.x d.SC
  have hXS : X ≤ d.S := d.rightConjugate_le d.sc_le_s
  have hXn : d.S ≤ normalizer (X : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hXS).mp
      (d.rightConjugate_normal d.sc_le_s d.normal_sc)
  have hDn : d.S ≤ normalizer ((d.S ⊓ d.K : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp d.normal_sk
  apply disjoint_iff.mpr
  by_contra hn
  have hc := inf_centerIn_ne_bot d.isTwoGroupS hn
    (show (d.S ⊓ d.K) ⊓ X ≤ d.S from inf_le_left.trans inf_le_left)
    ((le_inf hDn hXn).trans inf_normalizer_le_normalizer_inf)
  apply hc
  apply bot_unique
  intro a ha
  have haC : a ∈ zpowers (d.x⁻¹ * d.t * d.x) :=
    d.crossing_center ▸ (show a ∈ centerIn d.S ⊓ X from ⟨ha.2, ha.1.2⟩)
  rcases (mem_zpowers_two d.crossing_order).mp haC with ha1 | hat
  · exact ha1
  · exact (htx (hat ▸ ha.1.1.2)).elim

/-- Relative normality turns the disjoint intersection into centralization. -/
theorem crossing_centralizes_sk_of_not_mem
    (htx : d.x⁻¹ * d.t * d.x ∉ d.K) :
    rightConjugate d.x d.SC ≤ centralizer ((d.S ⊓ d.K : Subgroup G) : Set G) := by
  let D := (d.S ⊓ d.K).subgroupOf d.S
  let X := (rightConjugate d.x d.SC).subgroupOf d.S
  let : D.Normal := d.normal_sk
  let : X.Normal := d.rightConjugate_normal d.sc_le_s d.normal_sc
  have hd : Disjoint X D := by
    apply disjoint_def.mpr
    intro a haX haD
    exact Subtype.ext (disjoint_def.mp (d.disjoint_sk_crossing_of_not_mem htx) haD haX)
  have hc : X ≤ centralizer (D : Set d.S) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (bot_unique ((commutator_le_inf X D).trans (disjoint_iff.mp hd).le))
  intro a ha b hb
  exact congrArg Subtype.val
    (hc (show (⟨a, d.rightConjugate_le d.sc_le_s ha⟩ : d.S) ∈ X from ha)
      ⟨b, hb.1⟩ hb)

/-- The actual image of the crossed core centralizes the actual inner Sylow factor. -/
def crossingCentralizerHom
    (htx : d.x⁻¹ * d.t * d.x ∉ d.K) :
    rightConjugate d.x d.SC →*
      centralizer (sylowInner d.imageSylow : Set d.imageSylow) :=
  (d.toImageSylow.comp (inclusion (d.rightConjugate_le d.sc_le_s))).codRestrict _ (by
    intro a b hb
    have hb' : (b : AutA6) ∈ d.skAction.range := by
      rw [d.skAction_range]
      exact ⟨b.property, hb⟩
    obtain ⟨k, hk⟩ := hb'
    apply Subtype.ext
    change (b : AutA6) * d.sylowAction ⟨a, d.rightConjugate_le d.sc_le_s a.property⟩ =
      d.sylowAction ⟨a, d.rightConjugate_le d.sc_le_s a.property⟩ * (b : AutA6)
    rw [← hk]
    have hc : (⟨k, k.property.1⟩ : d.S) *
        ⟨a, d.rightConjugate_le d.sc_le_s a.property⟩ =
        (⟨a, d.rightConjugate_le d.sc_le_s a.property⟩ : d.S) * ⟨k, k.property.1⟩ :=
      Subtype.ext (d.crossing_centralizes_sk_of_not_mem htx a.property k k.property)
    have hm := congrArg d.sylowAction hc
    rw [map_mul, map_mul] at hm
    simpa [skAction, Subgroup.inclusion] using hm)

theorem crossingCentralizerHom_injective
    (htx : d.x⁻¹ * d.t * d.x ∉ d.K) :
    Function.Injective (d.crossingCentralizerHom htx) := by
  intro a b hab
  exact d.crossing_action_injective (congrArg Subtype.val hab)

/-- An embedding of S_C in the checked elementary-four centralizer in Aut(A₆).
The homomorphism factors through the compatible action, with no abstract
quotient identification or elementary-kernel assumption. -/
noncomputable def coreElementaryFourHom (htx : d.x⁻¹ * d.t * d.x ∉ d.K) : d.SC →* Holomorph.E4 :=
  (SylowGeometry.centralizerInnerEquiv d.imageSylow).toMonoidHom.comp
    ((d.crossingCentralizerHom htx).comp
      ((MulAut.conj d.x⁻¹).subgroupMap d.SC).toMonoidHom)

theorem coreElementaryFourHom_injective (htx : d.x⁻¹ * d.t * d.x ∉ d.K) :
    Function.Injective (d.coreElementaryFourHom htx) :=
  (SylowGeometry.centralizerInnerEquiv d.imageSylow).injective.comp
    ((d.crossingCentralizerHom_injective htx).comp
      ((MulAut.conj d.x⁻¹).subgroupMap d.SC).injective)

theorem elementary_core_of_crossing_not_mem (htx : d.x⁻¹ * d.t * d.x ∉ d.K) :
    IsElementaryAbelian 2 d.SC := by
  let f := d.coreElementaryFourHom htx
  have hf := d.coreElementaryFourHom_injective htx
  refine { is_comm.comm := ?_, exponent_dvd_p := ?_ }
  · intro a b
    apply hf
    simp only [map_mul]
    exact mul_comm _ _
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply hf
    rw [map_pow, map_one]
    exact (show ∀ b : Holomorph.E4, b ^ 2 = 1 by decide +kernel) (f a)

/-- Source 2.5.25, conditional only on the explicitly earlier result 2.5.24.
Nontrivial Φ(S_C) excludes the elementary-four embedding, forcing tˣ into
S_K. Its central involution is zK, and 2.5.13(1) then gives z = t zK. -/
theorem involution_identities_of_frattini_ne (hphi : frattini d.SC ≠ ⊥) :
    d.x⁻¹ * d.t * d.x = d.zK ∧ d.z = d.t * d.zK := by
  have htK : d.x⁻¹ * d.t * d.x ∈ d.K := by
    by_contra htK
    let : IsElementaryAbelian 2 d.SC := d.elementary_core_of_crossing_not_mem htK
    let : Fact (IsPGroup 2 d.SC) := ⟨IsElementaryAbelian.isPGroup 2 d.SC⟩
    exact hphi (frattini_eq_bot_of_isElementaryAbelian (p := 2))
  have htcent : d.x⁻¹ * d.t * d.x ∈ centerIn d.S :=
    (show zpowers (d.x⁻¹ * d.t * d.x) ≤ centerIn d.S from
      d.crossing_center ▸ inf_le_left) (mem_zpowers _)
  have htcentD : d.x⁻¹ * d.t * d.x ∈ centerIn (d.S ⊓ d.K) :=
    ⟨⟨htcent.1, htK⟩, fun a ha => htcent.2 a ha.1⟩
  rw [d.center_sk] at htcentD
  have htx := (mem_zpowers_two d.zK_order).mp htcentD
  have hne : d.x⁻¹ * d.t * d.x ≠ 1 := by
    intro he
    have ho := d.crossing_order
    simp [he] at ho
  have he := htx.resolve_left hne
  refine ⟨he, ?_⟩
  have hc : d.t * d.z = d.zK := d.crossing_t.symm.trans he
  have ht2 : d.t * d.t = 1 := by
    simpa only [pow_two, d.t_order] using pow_orderOf_eq_one d.t
  calc
    d.z = (d.t * d.t) * d.z := by rw [ht2, one_mul]
    _ = d.t * d.zK := by rw [mul_assoc, hc]

/-- The same crossing element gives the same conjugate of t in either
convention: x² belongs to S, and t is central in S. -/
theorem conj_t_eq_right : MulAut.conj d.x d.t = d.x⁻¹ * d.t * d.x := by
  have htZ : d.t ∈ centerIn d.S :=
    (show zpowers d.t ≤ centerIn d.S from d.center_sc ▸ inf_le_left) (mem_zpowers _)
  have hc : (d.x * d.x) * d.t = d.t * (d.x * d.x) := by
    simpa only [pow_two] using htZ.2 (d.x ^ 2) d.square_mem
  change d.x * d.t * d.x⁻¹ = _
  calc
    d.x * d.t * d.x⁻¹ = d.x⁻¹ * ((d.x * d.x) * d.t) * d.x⁻¹ := by group
    _ = d.x⁻¹ * (d.t * (d.x * d.x)) * d.x⁻¹ := by rw [hc]
    _ = d.x⁻¹ * d.t * d.x := by group

/-- Explicit conversion for the rank-one consumer, whose action uses
`MulAut.conj x` rather than the source's right conjugation. -/
theorem mulAut_conj_involution_identities_of_frattini_ne (hphi : frattini d.SC ≠ ⊥) :
    MulAut.conj d.x d.t = d.zK ∧ d.z = d.t * d.zK := by
  obtain ⟨ht, hz⟩ := d.involution_identities_of_frattini_ne hphi
  exact ⟨d.conj_t_eq_right.trans ht, hz⟩

end EarlierSetup
end CFSG.Quasithin.Chapter2.A6Shadow.Frattini
