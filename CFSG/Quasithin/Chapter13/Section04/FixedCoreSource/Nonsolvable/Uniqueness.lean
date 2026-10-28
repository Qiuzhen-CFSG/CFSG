module

public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.Rank
public import Theory.GroupTheory.SolvableNormalizerObstruction
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168Models
public import Theory.SpecificGroups.PSL3Two.NonSolvable
public import CFSG.Quasithin.Chapter3.Defs

/-!
# Comparing the two escaping central choices in original 13.4.12

The four-group V ∩ Ω₁Z(T) contains the fixed generator. Its other two points
have different weights. If both escape, the source parabolic alternatives
force O²(H₄,₂) to be normalized by N_G(J(T)). Maximal two-locality puts that
residual inside the normalizer; the actual L₃(2) quotient then kills its
solvable image. This contradicts its non-two-group property, which follows
from its Sylow supplement and H₄,₂ lying outside M.

The residual's nontrivial two-core is proved using characteristic-two
inheritance, so it is not an extra geometric assumption. The comparison
retains both literal two-residuals, the common Sylow, fixed-line centralizers,
and the SL₃(2) model of the quotient. The model simplicity theorem reuses
the attributed ATLAS port in Order168Models; see LICENSES/ATLAS.txt.

ParabolicComparison records intermediate conclusions of 13.4.10 and the
pair application of 13.4.7. Their construction remains unproved and belongs
to qt-d-1341-nonsolvable-source. The final theorem is a conditional uniqueness
and rank application, not the full nonsolvable contradiction. The earlier
local-amalgam inputs are now owned by qt-d-1341-fixed-core-source, which
also owns final ambient recognition. Universal nonsolvability is retained
and used for each of the two escaping choices independently.

Source: Aschbacher–Smith, 13.4.12, printed pp.910–911, and 13.4.17(5), p.914.
-/

public noncomputable section
open Subgroup Theory.GroupTheory CFSG.Quasithin
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
private theorem residual_not_two {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M H : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ CFSG.Quasithin.Chapter3.HStar (T : Subgroup G) M) :
    ¬ IsPGroup 2 ((pResidual 2 H).map H.subtype) := by
  intro hp
  have hR : IsPGroup 2 (pResidual 2 H) :=
    hp.of_equiv ((pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective).symm
  obtain ⟨a, ha⟩ := hR.exists_card_eq
  obtain ⟨b, hb⟩ := (isPGroup_quotient_pResidual (G := H) 2).exists_card_eq
  have hHtwo : IsPGroup 2 H := IsPGroup.of_card (n := a+b) (by
    rw [pow_add, ← ha, ← hb, ← index_eq_card, card_mul_index])
  have hHT : H ≤ T := (T.is_maximal' hHtwo hH.1.1.2).le
  exact hH.1.2 (hHT.trans hTM)

private theorem normal_core_nontrivial {H : Type*} [Group H] [Finite H]
    (hH : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (K : Subgroup H) [K.Normal] (hK : ¬ IsPGroup 2 K) :
    pCore 2 K ≠ ⊥ := by
  have hc := normal_core_selfCentralizing hH K
  intro he
  apply hK
  intro x
  have hx : x ∈ pCore 2 K := hc (by
    intro y hy
    have hy1 : y = 1 := mem_bot.mp (he ▸ hy)
    simp [hy1])
  exact ⟨0, by simpa using mem_bot.mp (he ▸ hx)⟩


private theorem escaping_residual_obstruction {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M N H : Subgroup G) (hTM : (T : Subgroup G) ≤ M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hsolv : Group.IsSolvable H)
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H)
    (hmax : IsMaximalTwoLocal N)
    (e : (N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    ¬ N ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  let R := (pResidual 2 H).map H.subtype
  let eR : pResidual 2 H ≃* R :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hR := residual_not_two T M H hTM hH
  have hcore : R.pCoreIn 2 ≠ ⊥ := by
    have hnon : pCore 2 (pResidual 2 H) ≠ ⊥ :=
      normal_core_nontrivial hc (pResidual 2 H) (fun hp => hR (hp.of_equiv eR))
    intro he
    have he' : pCore 2 R = ⊥ :=
      (map_eq_bot_iff_of_injective (pCore 2 R) R.subtype_injective).mp he
    have hh := pCore_map_iso (p := 2) (f := eR)
    rw [he'] at hh
    exact hnon ((map_eq_bot_iff_of_injective _ eR.injective).mp hh)
  let : Group.IsSolvable H := hsolv
  have hs : Group.IsSolvable R :=
    Group.isSolvable_of_surjective (f := eR.toMonoidHom) eR.surjective
  let := Atlas.Comparisons.Exceptional.sl3Two_simple
  exact not_normalizes_solvable N R hmax hcore hs hR e not_isSolvable_sl3_two

private theorem parabolic_comparison_false {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (M L₂ H₂ H₄ : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hH₂ : H₂ ∈ Chapter3.HStar (T : Subgroup G) M)
    (hH₄ : H₄ ∈ Chapter3.HStar (T : Subgroup G) M)
    (hne : H₄ ≠ H₂)
    (hsolv : Group.IsSolvable H₄)
    (hc : centralizer (pCore 2 H₄ : Set H₄) ≤ pCore 2 H₄)
    (hmax : IsMaximalTwoLocal
      (normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)))
    (e : ((normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⧸
        pCore 2 (normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G))) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hgen : (L₂ ⊔ (T : Subgroup G)) ⊔ H₂ =
      normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hunique : ∀ X ∈ Chapter3.HStar (T : Subgroup G) M,
      X ≤ normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) → X = H₂)
    (hfour : L₂ ⊔ (T : Subgroup G) ≤ normalizer ((pResidual 2 H₄).map H₄.subtype : Set G) ∨
      (L₂ ⊔ (T : Subgroup G)) ⊔ H₄ ≤
        normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (hpair : (pResidual 2 H₂).map H₂.subtype ≤
      normalizer ((pResidual 2 H₄).map H₄.subtype : Set G) ∨
      H₂ ⊔ H₄ ≤ normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)) :
    False := by
  have hout : ¬ H₄ ≤ normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
    fun h => hne (hunique H₄ hH₄ h)
  have hP := hfour.resolve_right (fun h => hout (le_sup_right.trans h))
  have hQ := hpair.resolve_right (fun h => hout (le_sup_right.trans h))
  apply escaping_residual_obstruction T M _ H₄ hTM hH₄ hsolv hc hmax e
  rw [← hgen]
  apply sup_le hP
  have hT₂ : (T : Subgroup G) ≤ H₂ := hH₂.1.1.2
  have hs : (pResidual 2 H₂).map H₂.subtype ⊔ (T : Subgroup G) = H₂ :=
    embedded_pResidual_sup_of_common_sylow H₂ T (T.subtype hT₂)
      (by rw [T.coe_subtype, map_subgroupOf_eq_of_le hT₂])
  rw [← hs]
  exact sup_le hQ (hH₄.1.1.2.trans (le_normalizer_embedded_pResidual 2 H₄))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource
open Chapter12.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {D : ChosenModule T L V}
namespace CoreMarking

/-- In a subgroup of order at most four containing the fixed generator,
each nonconstant weight occurs at most once. Multiplication by that generator
interchanges weights two and four. -/
theorem central_weight_injective (m : CoreMarking D)
    (Z : Subgroup G) (hZV : Z ≤ V) (hcard : Nat.card Z ≤ 4)
    (hd : m.constant.val ∈ Z)
    (v w : V) (hv : v.val ∈ Z) (hw : w.val ∈ Z)
    (hvfixed : v.val ∉ centralizer (L : Set G))
    (he : m.weight w = m.weight v) : w = v := by
  classical
  let := Fintype.ofFinite Z
  let f : Z → V := fun x => ⟨x.val, hZV x.property⟩
  let d : Z := ⟨m.constant.val, hd⟩
  let a : Z := ⟨v.val, hv⟩
  let b : Z := ⟨w.val, hw⟩
  have hdw : m.weight (f d) = 6 := m.weight_constant
  have haw : m.weight (f a) = m.weight v := rfl
  have habw : m.weight (f (a * d)) = 6 - m.weight v := m.weight_mul_constant v
  have h1w : m.weight (f 1) = 0 := m.weight_one
  have hkind := m.nonfixed_weight v hvfixed
  have hda : d ≠ a := by intro h; have := congrArg (fun x => m.weight (f x)) h; omega
  have hda' : d ≠ a * d := by intro h; have := congrArg (fun x => m.weight (f x)) h; omega
  have haa' : a ≠ a * d := by intro h; have := congrArg (fun x => m.weight (f x)) h; omega
  have h1d : (1 : Z) ≠ d := by intro h; have := congrArg (fun x => m.weight (f x)) h; omega
  have h1a : (1 : Z) ≠ a := by intro h; have := congrArg (fun x => m.weight (f x)) h; omega
  have h1a' : (1 : Z) ≠ a * d := by intro h; have := congrArg (fun x => m.weight (f x)) h; omega
  let s : Finset Z := {1, d, a, a * d}
  have hs : s.card = 4 := by simp [s, hda, hda', haa', h1d, h1a, h1a']
  have hu : s = Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    (by simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card, hs] using hcard)
  have hb : b = 1 ∨ b = d ∨ b = a ∨ b = a * d := by
    have hh : b ∈ s := hu ▸ Finset.mem_univ b
    simpa only [s, Finset.mem_insert, Finset.mem_singleton] using hh
  have hbw : m.weight (f b) = m.weight v := he
  rcases hb with hb | hb | hb | hb
  · rw [hb, h1w] at hbw
    omega
  · rw [hb, hdw] at hbw
    omega
  · exact Subtype.ext (congrArg (fun x : Z => (x : G)) hb)
  · rw [hb, habw] at hbw
    omega

/-- The source central four-group reduces uniqueness to exclusion of the
simultaneous weight-two and weight-four escapes. -/
theorem unique_escape_of_weight_exclusion (m : CoreMarking D)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hcard : Nat.card (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) ≤ 4)
    (hpair : ∀ v w : V,
      v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      m.weight v = 2 → m.weight w = 4 →
      ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → False)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (w : V) (hw1 : w ≠ 1)
    (hwT : w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hwout : ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G)) : w = z := by
  have nonfixed (v : V) (hv1 : v ≠ 1)
      (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G)) :
      v.val ∉ centralizer (L : Set G) := by
    intro hv
    exact hvout (fixed_generator_centralizer h structural D m ⟨v.property, hv⟩
      (fun he => hv1 (Subtype.ext he))).le
  have hz := nonfixed z hz1 hzout
  have hw := nonfixed w hw1 hwout
  have hd : m.constant.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) := by
    apply (mem_omega_iff (D := D) m.constant).mpr
    apply mem_centralizer_iff.mpr
    intro t ht
    exact (mem_centralizer_iff.mp
      (normalizer_component_le_fixed_centralizer h structural D m
        (D.sylow_normalizes_component ht)) m.constant.val
      ⟨m.constant.property, m.constant_fixed⟩).symm
  apply m.central_weight_injective _ inf_le_left hcard ⟨m.constant.property, hd⟩
    z w ⟨z.property, hzT⟩ ⟨w.property, hwT⟩ hz
  rcases m.nonfixed_weight z hz with hz | hz <;>
    rcases m.nonfixed_weight w hw with hw | hw
  · omega
  · exact (hpair z w hzT hwT hz hw hzout hwout).elim
  · exact (hpair w z hwT hzT hw hz hwout hzout).elim
  · omega
end CoreMarking
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource

namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal normalizer used by the weight-two amalgam. -/
@[expose] def thompsonNormalizer (T : Sylow 2 G) : Subgroup G :=
  normalizer (Stellmacher.elementaryAbelianMaxJ (T : Subgroup G) : Set G)

/-- Intermediate geometry for two distinct central choices. These fields are
consequences still to be constructed from 13.4.10 and the applications of
13.4.7; they are not hypotheses of the original theorem. The pair comparison
uses only normalization by the actual two-residual, with its Sylow supplement
recovered in the proof. No uniqueness of the escaping vector is a field. -/
structure ParabolicComparison (T : Sylow 2 G) (M L₂ Z : Subgroup G) (z₂ z₄ : G) where
  two : Subgroup G
  four : Subgroup G
  two_mem : two ∈ Chapter3.HStar (T : Subgroup G) M
  four_mem : four ∈ Chapter3.HStar (T : Subgroup G) M
  two_fixed : Z ⊓ centralizer (two : Set G) = zpowers z₂
  four_fixed : Z ⊓ centralizer (four : Set G) = zpowers z₄
  four_solvable : Group.IsSolvable four
  four_characteristic : centralizer (pCore 2 four : Set four) ≤ pCore 2 four
  maximal : IsMaximalTwoLocal (thompsonNormalizer T)
  quotient : (thompsonNormalizer T ⧸ pCore 2 (thompsonNormalizer T)) ≃*
    Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)
  generation : (L₂ ⊔ (T : Subgroup G)) ⊔ two = thompsonNormalizer T
  unique_parabolic : ∀ X ∈ Chapter3.HStar (T : Subgroup G) M,
    X ≤ thompsonNormalizer T → X = two
  four_alternatives :
    L₂ ⊔ (T : Subgroup G) ≤ normalizer ((pResidual 2 four).map four.subtype : Set G) ∨
      (L₂ ⊔ (T : Subgroup G)) ⊔ four ≤ thompsonNormalizer T
  pair_alternatives :
    (pResidual 2 two).map two.subtype ≤
      normalizer ((pResidual 2 four).map four.subtype : Set G) ∨
      two ⊔ four ≤ thompsonNormalizer T

open Chapter12.Section02
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Different weights force different fixed lines and hence different
parabolics. The two amalgam alternatives then give the normalizer obstruction
on the literal four-choice residual. -/
theorem ParabolicComparison.false_of_weights (m : CoreMarking D)
    (L₂ : Subgroup G) (v w : V) (hv : m.weight v = 2) (hw : m.weight w = 4)
    (C : ParabolicComparison T (normalizer (L : Set G)) L₂
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) v.val w.val) : False := by
  classical
  have hv1 : v ≠ 1 := by intro he; rw [he, m.weight_one] at hv; omega
  have hw1 : w ≠ 1 := by intro he; rw [he, m.weight_one] at hw; omega
  have hne : C.four ≠ C.two := by
    intro he
    have heq : zpowers v.val = zpowers w.val := by
      rw [← C.two_fixed, ← C.four_fixed, he]
    have hm : v.val ∈ zpowers w.val := heq ▸ mem_zpowers v.val
    let := D.elementary
    have ho : orderOf w.val = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian w.val w.property)
      (fun he => hw1 (Subtype.ext he))
    rw [mem_zpowers_iff_mem_range_orderOf, ho] at hm
    obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · exact hv1 (Subtype.ext (by simpa using he.symm))
    · have hvw : v = w := Subtype.ext (by simpa using he.symm)
      rw [hvw, hw] at hv
      omega
  exact parabolic_comparison_false T _ L₂ C.two C.four D.sylow_normalizes_component
    C.two_mem C.four_mem hne C.four_solvable C.four_characteristic C.maximal C.quotient
    C.generation C.unique_parabolic C.four_alternatives C.pair_alternatives

/-- Conditional 13.4.12 uniqueness and its actual 13.4.17(5) rank consumer.
Universal nonsolvability is applied separately to both weight choices.
Construction of `comparisons` remains with this nonsolvable-branch owner;
this theorem does not discharge 13.4.10 or the comparison applicability. -/
theorem unique_escape_and_rank_of_comparisons
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (L₂ : Subgroup G)
    (hcard : Nat.card (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Subgroup G) ≤ 4)
    (hnonsolvable : ∀ v : V,
      v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      v.val ∉ centralizer (L : Set G) →
      ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({v.val} : Set G)))
    (comparisons : ∀ v w : V,
      v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      m.weight v = 2 → m.weight w = 4 →
      ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) →
      ¬ Group.IsSolvable (centralizer ({v.val} : Set G)) →
      ¬ Group.IsSolvable (centralizer ({w.val} : Set G)) →
      Nonempty (ParabolicComparison T (normalizer (L : Set G)) L₂
        (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) v.val w.val))
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G)) :
    (∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z) ∧
      3 ≤ ChapterE.globalR V := by
  have hpair (v w : V)
      (hvT : v.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
      (hwT : w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
      (hv : m.weight v = 2) (hw : m.weight w = 4)
      (hvout : ¬ centralizer ({v.val} : Set G) ≤ normalizer (L : Set G))
      (hwout : ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G)) : False := by
    have nonfixed (a : V) (ha : m.weight a = 2 ∨ m.weight a = 4) :
        a.val ∉ centralizer (L : Set G) := by
      intro hf
      rcases (m.fixed_iff a).mp hf with he | he
      · rw [he, m.weight_one] at ha
        omega
      · rw [he, m.weight_constant] at ha
        omega
    obtain ⟨C⟩ := comparisons v w hvT hwT hv hw hvout hwout
      (hnonsolvable v hvT (nonfixed v (Or.inl hv)) hvout)
      (hnonsolvable w hwT (nonfixed w (Or.inr hw)) hwout)
    exact C.false_of_weights m L₂ v w hv hw
  have hu := m.unique_escape_of_weight_exclusion h structural hcard hpair z hz1 hzT hzout
  exact ⟨hu, m.three_le_globalR_of_unique_escape h structural z hz1 hzT hzout hu⟩

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
