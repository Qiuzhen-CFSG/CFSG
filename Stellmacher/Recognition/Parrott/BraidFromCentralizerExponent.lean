module

public import Stellmacher.Recognition.Parrott.BraidReduction
public import Stellmacher.Recognition.Parrott.CentralizerInvolutionProducts
public import Theory.SpecificGroups.Tits.RecognitionBraidWords

/-!
# Parrott's braid relation from the actual second-centralizer core

The two involution classes move the dihedral pair into one of the two actual
centralizers. The first centralizer has the required eighth- or tenth-power
bound. In the second, outside-core fusion and exponent four of the actual
core give eighth power one. Parrott's word identities exclude order ten.

The local generator pair and second-centralizer data are retained throughout.
Only the exponent-four consequence of the normalizer geometry remains explicit;
no global N₂ hypothesis is used. The original-source assembly supplies this
consequence from the same normalizer core.

Source: Parrott (1972), §6, printed p.684, Verification of VI(i).
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

omit [Finite G] in
/-- Multiplying an involution from the z-class by a square-one element in
the second centralizer gives eighth power one. Outside-core fusion puts the
first involution in the core, so the square of the product lies there too. -/
public theorem ParrottSecondCentralizerData.involution_product_eighth_power_of_core_exponent
    (c : ParrottSecondCentralizerData n)
    (hfour : ∀ a : pCore 2 (centralizer ({n.v} : Set G)), a ^ 4 = 1)
    (a b : centralizer ({n.v} : Set G))
    (ha : orderOf (a : G) = 2) (haz : IsConj (a : G) z) (hb : b ^ 2 = 1) :
    (a * b) ^ 8 = 1 := by
  let C := centralizer ({n.v} : Set G)
  let U := pCore 2 C
  have haU : a ∈ U := by
    by_contra hnot
    have hnot' : (a : G) ∉ U.map C.subtype := by
      rintro ⟨u, hu, he⟩
      exact hnot ((Subtype.ext he : u = a) ▸ hu)
    exact n.not_isConj (haz.symm.trans (c.outside_core_fusion _ a.property ha hnot').symm)
  have hqa : QuotientGroup.mk' U a = 1 := (QuotientGroup.eq_one_iff a).mpr haU
  have hp : (a * b) ^ 2 ∈ U := by
    apply (QuotientGroup.eq_one_iff (N := U) _).mp
    change QuotientGroup.mk' U ((a * b) ^ 2) = 1
    rw [map_pow, map_mul, hqa, one_mul, ← map_pow,
      hb, map_one]
  have hh := congrArg U.subtype (hfour ⟨(a * b) ^ 2, hp⟩)
  change ((a * b) ^ 2) ^ 4 = 1 at hh
  exact (by simpa only [← pow_mul] using hh)


namespace ParrottNormalizerGeneratorData
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)

omit [Finite G] in
private theorem pullback_mem_centralizer (c : MulAut G) {u a : G}
    (ha : Commute a (c u)) : c.symm a ∈ centralizer ({u} : Set G) := by
  apply mem_centralizer_singleton_iff.mpr
  apply c.injective
  simpa only [map_mul, c.apply_symm_apply] using ha.eq

omit [Finite G] in
private theorem pullback_square (c : MulAut G) (a : G) (ha : a ^ 2 = 1)
    (u : G) (hmem : c.symm a ∈ centralizer ({u} : Set G)) :
    (⟨c.symm a, hmem⟩ : centralizer ({u} : Set G)) ^ 2 = 1 := by
  apply Subtype.ext
  change (c.symm a) ^ 2 = 1
  rw [← map_pow, ha, map_one]

omit [Finite G] in
private theorem push_product_power (c : MulAut G) (a b : G) (u : G)
    (ha : c.symm a ∈ centralizer ({u} : Set G))
    (hb : c.symm b ∈ centralizer ({u} : Set G)) (m : ℕ)
    (hp : ((⟨c.symm a, ha⟩ : centralizer ({u} : Set G)) * ⟨c.symm b, hb⟩) ^ m = 1) :
    (a * b) ^ m = 1 := by
  have hh := congrArg (fun x : centralizer ({u} : Set G) => c (x : G)) hp
  change c ((c.symm a * c.symm b) ^ m) = c 1 at hh
  simpa only [map_pow, map_mul, c.apply_symm_apply, map_one] using hh

/-- The actual compatible generators satisfy the eighth- or tenth-power
alternatives. The central involution selects one of the two actual centralizers;
no lower order bound or word identity is needed for these alternatives. -/
public theorem braid_order_alternatives_of_second_centralizer_exponent
    (h : ParrottCentralizerHypotheses z) (cdata : ParrottSecondCentralizerData n)
    (hfour : ∀ a : pCore 2 (centralizer ({n.v} : Set G)), a ^ 4 = 1) :
    (f.r * k.s) ^ 8 = 1 ∨ (f.r * k.s) ^ 10 = 1 := by
  let i := (f.r * k.s) ^ (orderOf (f.r * k.s) / 2)
  have hi := k.braid_central_involution
  rcases n.involution_classes i hi.2.1 with hz | hv
  · obtain ⟨g, hg⟩ := isConj_iff.mp hz
    let c := MulAut.conj g
    have hc : c z = i := hg
    have hr : c.symm f.r ∈ centralizer ({z} : Set G) :=
      pullback_mem_centralizer c (hc ▸ hi.2.2.1.symm)
    have hs : c.symm k.s ∈ centralizer ({z} : Set G) :=
      pullback_mem_centralizer c (hc ▸ hi.2.2.2.symm)
    have hh := parrott_centralizer_involution_product_powers z h
      ⟨c.symm f.r, hr⟩ ⟨c.symm k.s, hs⟩
      (pullback_square c f.r f.eq20_r z hr) (pullback_square c k.s k.s_sq z hs)
    rcases hh with h8 | h10
    · exact Or.inl (push_product_power c f.r k.s z hr hs 8 h8)
    · exact Or.inr (push_product_power c f.r k.s z hr hs 10 h10)
  · obtain ⟨g, hg⟩ := isConj_iff.mp hv
    let c := MulAut.conj g
    have hc : c n.v = i := hg
    have hr : c.symm f.r ∈ centralizer ({n.v} : Set G) :=
      pullback_mem_centralizer c (hc ▸ hi.2.2.1.symm)
    have hs : c.symm k.s ∈ centralizer ({n.v} : Set G) :=
      pullback_mem_centralizer c (hc ▸ hi.2.2.2.symm)
    have hr2 : orderOf (c.symm f.r) = 2 := (c.symm.orderOf_eq f.r).trans f.r_order
    have hrz : IsConj (c.symm f.r) z := by
      have hcr : IsConj (c.symm f.r) f.r := isConj_iff.mpr ⟨g, c.apply_symm_apply f.r⟩
      exact hcr.trans f.r_conjugate
    have hh := cdata.involution_product_eighth_power_of_core_exponent hfour
      ⟨c.symm f.r, hr⟩ ⟨c.symm k.s, hs⟩ hr2 hrz
      (pullback_square c k.s k.s_sq n.v hs)
    exact Or.inl (push_product_power c f.r k.s n.v hr hs 8 hh)

end ParrottNormalizerGeneratorData


namespace ParrottNormalizerGeneratorData
variable {f : ParrottCentralizerGeneratorData n} (k : ParrottNormalizerGeneratorData f)

/-- The same local words satisfy the braid relation, using the actual
second-centralizer core of exponent dividing four. -/
public theorem braid_eighth_power_of_second_centralizer_exponent
    (h : ParrottCentralizerHypotheses z) (c : ParrottSecondCentralizerData n)
    (hfour : ∀ a : pCore 2 (centralizer ({n.v} : Set G)), a ^ 4 = 1) :
    (f.r * k.s) ^ 8 = 1 := by
  exact k.braid_eighth_power_of_local_steps h c
    k.localRelations.braid_fourth_conjugation
    k.localRelations.braid_ten_commute
    (fun _ => k.localRelations.braid_word_fourth_power)
    (k.braid_order_alternatives_of_second_centralizer_exponent h c hfour)

/-- All 37 relators hold for this supplied compatible pair. -/
public theorem satisfiesParrottRelations_of_second_centralizer_exponent
    (h : ParrottCentralizerHypotheses z) (c : ParrottSecondCentralizerData n)
    (hfour : ∀ a : pCore 2 (centralizer ({n.v} : Set G)), a ^ 4 = 1) :
    Tits.SatisfiesParrottRelations k.words := by
  apply (Tits.satisfiesParrottRelations_iff_except_braid k.words).mpr
  exact ⟨k.relators_except_braid,
    k.braid_eighth_power_of_second_centralizer_exponent h c hfour⟩

end ParrottNormalizerGeneratorData
end Stellmacher.Recognition
