module

public import Stellmacher.Recognition.Parrott.BraidDihedral
public import Stellmacher.Recognition.Parrott.CentralizerInvolutionProducts
public import Stellmacher.Recognition.Parrott.SecondCentralizerInvolutionProducts

/-!
# The eighth- or tenth-power alternatives in Parrott's braid argument

For the supplied compatible generators r and s, their half-order rotation is
an involution centralizing both. The two involution classes move this pair
into either C_G(z) or C_G(v). Products of involutions in the former have
eighth or tenth power one. In the latter, the r-image lies in the actual
two-core by outside-core fusion, and its product with the s-image has eighth
power one.

This derives the alternatives from the actual centralizer structures. Neither
the lower order bound, the source word identities, nor a replacement choice
of generators is needed. The exclusion of order ten belongs to the consumer.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
§6, printed p.684, the sentence “the structures of H and C imply”.
-/

open Subgroup
namespace Stellmacher.Recognition
variable {G : Type*} [Group G] [Finite G] {z : G}
variable {e : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData e}

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
public theorem braid_order_alternatives
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G) :
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
    have hh := (n.second_centralizer_data h hN).involution_product_eighth_power h hN
      ⟨c.symm f.r, hr⟩ ⟨c.symm k.s, hs⟩ hr2 hrz
      (pullback_square c k.s k.s_sq n.v hs)
    exact Or.inl (push_product_power c f.r k.s n.v hr hs 8 hh)

end ParrottNormalizerGeneratorData

end Stellmacher.Recognition
