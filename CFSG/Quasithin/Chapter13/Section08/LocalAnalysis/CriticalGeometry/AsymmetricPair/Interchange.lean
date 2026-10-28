module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.Transport
public import Theory.GroupTheory.LocalNormalizerUniqueness

/-!
# Interchanging the two local subgroups

A normalizer of a subgroup of order two fixes its nonidentity element.
Consequently, when H=C_G(z), equal conjugates of ⟨z⟩ give equal conjugates
of every H-normalized subgroup. An element l whose square lies in H then
interchanges those subgroups. Applying this to U_H and O₂(H) contradicts
the unequal two-core containments.

This proves the sufficiency of condition (*) in Aschbacher–Smith 13.8.7,
printed p.949. The center orbit and the construction of l in L₂T are separate
mathematical obligations, not hypotheses hidden in a source theorem.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
variable {G : Type*} [Group G]

/-- The order-two line normalizer fixes its generator. -/
theorem normalizer_line_le_centralizer (z : G) (hz : z ≠ 1)
    (hcard : Nat.card (zpowers z) = 2) :
    normalizer (zpowers z : Set G) ≤ centralizer ({z} : Set G) := by
  obtain ⟨a, ha, hlast⟩ := (Nat.card_eq_two_iff' (1 : zpowers z)).mp hcard
  have huniq (x : zpowers z) (hx : (x : G) ≠ 1) : (x : G) = z := by
    have hx' := hlast x (fun hh => hx (congrArg Subtype.val hh))
    have hz' := hlast ⟨z, mem_zpowers z⟩ (fun hh => hz (congrArg Subtype.val hh))
    exact congrArg Subtype.val (hx'.trans hz'.symm)
  intro k hk
  have hm : k * z * k⁻¹ ∈ zpowers z :=
    (mem_normalizer_iff.mp hk z).mp (mem_zpowers z)
  have he : k * z * k⁻¹ = z := huniq ⟨_, hm⟩ (by
    intro hh
    apply hz
    have : MulAut.conj k z = MulAut.conj k 1 := by simpa using hh
    exact (MulAut.conj k).injective this)
  apply mem_centralizer_singleton_iff.mpr
  exact (mul_inv_eq_iff_eq_mul).mp he

/-- Equality of the actual central lines identifies conjugates of any subgroup
normalized by the involution centralizer. -/
theorem conjugates_eq_of_line_eq (H B : Subgroup G) (z k l : G)
    (hH : H = centralizer ({z} : Set G)) (hz : z ≠ 1)
    (hcard : Nat.card (zpowers z) = 2)
    (hn : H ≤ normalizer (B : Set G))
    (he : (zpowers z).conjBy k = (zpowers z).conjBy l) :
    B.conjBy k = B.conjBy l := by
  have hmem : l⁻¹ * k ∈ normalizer (zpowers z : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact conjBy_inv_mul_cancel _ he.symm
  have hmemH : l⁻¹ * k ∈ H := hH ▸
    normalizer_line_le_centralizer z hz hcard hmem
  have hfix : B.conjBy (l⁻¹ * k) = B :=
    mem_normalizer_iff_map_conj_eq.mp (hn hmemH)
  have hh := congrArg (fun X : Subgroup G => X.conjBy l) hfix
  simpa only [conjBy_conjBy, mul_inv_cancel_left] using hh

/-- The algebraic interchange obstruction; square membership is relative to H. -/
theorem no_interchange_of_asymmetric_containment
    (H U Q : Subgroup G) (z k l : G)
    (hH : H = centralizer ({z} : Set G)) (hz : z ≠ 1)
    (hcard : Nat.card (zpowers z) = 2)
    (hU : H ≤ normalizer (U : Set G)) (hQ : H ≤ normalizer (Q : Set G))
    (hline : (zpowers z).conjBy k = (zpowers z).conjBy l)
    (hsquare : l ^ 2 ∈ H)
    (hinside : U ≤ Q.conjBy k) (houtside : ¬ U.conjBy k ≤ Q) : False := by
  have hUk := conjugates_eq_of_line_eq H U z k l hH hz hcard hU hline
  have hQk := conjugates_eq_of_line_eq H Q z k l hH hz hcard hQ hline
  have hswap : (Q.conjBy l).conjBy l = Q := by
    rw [conjBy_conjBy, ← pow_two]
    exact mem_normalizer_iff_map_conj_eq.mp (hQ hsquare)
  apply houtside
  rw [hUk]
  have hh := map_mono (f := (MulAut.conj l).toMonoidHom) hinside
  change U.conjBy l ≤ (Q.conjBy k).conjBy l at hh
  rwa [hQk, hswap] at hh

/-- The source's condition (*) reduces to an actual line conjugator whose square
lies in H. No normality in G is needed for U_H or Q_H. -/
theorem no_asymmetric_pair_of_center_conjugator
    (H V₃ : Subgroup G) (z g h l : G)
    (hH : H = centralizer ({z} : Set G)) (hz : z ≠ 1)
    (hcard : Nat.card (zpowers z) = 2) (hh : h ∈ H)
    (hline : ((zpowers z).conjBy g).conjBy h = (zpowers z).conjBy l)
    (hsquare : l ^ 2 ∈ H)
    (hinside : Source.UH H V₃ ≤ (Source.QH H).conjBy g)
    (houtside : ¬ (Source.UH H V₃).conjBy g ≤ Source.QH H) : False := by
  have hU : H ≤ normalizer (Source.UH H V₃ : Set G) :=
    le_normalizer_conjugateSpanBy V₃ H
  have hQ : H ≤ normalizer (Source.QH H : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hUh : (Source.UH H V₃).conjBy h = Source.UH H V₃ :=
    mem_normalizer_iff_map_conj_eq.mp (hU hh)
  have hQh : (Source.QH H).conjBy h = Source.QH H :=
    mem_normalizer_iff_map_conj_eq.mp (hQ hh)
  apply no_interchange_of_asymmetric_containment H (Source.UH H V₃) (Source.QH H)
    z (h * g) l hH hz hcard hU hQ (by rwa [conjBy_conjBy] at hline) hsquare
  · have hi := map_mono (f := (MulAut.conj h).toMonoidHom) hinside
    change (Source.UH H V₃).conjBy h ≤ ((Source.QH H).conjBy g).conjBy h at hi
    simpa only [hUh, conjBy_conjBy] using hi
  · intro hi
    apply houtside
    have hj := map_mono (f := (MulAut.conj h⁻¹).toMonoidHom) hi
    change ((Source.UH H V₃).conjBy (h * g)).conjBy h⁻¹ ≤
      (Source.QH H).conjBy h⁻¹ at hj
    have hQhi : (Source.QH H).conjBy h⁻¹ = Source.QH H :=
      mem_normalizer_iff_map_conj_eq.mp (hQ (H.inv_mem hh))
    simpa only [conjBy_conjBy, inv_mul_cancel_left, hQhi] using hj

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair
end
