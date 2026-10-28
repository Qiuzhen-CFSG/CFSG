module

public import Stellmacher.Recognition.Parrott.LocalSecondCentralizer.Quotient.Abelian.Geometry
public import Stellmacher.Recognition.Parrott.LocalNormalizer.InvolutionCosets

/-!
# Elementary-point displacement in the actual omega subgroup

The involution generators of Ω₁(K) can be transported into E∨F. Its derived
subgroup is ⟨z⟩, and the whole normalizer preserves Z(K), so [Ω₁(K),F]≤Z(K).
For k in F outside Z(Y), the pair normalizer can displace k only by v.
The displacement bound and v∉Z(K) exclude that possibility. Thus its
relative pair normalizer is exactly its ordinary centralizer in Y.

Source: Parrott (1972), Lemma 8, printed p.683, elementary branch of
observation (ii), using the local calculations on pp.677–678.
-/

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition.ParrottNormalizerFusionData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} (n : ParrottNormalizerFusionData d)

include n

/-- The actual omega subgroup acts trivially on F modulo Z(K).
Transport its involution generators into E∨F, where the commutator is the
original involution line; normality of Z(K) then transports that bound back. -/
public theorem omega_elementary_commutator_le_coreCenter
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let i := N.subtype.comp K.subtype
    let W := (omega₁ K (p := 2)).map i
    let ZK := (center K).map i
    ⁅W, d.F⁆ ≤ ZK := by
  intro N K i W ZK
  let H := centralizer ({z} : Set G)
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hi : Function.Injective i := N.subtype_injective.comp K.subtype_injective
  have hgen (u : K) (hu : u ^ 2 = 1) (f : G) (hf : f ∈ d.F) :
      ⁅i u, f⁆ ∈ ZK := by
    obtain ⟨a, ha⟩ := d.normalizer_core_involution_transport_of_local_inputs
      h hlocal n.sylow_lt_normalizer n.Q n.core_fixed_le_derived (i u)
      (mem_map_of_mem N.subtype u.property)
      (by simpa only [map_pow, map_one] using congrArg i hu)
    let g := MulAut.conj ((a : N) : G)
    have hf' : g f ∈ d.F :=
      (mem_normalizer_iff.mp (a : N).property f).mp hf
    have hc : ⁅g (i u), g f⁆ ∈ zpowers z := by
      have hh := commutator_mem_commutator ha (mem_sup_right hf' : g f ∈ E ⊔ d.F)
      rw [← map_subtype_commutator, d.elementary_join_commutator h] at hh
      exact hh
    have hcZ : g ⁅i u, f⁆ ∈ ZK := by
      rw [map_commutatorElement]
      exact (zpowers_le.mpr d.z_mem_normalizer_core_center) hc
    exact (mem_normalizer_iff.mp
      (d.normalizer_core_centers_normalized.1 (a : N).property) ⁅i u, f⁆).mpr hcZ
  let q := QuotientGroup.mk' (center K)
  let B := d.F.comap i
  let C := (centralizer (B.map q : Set (K ⧸ center K))).comap q
  have hUC : omega₁ K (p := 2) ≤ C := by
    apply (closure_le _).mpr
    intro u hu
    change u ^ (2 ^ 1) = 1 at hu
    have hu2 : u ^ 2 = 1 := by simpa only [pow_one] using hu
    change q u ∈ centralizer (B.map q : Set (K ⧸ center K))
    rintro _ ⟨a, ha, rfl⟩
    apply Eq.symm
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    have hh : i ⁅u, a⁆ ∈ (center K).map i := by
      rw [map_commutatorElement]
      exact hgen u hu2 (i a) ha
    exact (comap_map_eq_self_of_injective hi (center K)) ▸
      (show ⁅u, a⁆ ∈ ((center K).map i).comap i from hh)
  apply commutator_le.mpr
  rintro _ ⟨u, hu, rfl⟩ f hf
  obtain ⟨fN, hfN, he⟩ := n.omega_le_core (n.elementary_le_omega hf)
  let fK : K := ⟨fN, hfN⟩
  have hfK : fK ∈ B := by
    change i fK ∈ d.F
    exact he.symm ▸ hf
  have hcomm := hUC hu (q fK) (mem_map_of_mem q hfK)
  have hc : ⁅u, fK⁆ ∈ center K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change q ⁅u, fK⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm
  have hh := mem_map_of_mem i hc
  change i fK = f at he
  simpa only [map_commutatorElement, he] using hh

end Stellmacher.Recognition.ParrottNormalizerFusionData

open Subgroup
open scoped commutatorElement
namespace Stellmacher.Recognition.ParrottSecondTransferData
variable {G : Type*} [Group G] [Finite G] {z : G}
  {d : ParrottSecondElementaryData z} {n : ParrottNormalizerFusionData d}
  (t : ParrottSecondTransferData n)

/-- In the elementary branch of observation (ii), normalizing the actual
pair already fixes k. The possible displacement v is excluded because
[Ω₁(K),F] lies in Z(K), whereas v does not. -/
public theorem pairNormalizer_eq_sylow_centralizer_of_mem_elementary
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    {k : G} (hkF : k ∈ d.F) (hkZ : k ∉ t.sylowCenter) :
    t.pairNormalizer k = t.sylowImage ⊓ centralizer ({k} : Set G) := by
  classical
  let : IsElementaryAbelian 2 d.F := d.elementary
  obtain ⟨a, ha, rfl⟩ := t.elementary_le_sylow_image hkF
  let q := QuotientGroup.mk' (zpowers t.v)
  have ha2 : a ^ 2 = 1 := t.embedding_injective (by
    rw [map_pow, map_one]
    exact elemPow_eq_one_of_isElementaryAbelian (t.embedding a) hkF)
  have hqa2 : orderOf (q a) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ha2, map_one]
    · intro he
      have hamem : a ∈ zpowers t.v := (QuotientGroup.eq_one_iff _).mp he
      apply hkZ
      have hh := mem_map_of_mem t.embedding hamem
      have hvZ : zpowers n.v ≤ t.sylowCenter := zpowers_le.mpr t.v_mem_sylowCenter
      apply hvZ
      simpa only [MonoidHom.map_zpowers, t.v_image] using hh
  apply le_antisymm
  · intro y hy
    have hyp : y ∈ ((t.quotientLocalCentralizer (q a)).comap q).map t.embedding :=
      (t.localCentralizer_preimage_map hqa2).symm ▸ hy
    obtain ⟨b, hb, rfl⟩ := hyp
    have hbcent : q b ∈ centralizer ({q a} : Set t.Quotient) := hb.2
    have hbV : ⁅t.embedding b, t.embedding a⁆ ∈ zpowers n.v := by
      have hbker : ⁅b, a⁆ ∈ zpowers t.v := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q ⁅b, a⁆ = 1
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr
          (mem_centralizer_singleton_iff.mp hbcent)
      simpa only [MonoidHom.map_zpowers, t.v_image, map_commutatorElement] using
        (mem_map_of_mem t.embedding hbker)
    have hbZ := n.omega_elementary_commutator_le_coreCenter h hlocal
      (commutator_mem_commutator (t.sylow_image_le_omega hy.1) hkF)
    have hb1 : ⁅t.embedding b, t.embedding a⁆ = 1 := by
      rw [mem_zpowers_iff_mem_range_orderOf, n.v_order] at hbV
      obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hbV
      have hj2 : j < 2 := Finset.mem_range.mp hj
      interval_cases j
      · simpa only [pow_zero] using he.symm
      · have he' : ⁅t.embedding b, t.embedding a⁆ = n.v := by
          simpa only [pow_one] using he.symm
        exact (n.v_not_mem_core_center (he' ▸ hbZ)).elim
    exact ⟨hy.1, mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hb1)⟩
  · intro y hy
    refine ⟨hy.1, Subgroup.centralizer_le_normalizer _ ?_⟩
    have hyv := mem_centralizer_singleton_iff.mp
      (t.embedding_range_le_centralizer ((map_le_range t.embedding _) hy.1))
    have hp : zpowers (t.embedding a) ⊔ zpowers n.v ≤ centralizer ({y} : Set G) :=
      sup_le
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
          (mem_centralizer_singleton_iff.mp hy.2).symm))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyv.symm))
    intro c hc
    exact mem_centralizer_singleton_iff.mp (hp hc)

end Stellmacher.Recognition.ParrottSecondTransferData
