module

public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterTransport
public import Stellmacher.Recognition.Parrott.SecondCentralizerOuterWitness

/-!
# Outer geometry for the second centralizer

The lower transport module proves that each involution of C_N(v) outside
Ω₁(O₂(N)) has a conjugate in the original two-core outside its derived
subgroup, retaining a conjugator in C_N(v). The witness module constructs
an involution outside omega whose centralizer in C_N(v) is a compatible
fixed join, with v outside its omega center. The fixed-join normalizer
bound then gives the ambient normalizer assertion.

Keeping the transport interface below this assembly permits the witness
construction to use it without an import cycle.

Source: D. Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678 and §4, p.682.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

/-- A fixed-join witness with the supplied point outside its omega center
completes the elementary-centralizer and ambient normalizer assertions. -/
public theorem normalizer_fixed_outer_geometry_of_fixed_join_witness
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let C := centralizer ({v} : Set G)
    let V := N ⊓ C
    let P := (d.sylow : Subgroup G) ⊓ C
    let H := centralizer ({z} : Set G)
    (∃ (w : G) (e : ParrottSecondElementaryData z),
      w ∈ P ∧ orderOf w = 2 ∧ w ∉ W ∧
      e.F = V ⊓ centralizer ({w} : Set G) ∧
      let M := normalizer (e.F : Set G)
      let Kₑ := pCore 2 M
      let Uₑ := omega₁ Kₑ (p := 2)
      v ∉ (center Uₑ).map ((M.subtype.comp Kₑ.subtype).comp Uₑ.subtype)) →
    ∃ w : G, w ∈ V ∧ orderOf w = 2 ∧ w ∉ W ∧
      let S := V ⊓ centralizer ({w} : Set G)
      IsElementaryAbelian 2 S ∧ Nat.card S = 32 ∧
      (∃ a : H, d.F.map (MulAut.conj (a : G)).toMonoidHom = S) ∧
      C ⊓ normalizer (S : Set G) ≤ V := by
  intro N K W C V P H hwitness
  obtain ⟨w, e, hwP, hw2, hwW, heF, hvout⟩ := hwitness
  let J := pCore 2 H
  let E := (commutator J).map (H.subtype.comp J.subtype)
  have hvE : v ∈ E :=
    (d.normalizer_core_omega_structure h hN hproper).2.2.1
      (d.normalizer_three_fixed_point_geometry h hN hproper Q v hv hfix).1 |>.1
  have hveF : v ∈ e.F := by
    rw [heF]
    have hvF : v ∈ d.F := (hfix.symm ▸ mem_zpowers v).1
    exact ⟨⟨d.sylow_le_normalizer (d.le_sylow hvF),
      mem_centralizer_singleton_iff.mpr rfl⟩,
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hwP.2).symm⟩
  have heproper : (e.sylow : Subgroup G) < normalizer (e.F : Set G) := by
    apply lt_of_le_of_ne e.sylow_le_normalizer
    intro he
    exact hproper.ne (e.normalizer_eq_sylow_of_normalizer_eq_sylow d h he.symm).symm
  obtain ⟨a, ha⟩ := d.exists_conjugate_fixed_join e h
  refine ⟨w, ⟨d.sylow_le_normalizer hwP.1, hwP.2⟩, hw2, hwW, ?_⟩
  change IsElementaryAbelian 2 (V ⊓ centralizer ({w} : Set G) : Subgroup G) ∧ _
  rw [← heF]
  exact ⟨e.elementary, e.card, ⟨a, ha⟩,
    d.fixed_join_normalizer_le_of_outside_omega_center e h hN heproper v ⟨hvE, hveF⟩ hvout⟩

/-- There is an involution of V outside omega whose V-centralizer is an
elementary subgroup of order 32, H-conjugate to the supplied F, and whose
normalizer inside C_G(v) is contained in V. -/
public theorem normalizer_fixed_outer_geometry
    {G : Type*} [Group G] [Finite G] {z : G}
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hN : IsNTwoGroup G)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) (v : G) (hv : orderOf v = 2)
    (hfix : d.F ⊓ centralizer ((Q : Subgroup (normalizer (d.F : Set G))).map
      (normalizer (d.F : Set G)).subtype : Set G) = zpowers v) :
    let N := normalizer (d.F : Set G)
    let K := pCore 2 N
    let W := (omega₁ K (p := 2)).map (N.subtype.comp K.subtype)
    let C := centralizer ({v} : Set G)
    let V := N ⊓ C
    let H := centralizer ({z} : Set G)
    ∃ w : G, w ∈ V ∧ orderOf w = 2 ∧ w ∉ W ∧
      let S := V ⊓ centralizer ({w} : Set G)
      IsElementaryAbelian 2 S ∧ Nat.card S = 32 ∧
      (∃ a : H, d.F.map (MulAut.conj (a : G)).toMonoidHom = S) ∧
      C ⊓ normalizer (S : Set G) ≤ V := by
  exact d.normalizer_fixed_outer_geometry_of_fixed_join_witness h hN hproper Q v hv hfix
    (d.normalizer_fixed_join_witness h hN hproper Q v hv hfix)

end Stellmacher.Recognition.ParrottSecondElementaryData
