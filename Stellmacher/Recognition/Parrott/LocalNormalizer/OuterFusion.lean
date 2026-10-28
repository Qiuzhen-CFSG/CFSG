module

public import Stellmacher.Recognition.Parrott.NormalizerOuterFusion
public import Stellmacher.Recognition.Parrott.LocalInputs
public import Stellmacher.Recognition.Parrott.NormalizerCoreSolvable
public import Stellmacher.Recognition.Parrott.LocalNormalizer.CoreOmega
public import Stellmacher.Recognition.Parrott.LocalNormalizer.InvolutionCosets

/-!
# The actual second normalizer from local inputs

These calculations retain the supplied second elementary subgroup and Sylow.
The original derived-core normalizer identity and solvability of the actual
second normalizer replace the ambient N₂ assumption. All subgroup images,
centers, omega subgroups and conjugators are the original literal ones.

Source: Parrott, *A characterization of the Tits' simple group* (1972),
pp.677–678. This is the local-input extension of `NormalizerOuterFusion`.
-/

open Subgroup

namespace Stellmacher.Recognition.ParrottSecondElementaryData

variable {G : Type*} [Group G] [Finite G] {z : G}

/-- There is a pair y, yz of outer involutions in the supplied normalizer core,
so a two-class cover may be applied to these particular representatives. -/
public theorem exists_normalizer_core_outer_involution_pair_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    ∃ y : G, y ∈ X ∧ y ∉ J.map H.subtype ∧ orderOf y = 2 ∧
      y * z ∈ X ∧ y * z ∉ J.map H.subtype ∧ orderOf (y * z) = 2 := by
  intro H J N X
  obtain ⟨y, hyX, hy2, hyJ⟩ :=
    d.exists_normalizer_core_involution_outside_original_core_of_local_inputs h hlocal hproper
  exact ⟨y, hyX, hyJ, hy2, d.normalizer_core_outer_involution_mul_z h y hyX hyJ hy2⟩

/-- The H-class cover and transport for outer involutions in the normalizer
core suffice for all outer involutions in the supplied Sylow. Both local
calculations are explicit premises of this assembly theorem. -/
public theorem outer_involution_transport_of_local_calculations_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G)) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let L := H ⊔ N
    (∀ y u : G, y ∈ H → y ∉ J.map H.subtype → orderOf y = 2 →
      u ∈ H → u ∉ J.map H.subtype → orderOf u = 2 →
      ∃ c : H, (c : G) * u * (c : G)⁻¹ = y ∨
        (c : G) * u * (c : G)⁻¹ = y * z) →
    (∀ y : G, y ∈ X → y ∉ J.map H.subtype → orderOf y = 2 →
      ∃ n : N, (n : G) * y * (n : G)⁻¹ ∈ E ⊔ d.F) →
    ∀ u : G, u ∈ (d.sylow : Subgroup G) → u ∉ J.map H.subtype →
      orderOf u = 2 → ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E := by
  intro H J E N X L hclasses htransport u huT huJ hu2
  obtain ⟨y, hyX, hyJ, hy2, hyzX, hyzJ, hyz2⟩ :=
    d.exists_normalizer_core_outer_involution_pair_of_local_inputs h hlocal hproper
  obtain ⟨c, hc⟩ := hclasses y u
    (d.sylow_le_centralizer (d.normalizer_core_le_sylow hyX)) hyJ hy2
    (d.sylow_le_centralizer huT) huJ hu2
  have hstep (w : G) (hwX : w ∈ X) (hwJ : w ∉ J.map H.subtype)
      (hw2 : orderOf w = 2) (hcw : (c : G) * u * (c : G)⁻¹ = w) :
      ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E := by
    obtain ⟨n, hnjoin⟩ := htransport w hwX hwJ hw2
    have hn := d.outer_involution_normalizer_conjugate_mem_derived h w hwJ hw2 n hnjoin
    refine ⟨⟨(n : G) * (c : G), L.mul_mem (mem_sup_right n.property)
      (mem_sup_left c.property)⟩, ?_⟩
    change ((n : G) * (c : G)) * u * ((n : G) * (c : G))⁻¹ ∈ E
    rw [mul_inv_rev]
    simpa only [← hcw, mul_assoc] using hn
  rcases hc with hc | hc
  · exact hstep y hyX hyJ hy2 hc
  · exact hstep (y * z) hyzX hyzJ hyz2 hc

/-- Every outer involution of the supplied Sylow is conjugate into the derived
core E by an element of H ∨ N. The H-class cover first transports it to one of
the two outer representatives in the normalizer core; the supplied Q then
transports that representative into E. -/
public theorem outer_involution_transport_of_local_inputs
    (d : ParrottSecondElementaryData z)
    (h : ParrottCentralizerHypotheses z) (hlocal : ParrottLocalInputs z)
    (hproper : (d.sylow : Subgroup G) < normalizer (d.F : Set G))
    (Q : Sylow 3 (normalizer (d.F : Set G))) :
    let H := centralizer ({z} : Set G)
    let J := pCore 2 H
    let E := (commutator J).map (H.subtype.comp J.subtype)
    let N := normalizer (d.F : Set G)
    let X := (pCore 2 N).map N.subtype
    let D := (commutator X).map X.subtype
    let A := (Q : Subgroup N).map N.subtype
    let L := H ⊔ N
    X ⊓ centralizer (A : Set G) ≤ D →
    ∀ v : G, orderOf v = 2 → d.F ⊓ centralizer (A : Set G) = zpowers v →
    ∀ u : G, u ∈ (d.sylow : Subgroup G) → u ∉ J.map H.subtype →
      orderOf u = 2 → ∃ l : L, (l : G) * u * (l : G)⁻¹ ∈ E := by
  intro H J E N X D A L hCD v hv hfix
  exact d.outer_involution_transport_of_local_calculations_of_local_inputs h hlocal hproper
    (parrott_outer_involution_classes z h)
    (d.normalizer_core_outer_involution_conjugate_into_elementary_join_of_local_inputs
      h hlocal hproper Q hCD v hv hfix)

end Stellmacher.Recognition.ParrottSecondElementaryData
