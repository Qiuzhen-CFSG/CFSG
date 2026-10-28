module

public import Theory.GroupTheory.SylowCentralFusion.LocalMover
public import Theory.GroupTheory.ConjugationFamily

/-!
# The center-containing central fusion selection

Decompose a conjugator using the existing extremal centric fusion family.
Before the first step moving z, the element is still z. This step cannot be
a centralizer step, so its subgroup Q is self-centralizing in T and contains
Z(T). Extremality supplies the actual Sylow subgroup of N_G(Q). The shared
local argument then gives an odd-order mover normalizing both Q and C_T(Q).

This proves clauses (a), (b), (d), (e) of Glauberman's Lemma 1, pp.155–156,
Math. Z. 93 (1966), DOI 10.1007/BF01111033, by the equivalent centric fusion
route. The separate normal-closure selection is not asserted here.
-/

namespace SylowCentralFusion
open Subgroup BenderSuzuki.External BenderSuzuki.PFchapter1section1
universe u
variable {G : Type u} [Group G]

private theorem first_moving_step [Finite G] (T : Sylow 2 G) (z : G)
    {g : G}
    (hd : HuppertCentricConjugationDecomposition (T : Subgroup G)
      (HuppertExtremal T) (zpowers z) g)
    (hm : g⁻¹ * z * g ≠ z) :
    ∃ Q : Subgroup G, HuppertExtremal T Q ∧ z ∈ Q ∧
      subgroupCentralizerIn (T : Subgroup G) Q ≤ Q ∧
      ∃ h ∈ normalizer (Q : Set G), h * z * h⁻¹ ≠ z := by
  induction hd with
  | one => simp at hm
  | @tail g h Q hd hQ hQT hAQ hh hc ih =>
    by_cases hg : g⁻¹ * z * g = z
    · have hzQ : z ∈ Q := by
        have hzmem : g⁻¹ * z * g ∈ rightConjugate (zpowers z) g :=
          mem_map.mpr ⟨z, mem_zpowers z, by simp⟩
        exact hg ▸ hAQ hzmem
      have hhmove : h⁻¹ * z * h ≠ z := by
        intro he
        apply hm
        calc
          (g * h)⁻¹ * z * (g * h) = h⁻¹ * (g⁻¹ * z * g) * h := by group
          _ = z := by rw [hg, he]
      refine ⟨Q, hQ, hzQ, ?_, h⁻¹, (normalizer (Q : Set G)).inv_mem hh, ?_⟩
      · rcases hc with hc | hc
        · exact hc
        · exfalso
          apply hhmove
          have he := mem_centralizer_iff.mp hc z hzQ
          calc
            h⁻¹ * z * h = h⁻¹ * (z * h) := mul_assoc _ _ _
            _ = h⁻¹ * (h * z) := by rw [he]
            _ = z := inv_mul_cancel_left _ _
      · simpa only [inv_inv] using hhmove
    · exact ih hg

/-- At the first step which moves z in a centric fusion decomposition,
the selected extremal subgroup contains z and the ambient image of Z(T). -/
public theorem exists_center_normalizerSelection [Finite G] (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G))
    (hf : ∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) ∧ g * z * g⁻¹ ≠ z) :
    ∃ s : NormalizerSelection T z,
      (center T).map (T : Subgroup G).subtype ≤ s.subgroup := by
  obtain ⟨g, hgT, hgm⟩ := hf
  have hzP : zpowers z ≤ (T : Subgroup G) := zpowers_le.mpr hzT
  have hzgP : rightConjugate (zpowers z) g⁻¹ ≤ (T : Subgroup G) := by
    change (zpowers z).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ _
    rw [inv_inv, map_le_iff_le_comap, zpowers_le]
    exact hgT
  obtain ⟨Q, hQ, hzQ, hcent, hmove⟩ := first_moving_step T z
    (HuppertExtremal.centric_conjugation_decomposition T hzP hzgP)
    (by simpa only [inv_inv] using hgm)
  refine ⟨⟨Q, hQ.1, hzQ, hQ.exists_sylow_normalizer, hmove⟩, ?_⟩
  rintro x ⟨c, hc, rfl⟩
  apply hcent
  refine ⟨c.property, ?_⟩
  change (c : G) ∈ centralizer (Q : Set G)
  rw [mem_centralizer_iff]
  intro q hq
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨q, hQ.1 hq⟩)

/-- The center-containing selection of Glauberman's fusion lemma.
In fact the argument works for any central element, regardless of its order. -/
public theorem exists_center_witness [Finite G] (T : Sylow 2 G) (z : G)
    (hzT : z ∈ (T : Subgroup G))
    (hz : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hf : ∃ g : G, g * z * g⁻¹ ∈ (T : Subgroup G) ∧ g * z * g⁻¹ ≠ z) :
    ∃ w : Witness T z, (center T).map (T : Subgroup G).subtype ≤ w.subgroup := by
  obtain ⟨s, hs⟩ := exists_center_normalizerSelection T z hzT hf
  obtain ⟨w, hw⟩ := s.exists_witness T z hz
  exact ⟨w, hw ▸ hs⟩

end SylowCentralFusion
