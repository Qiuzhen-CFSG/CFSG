module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.Intersection
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The normalizers of the literal partner pair

A full action of J on the four-group V₀ lets every element of N_G(V₀)
be written as an element of J times an element centralizing V₀. Since
Z≤V₀, that centralizer normalizes U; y-invariance of V₀ gives the same
normalization for Uʸ. Thus both J and E are normal in N_G(V₀).

Source: Aschbacher–Smith, argument in 15.3.56(3), printed p.1147.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
variable {G : Type*} [Group G] (Z ZS : Subgroup G)

/-- The two source planes recover the original H-closure. This is the
seed bridge needed to apply the binary module calculation with V₀. -/
theorem plane_closure_eq (V₀ : Subgroup G) (t : G)
    (hV₀ : V₀ ≤ closureU Z ZS) (ht : t ∈ centralizerH Z)
    (hseed : ZS ≤ V₀ ⊔ rightConjugate V₀ t) :
    localSpan V₀ (centralizerH Z) = closureU Z ZS := by
  have hV : V₀ ≤ localSpan V₀ (centralizerH Z) := le_conjugateSpanBy _ _
  have hVt : rightConjugate V₀ t ≤ localSpan V₀ (centralizerH Z) := by
    rintro _ ⟨v, hv, rfl⟩
    exact (mem_normalizer_iff.mp
      (le_normalizer_conjugateSpanBy V₀ (centralizerH Z)
        ((centralizerH Z).inv_mem ht)) v).mp (hV hv)
  apply le_antisymm
  · exact conjugateSpanBy_le hV₀ (H_normalizes_closureU Z ZS)
  · exact conjugateSpanBy_le (hseed.trans (sup_le hV hVt))
      (le_normalizer_conjugateSpanBy V₀ (centralizerH Z))

/-- The literal conjugation action on the point plane. -/
def planeAction (V₀ : Subgroup G) (y : G)
    (hJV : pairI Z ZS y ≤ normalizer (V₀ : Set G)) :
    pairI Z ZS y →* MulAut V₀ :=
  V₀.normalizerMonoidHom.comp (inclusion hJV)

/-- The centralizer of the invariant point plane normalizes both original
U-conjugates, hence their join and intersection. -/
theorem plane_centralizer_normalizes (V₀ : Subgroup G) (y : G)
    (hZV : Z ≤ V₀) (hyV : y ∈ normalizer (V₀ : Set G)) :
    centralizer (V₀ : Set G) ≤ normalizer (pairI Z ZS y : Set G) ∧
      centralizer (V₀ : Set G) ≤
        normalizer (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) y : Set G) := by
  have hCU : centralizer (V₀ : Set G) ≤ normalizer (closureU Z ZS : Set G) :=
    (centralizer_le hZV).trans (H_normalizes_closureU Z ZS)
  have hyC : y ∈ normalizer (centralizer (V₀ : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer V₀ hyV
  have hCUy : centralizer (V₀ : Set G) ≤
      normalizer (rightConjugate (closureU Z ZS) y : Set G) := by
    intro c hc
    have hconj : y * c * y⁻¹ ∈ centralizer (V₀ : Set G) :=
      (mem_normalizer_iff.mp hyC c).mp hc
    apply le_normalizer_map (MulAut.conj y⁻¹).toMonoidHom
    refine ⟨y * c * y⁻¹, hCU hconj, ?_⟩
    change y⁻¹ * (y * c * y⁻¹) * (y⁻¹)⁻¹ = c
    group
  exact ⟨(le_inf hCU hCUy).trans (normalizer_inf_normalizer_le_normalizer_sup _ _),
    (le_inf hCU hCUy).trans inf_normalizer_le_normalizer_inf⟩

/-- Fullness of the actual action gives the two ambient normalizer fields
used by Partner.EarlierGeometry. -/
theorem partner_normalizers (V₀ : Subgroup G) (y : G)
    (hZS : ZS ≤ centralizerH Z)
    (hplane : V₀ = Z ⊔ rightConjugate Z y)
    (hyV : y ∈ normalizer (V₀ : Set G))
    (hJV : pairI Z ZS y ≤ normalizer (V₀ : Set G))
    (hJE : pairI Z ZS y ≤ normalizer (intersectionE Z ZS y : Set G))
    (hfull : Function.Surjective (planeAction Z ZS V₀ y hJV)) :
    normalizer (V₀ : Set G) ≤ normalizer (pairI Z ZS y : Set G) ∧
      normalizer (V₀ : Set G) ≤ normalizer (intersectionE Z ZS y : Set G) := by
  have hZV : Z ≤ V₀ := by rw [hplane]; exact le_sup_left
  obtain ⟨hCJ, hCE⟩ := plane_centralizer_normalizes Z ZS V₀ y hZV hyV
  change centralizer (V₀ : Set G) ≤ normalizer
    (↑(closureU Z ZS ⊓ rightConjugate (closureU Z ZS) y) : Set G) at hCE
  rw [← intersectionE_eq Z ZS V₀ y hZS hplane hyV] at hCE
  have hsplit : ∀ n ∈ normalizer (V₀ : Set G),
      ∃ j ∈ pairI Z ZS y, j⁻¹ * n ∈ centralizer (V₀ : Set G) := by
    intro n hn
    obtain ⟨j, hj⟩ := hfull (V₀.normalizerMonoidHom ⟨n, hn⟩)
    refine ⟨j, j.property, ?_⟩
    intro v hv
    have he := congrArg Subtype.val (MulEquiv.congr_fun hj ⟨v, hv⟩)
    change (j : G) * v * (j : G)⁻¹ = n * v * n⁻¹ at he
    have hh : (j : G)⁻¹ * n * v * ((j : G)⁻¹ * n)⁻¹ = v := by
      calc
        _ = (j : G)⁻¹ * (n * v * n⁻¹) * j := by group
        _ = (j : G)⁻¹ * ((j : G) * v * (j : G)⁻¹) * j := by rw [← he]
        _ = v := by group
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  constructor
  · intro n hn
    obtain ⟨j, hj, hc⟩ := hsplit n hn
    have hh := (normalizer (pairI Z ZS y : Set G)).mul_mem
      ((pairI Z ZS y).le_normalizer hj) (hCJ hc)
    simpa only [mul_inv_cancel_left] using hh
  · intro n hn
    obtain ⟨j, hj, hc⟩ := hsplit n hn
    have hh := (normalizer (intersectionE Z ZS y : Set G)).mul_mem (hJE hj) (hCE hc)
    simpa only [mul_inv_cancel_left] using hh

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry
