module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.MarkedPairedRadicals
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SixteenSymplecticNormalizer
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedRadicals

/-!
# An actual cubic lift and common order-192 subgroup

An arbitrary lift g of a quotient cubic has g³ in the elementary kernel,
so g⁶=1 and g⁴ is a cubic with exactly the requested quotient image.
The full marked action carries preservation of the seed plane back to the
original group. The exact pair-normalizer theorem then places the cubic
in both radical normalizers, and the coprime product count constructs the
literal order-192 join. The quotient actor is specific marked group data;
no endpoint, splitting, or Borel premise is used.

The import-all edge is an intentional internal continuation of the frozen
paired-radical commutator and cardinality proof.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem cubic_lift {J Q : Type*} [Group J] [Group Q]
    (q : J →* Q) (hq : Function.Surjective q)
    (hkernel : ∀ g : J, q g = 1 → g ^ 2 = 1)
    (τ : Q) (hτ : orderOf τ = 3) : ∃ t : J, orderOf t = 3 ∧ q t = τ := by
  obtain ⟨g, hg⟩ := hq τ
  have hτ3 : τ ^ 3 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hg6 : g ^ 6 = 1 := by
    have hh := hkernel (g ^ 3) (by rw [map_pow, hg, hτ3])
    simpa only [← pow_mul] using hh
  have ht3 : (g ^ 4) ^ 3 = 1 := by
    rw [← pow_mul]
    change g ^ (6 * 2) = 1
    rw [pow_mul, hg6, one_pow]
  have htq : q (g ^ 4) = τ := by
    rw [map_pow, hg]
    change τ ^ (3 + 1) = τ
    rw [pow_succ, hτ3, one_mul]
  refine ⟨g ^ 4, orderOf_eq_prime ht3 ?_, htq⟩
  intro ht
  have he : τ = 1 := htq.symm.trans (ht ▸ q.map_one)
  rw [he, orderOf_one] at hτ
  omega

/-- A specified cubic in the literal symplectic normalizer quotient that
preserves the original seed plane lifts to an actual common cubic. Its
join with the original paired radicals has order192, and the full marked
action on the first radical is retained. -/
theorem TypeAt.paired_radicals_common_cubic (h : TypeAt z V) (W A : Subgroup G)
    [IsElementaryAbelian 2 A] (hWV : W ≤ V) (hW4 : Nat.card W = 4)
    (hA16 : Nat.card A = 16) (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (e : Additive A ≃ₗ[ZMod 2] Matrix.PSp4Three.Vector 2 (ZMod 2))
    (φ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
      Matrix.PSp4Three.Sp 2 (ZMod 2))
    (hφ : ∀ (g : normalizer (A : Set G)) (x : A),
      (φ (QuotientGroup.mk g)).val *ᵥ (e (Additive.ofMul x)) =
        e (Additive.ofMul (A.normalizerMonoidHom g x)))
    (τ : Matrix.PSp4Three.Sp 2 (ZMod 2)) (hτ : orderOf τ = 3)
    (hτW : ∀ x : A, (x : G) ∈ W → ∃ y : A, (y : G) ∈ W ∧
      τ.val *ᵥ e (Additive.ofMul x) = e (Additive.ofMul y)) :
    let B := A.map (MulAut.conj p).toMonoidHom
    ∃ t : normalizer (A : Set G), orderOf (t : G) = 3 ∧
      φ (QuotientGroup.mk t) = τ ∧
      (t : G) ∈ normalizer (B : Set G) ∧ (t : G) ∈ normalizer (W : Set G) ∧
      (∀ x : A, τ.val *ᵥ e (Additive.ofMul x) =
        e (Additive.ofMul (A.normalizerMonoidHom t x))) ∧
      Disjoint (A ⊔ B) (zpowers (t : G)) ∧
      (A ⊔ B) ⊔ zpowers (t : G) ≤
        normalizer (A : Set G) ⊓ normalizer (B : Set G) ∧
      Nat.card ((A ⊔ B) ⊔ zpowers (t : G) : Subgroup G) = 192 := by
  let N := normalizer (A : Set G)
  let q : N →* Matrix.PSp4Three.Sp 2 (ZMod 2) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (A.subgroupOf N))
  have hq : Function.Surjective q := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk (g : N) (hg : q g = 1) : g ^ 2 = 1 := by
    have hgA : (g : G) ∈ A := (QuotientGroup.eq_one_iff g).mp
      (φ.injective (hg.trans φ.map_one.symm))
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (g : G) hgA)
  obtain ⟨t, ht3, htq⟩ := cubic_lift q hq hk τ hτ
  have htG : orderOf (t : G) = 3 := (orderOf_coe t).trans ht3
  have htφ : φ (QuotientGroup.mk t) = τ := htq
  have hact (x : A) : τ.val *ᵥ e (Additive.ofMul x) =
      e (Additive.ofMul (A.normalizerMonoidHom t x)) := by
    rw [← htφ]
    exact hφ t x
  have htW : (t : G) ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro w ⟨x, hxW, rfl⟩
      obtain ⟨y, hyW, hy⟩ := hτW ⟨x, hWA hxW⟩ hxW
      have he := e.injective ((hact ⟨x, hWA hxW⟩).symm.trans hy)
      have hv := congrArg (fun a : Additive A => (a.toMul : G)) he
      change (t : G) * x * (t : G)⁻¹ = (y : G) at hv
      change (t : G) * x * (t : G)⁻¹ ∈ W
      exact hv.symm ▸ hyW
    · exact (card_map_of_injective (MulAut.conj (t : G)).injective).ge
  let B := A.map (MulAut.conj p).toMonoidHom
  have hpairN := h.paired_plane_radicals_normalizer W A hWV hW4 hA16 hWA hAC hAP p hp hpW
  have htB : (t : G) ∈ normalizer (B : Set G) :=
    (hpairN.symm ▸ (show (t : G) ∈ N ⊓ normalizer (W : Set G) from ⟨t.property, htW⟩)).2
  obtain ⟨hi, hc⟩ := conjugate_pair h W A hWV hW4 hWA hAC hAP p hp hpW
  change A ⊓ B = W at hi
  change ⁅A, B⁆ ≤ W at hc
  have hWB : W ≤ B := hi ▸ (show A ⊓ B ≤ B from inf_le_right)
  have hAB := le_normalizer_iff_commutator_le_right.mpr (hc.trans hWB)
  have hBA := le_normalizer_iff_commutator_le_left.mpr (hc.trans hWA)
  have hB16 : Nat.card B = 16 := (card_map_of_injective (MulAut.conj p).injective).trans hA16
  have hS64 : Nat.card (A ⊔ B : Subgroup G) = 64 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes A B hBA
    rw [hA16, hB16, hi, hW4] at hh
    omega
  have htN : (t : G) ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) :=
    normalizer_inf_normalizer_le_normalizer_sup A B ⟨t.property, htB⟩
  have hdis : Disjoint (A ⊔ B) (zpowers (t : G)) :=
    disjoint_of_coprime_natCard (by rw [hS64, Nat.card_zpowers, htG]; decide)
  have h192 : Nat.card ((A ⊔ B) ⊔ zpowers (t : G) : Subgroup G) = 192 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint _ _ (zpowers_le.mpr htN) hdis,
      hS64, Nat.card_zpowers, htG]
  have hle : (A ⊔ B) ⊔ zpowers (t : G) ≤ N ⊓ normalizer (B : Set G) :=
    sup_le (sup_le (le_inf A.le_normalizer hAB) (le_inf hBA B.le_normalizer))
      (zpowers_le.mpr ⟨t.property, htB⟩)
  exact ⟨t, htG, htφ, htB, htW, hact, hdis, hle, h192⟩

end CFSG.Quasithin.HigmanSims
