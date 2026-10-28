module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairNormalizer

/-!
# The whole intersection of the actual two endpoints

The intersection normalizes both radicals, hence their original seed plane.
The full plane normalizer lies in the original seed normalizer of order10752.
Its order also divides the endpoint order960; their gcd is192. A common
subgroup of order192 is therefore the entire intersection, including its
odd part. No amalgam marking or endpoint-intersection equality is assumed.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

/-- A common order192 subgroup of the actual paired endpoints is their
whole literal intersection. -/
theorem TypeAt.paired_endpoint_whole_intersection (h : TypeAt z V)
    (W A : Subgroup G) [IsElementaryAbelian 2 A]
    (hWV : W ≤ V) (hW4 : Nat.card W = 4) (hA16 : Nat.card A = 16)
    (hWA : W ≤ A) (hAC : A ≤ centralizer (W : Set G))
    (hAP : A ⊓ (normalizer (V : Set G)).pCoreIn 2 = W)
    (p : G) (hp : p ∈ (normalizer (V : Set G)).pCoreIn 2) (hpW : p ^ 2 ∉ W)
    (P₁ P₂ J : Subgroup G) (hP₁ : P₁ ≤ normalizer (A : Set G))
    (hP₂ : P₂ ≤ normalizer (A.map (MulAut.conj p).toMonoidHom : Set G))
    (hc₁ : Nat.card P₁ = 960) (hJ : J ≤ P₁ ⊓ P₂) (hcJ : Nat.card J = 192) :
    P₁ ⊓ P₂ = J := by
  have hNW : P₁ ⊓ P₂ ≤ normalizer (W : Set G) := by
    have hn := inf_le_inf hP₁ hP₂
    rw [h.paired_plane_radicals_normalizer W A hWV hW4 hA16 hWA hAC hAP p hp hpW] at hn
    exact hn.trans inf_le_right
  have hM : P₁ ⊓ P₂ ≤ normalizer (V : Set G) :=
    hNW.trans (h.plane_normalizer_le_seed_normalizer W hWV hW4)
  have hd₁ : Nat.card (P₁ ⊓ P₂ : Subgroup G) ∣ 960 :=
    hc₁ ▸ card_dvd_of_le (show P₁ ⊓ P₂ ≤ P₁ from inf_le_left)
  have hd₂ : Nat.card (P₁ ⊓ P₂ : Subgroup G) ∣ 10752 :=
    h.normalizer_card ▸ card_dvd_of_le hM
  have hd : Nat.card (P₁ ⊓ P₂ : Subgroup G) ∣ 192 := by
    have hh := Nat.dvd_gcd hd₁ hd₂
    norm_num at hh
    exact hh
  exact (eq_of_le_of_card_ge hJ (by
    rw [hcJ]
    exact Nat.le_of_dvd (by decide : 0 < 192) hd)).symm

end CFSG.Quasithin.HigmanSims
