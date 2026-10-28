module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.NormalStructure
public import Glauberman.ZStar

/-!
# The first ambient fusion step for G₂(3)-type groups

The distinguished involution cannot be weakly closed in any ambient Sylow
containing it. Otherwise weak closure first makes it Sylow-central, and the
proved Z-star theorem makes its image central modulo the actual odd core.
Coprime centralizer lifting then gives G = C_G(z)O(G), contradicted by the
normal-subgroup argument using the actual M. Thus every such Sylow contains
a distinct ambient conjugate. A final theorem constructs a Sylow and fusion
witness without any additional input.

This is the Z-star step of Fong–Wong §2F, Nagoya Math. J. 36 (1969),
pp.153–154, DOI 10.1017/S0027763000013180, for the configuration of
Aschbacher–Smith I.4.5, printed p.417. It does not yet place the conjugate
in H₁H₂, determine the outer involution, or prove the final recognition.
Those obligations remain with `qt-i45-g2-recognition`.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] (c : G2ThreeConfiguration G)

theorem distinguished_involution_not_weakly_closed (z : G) (hz : orderOf z = 2)
    (hH : c.H = centralizer ({z} : Set G)) (S : Sylow 2 G) :
    ¬ Glauberman.ZStar.IsWeaklyClosedInSylow z (S : Subgroup G) := by
  intro hw
  have hcentral : ∀ s ∈ (S : Subgroup G), s * z = z * s := by
    intro s hs
    exact mul_inv_eq_iff_eq_mul.mp (hw.2 s
      ((S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hw.1)
        ((S : Subgroup G).inv_mem hs)))
  have hI : BenderSuzuki.PFAppendixIII.IsInvolution z :=
    ⟨fun h => by simp [h] at hz, by rw [← hz]; exact pow_orderOf_eq_one z⟩
  have hqz := Glauberman.ZStar.glauberman_zstar_local S z hI hw.1 hcentral hw
  let O := pPrimeCore 2 G
  let q := QuotientGroup.mk' O
  let Z := zpowers z
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers, hz]
  let : Fact (IsPGroup 2 Z) := ⟨IsPGroup.of_card (n := 1) hZcard⟩
  have hqZ : Z.map q ≤ center (G ⧸ O) := by
    change (zpowers z).map q ≤ _
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr hqz
  have hqcent : centralizer ((Z.map q : Subgroup (G ⧸ O)) : Set (G ⧸ O)) = ⊤ := by
    apply top_unique
    intro x _ y hy
    exact (mem_center_iff.mp (hqZ hy) x).symm
  have hm : (centralizer (Z : Set G)).map q = ⊤ := by
    rw [← centralizer_map_quotient_eq_map_centralizer 2 Z O inferInstance
      (pPrimeCore_coprime_card (p := 2) (G := G))]
    exact hqcent
  have he : centralizer (Z : Set G) = c.H := by
    change centralizer (zpowers z : Set G) = c.H
    rw [zpowers_eq_closure, centralizer_closure, hH]
  rw [he] at hm
  have hh := congrArg (Subgroup.comap q) hm
  have hk : q.ker = O := QuotientGroup.ker_mk' O
  rw [comap_map_eq, comap_top, hk] at hh
  exact H_sup_oddCore_ne_top c hh

theorem distinguished_involution_fuses_in_sylow (z : G) (hz : orderOf z = 2)
    (hH : c.H = centralizer ({z} : Set G)) (S : Sylow 2 G)
    (hzS : z ∈ (S : Subgroup G)) :
    ∃ g : G, g * z * g⁻¹ ∈ (S : Subgroup G) ∧ g * z * g⁻¹ ≠ z := by
  by_contra! hn
  exact distinguished_involution_not_weakly_closed c z hz hH S ⟨hzS, hn⟩

theorem exists_distinguished_fusion :
    ∃ (z : G) (S : Sylow 2 G) (g : G), orderOf z = 2 ∧
      c.H = centralizer ({z} : Set G) ∧ z ∈ (S : Subgroup G) ∧
      g * z * g⁻¹ ∈ (S : Subgroup G) ∧ g * z * g⁻¹ ≠ z := by
  obtain ⟨z, hz, hH⟩ := exists_involution_centralizer c
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hz]; rfl)
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hzS := hS (mem_zpowers z)
  obtain ⟨g, hg⟩ := distinguished_involution_fuses_in_sylow c z hz hH S hzS
  exact ⟨z, S, g, hz, hH, hzS, hg⟩

end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
