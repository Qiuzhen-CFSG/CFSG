module
public import Theory.GroupTheory.WeakClosureSetFusion
/-!
# Simultaneous Burnside fusion of two marked elements

The Sylow correction in the weak-closure argument can be made inside the
common centralizer of both target marks. It consequently preserves the
ordered pair, while placing the corrected conjugator in the normalizer of
the weakly closed subgroup. No permutation or fusion assumption on the two
marks is needed.

Source: the pointwise form of Burnside fusion, Aschbacher–Smith A.1.35,
used for the marked commuting pair in F.4.42, printed p.295.
-/

open Subgroup
public section
namespace Sylow.PointwiseFusion
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
private theorem exists_conj_map_le (P : Sylow p G) {H : Subgroup G}
    (hH : IsPGroup p H) : ∃ g : G, H.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨Q, hQ⟩ := hH.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  refine ⟨g, ?_⟩
  rw [← hg]
  exact map_mono hQ

private theorem exists_normalizer_correction
    (P : Sylow p G) (W : Subgroup G)
    (hWP : W ≤ (P : Subgroup G))
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (W : Set G))
    (H : Subgroup G) (hWH : W ≤ H) (g : G)
    (hgWH : W.map (MulAut.conj g).toMonoidHom ≤ H) :
    ∃ c : H, (c : G) * g ∈ normalizer (W : Set G) := by
  let V := W.map (MulAut.conj g).toMonoidHom
  have hW : IsPGroup p W := P.isPGroup'.to_le hWP
  obtain ⟨Q, hQ⟩ := (hW.comap_subtype (K := H)).exists_le_sylow
  obtain ⟨c, hc⟩ := exists_conj_map_le Q
    ((hW.map (MulAut.conj g).toMonoidHom).comap_subtype (K := H))
  obtain ⟨k, hk⟩ := exists_conj_map_le P (Q.isPGroup'.map H.subtype)
  have hkW : k ∈ normalizer (W : Set G) := by
    apply hweak
    rintro _ ⟨w, hw, rfl⟩
    apply hk
    exact mem_map_of_mem _ ⟨⟨w, hWH hw⟩, hQ hw, rfl⟩
  have hkcgW : k * (c : G) * g ∈ normalizer (W : Set G) := by
    apply hweak
    rintro _ ⟨w, hw, rfl⟩
    have hwV : MulAut.conj g w ∈ V := mem_map_of_mem _ hw
    have hcQ := hc (mem_map_of_mem (MulAut.conj c).toMonoidHom
      (show (⟨MulAut.conj g w, hgWH hwV⟩ : H) ∈ V.subgroupOf H from hwV))
    have hkP := hk (mem_map_of_mem (MulAut.conj k).toMonoidHom
      (mem_map_of_mem H.subtype hcQ))
    change k * (↑c * (g * w * g⁻¹) * (↑c)⁻¹) * k⁻¹ ∈ (P : Subgroup G) at hkP
    change (k * ↑c * g) * w * (k * ↑c * g)⁻¹ ∈ (P : Subgroup G)
    simpa only [mul_inv_rev, mul_assoc] using hkP
  refine ⟨c, ?_⟩
  have := (normalizer (W : Set G)).mul_mem
    ((normalizer (W : Set G)).inv_mem hkW) hkcgW
  simpa only [← mul_assoc, inv_mul_cancel, one_mul] using this


/-- Simultaneous element fusion in the centralizer of a weakly closed subgroup. -/
theorem pair_fusion
    (P : Sylow p G) (W : Subgroup G)
    (hWP : W ≤ (P : Subgroup G))
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (W : Set G))
    {x y z t : G}
    (hx : x ∈ centralizer (W : Set G)) (hy : y ∈ centralizer (W : Set G))
    (hz : z ∈ centralizer (W : Set G)) (ht : t ∈ centralizer (W : Set G))
    (g : G) (hgx : MulAut.conj g x = z) (hgy : MulAut.conj g y = t) :
    ∃ n ∈ normalizer (W : Set G), MulAut.conj n x = z ∧ MulAut.conj n y = t := by
  let C := centralizer ({z} : Set G) ⊓ centralizer ({t} : Set G)
  have hWC : W ≤ C := by
    intro w hw
    exact ⟨mem_centralizer_singleton_iff.mpr (hz w hw),
      mem_centralizer_singleton_iff.mpr (ht w hw)⟩
  have hconj : W.map (MulAut.conj g).toMonoidHom ≤ C := by
    rintro _ ⟨w,hw,rfl⟩
    constructor
    · apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (MulAut.conj g) (hx w hw).symm
      change MulAut.conj g w * z = z * MulAut.conj g w
      simp only [map_mul,hgx] at hh
      exact hh.symm
    · apply mem_centralizer_singleton_iff.mpr
      have hh := congrArg (MulAut.conj g) (hy w hw).symm
      change MulAut.conj g w * t = t * MulAut.conj g w
      simp only [map_mul,hgy] at hh
      exact hh.symm
  obtain ⟨c,hc⟩ := exists_normalizer_correction P W hWP hweak C hWC g hconj
  refine ⟨c.val * g,hc,?_,?_⟩
  · change (c.val * g) * x * (c.val * g)⁻¹ = z
    calc
      _ = c.val * (g * x * g⁻¹) * c.val⁻¹ := by group
      _ = z := by
        change c.val * MulAut.conj g x * c.val⁻¹ = z
        rw [hgx]
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property.1)
  · change (c.val * g) * y * (c.val * g)⁻¹ = t
    calc
      _ = c.val * (g * y * g⁻¹) * c.val⁻¹ := by group
      _ = t := by
        change c.val * MulAut.conj g y * c.val⁻¹ = t
        rw [hgy]
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp c.property.2)
end Sylow.PointwiseFusion
