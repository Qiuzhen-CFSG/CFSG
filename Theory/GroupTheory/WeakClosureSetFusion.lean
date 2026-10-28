module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Burnside fusion for subsets normalized by a weakly closed subgroup

Let W be weakly closed in a Sylow p-subgroup P of a finite group. If two
subsets normalized by W are conjugate in G, they are conjugate under N_G(W).
In particular, this normalizer controls element fusion in the whole C_G(W).
There is no centrality assumption on W inside P.

If g carries X to Y, both W and gWg⁻¹ lie in N_G(Y). Sylow conjugacy inside
that normalizer, followed by an ambient conjugation into P, lets weak closure
correct g by an element of N_G(Y) to an element of N_G(W). The correction
preserves the target subset. Singleton subsets give the element-fusion clause.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, A.1.35, printed p.30 (Burnside's Fusion Lemma).
-/

public section

open Subgroup

namespace Sylow

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

/-- Burnside fusion for arbitrary subsets normalized by a weakly closed subgroup. -/
theorem weakly_closed_normalizer_controls_set_fusion
    (P : Sylow p G) (W : Subgroup G)
    (hWP : W ≤ (P : Subgroup G))
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (W : Set G))
    (X Y : Set G) (hX : W ≤ normalizer X) (hY : W ≤ normalizer Y)
    (g : G) (hXY : MulAut.conj g '' X = Y) :
    ∃ n ∈ normalizer (W : Set G), MulAut.conj n '' X = Y := by
  have hgW : W.map (MulAut.conj g).toMonoidHom ≤ normalizer Y := by
    rintro _ ⟨w, hw, rfl⟩
    apply mem_normalizer_iff_conj_image_eq.mpr
    change MulAut.conj (MulAut.conj g w) '' Y = Y
    rw [← hXY]
    have he : (MulAut.conj (MulAut.conj g w)) ∘ MulAut.conj g =
        MulAut.conj g ∘ MulAut.conj w := by
      funext x
      simp only [Function.comp_apply, MulAut.conj_apply]
      group
    calc
      _ = (MulAut.conj g ∘ MulAut.conj w) '' X := by
        simpa only [Set.image_image, Function.comp_def] using congrArg (· '' X) he
      _ = MulAut.conj g '' (MulAut.conj w '' X) :=
        (Set.image_image (MulAut.conj g) (MulAut.conj w) X).symm
      _ = MulAut.conj g '' X := by
        rw [mem_normalizer_iff_conj_image_eq.mp (hX hw)]
  obtain ⟨c, hc⟩ := P.exists_normalizer_correction W hWP hweak
    (normalizer Y) hY g hgW
  refine ⟨(c : G) * g, hc, ?_⟩
  have he : (MulAut.conj ((c : G) * g) : G → G) = MulAut.conj (c : G) ∘ MulAut.conj g := by
    funext x
    simp only [Function.comp_apply, MulAut.conj_apply]
    group
  calc
    _ = MulAut.conj (c : G) '' (MulAut.conj g '' X) := by
      rw [he, Set.image_image]
      rfl
    _ = Y := by rw [hXY, mem_normalizer_iff_conj_image_eq.mp c.property]

/-- The normalizer controls element fusion in the ambient centralizer of W. -/
theorem weakly_closed_normalizer_controls_centralizer_fusion
    (P : Sylow p G) (W : Subgroup G)
    (hWP : W ≤ (P : Subgroup G))
    (hweak : ∀ g : G, W.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) →
      g ∈ normalizer (W : Set G))
    {x y : G} (hx : x ∈ centralizer (W : Set G))
    (hy : y ∈ centralizer (W : Set G)) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (W : Set G), n * x * n⁻¹ = y := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hxy
  have hnorm {a : G} (ha : a ∈ centralizer (W : Set G)) :
      W ≤ normalizer ({a} : Set G) := by
    rw [normalizer_singleton]
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (ha w hw)
  obtain ⟨n, hn, h⟩ := P.weakly_closed_normalizer_controls_set_fusion W hWP hweak
    {x} {y} (hnorm hx) (hnorm hy) g (by simpa using hg)
  exact ⟨n, hn, by simpa using h⟩

end Sylow