module

public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.PGroup.OmegaCenterDetection
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# The two centers in the rank-two case

The point misses the intersection of the two centers by 12.8.8(3) and
12.8.9(7). Since the center of I₂ is normalized by T, the normal-subgroup
fixed-point argument then makes it trivial when Ω₁(Z(T)) = V₁. Both centers
normalize each other, so their commutator also vanishes.

These prove the center and commutator assertions of 12.8.13(3) from the
specified earlier source clauses. The setup owner supplies the rank-two
omega equality and U ≤ T; the parabolic owner supplies normalization of I₂,
12.8.9(7), and 12.8.10(2). No conclusion of 12.8.13 is an input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
printed pp.852–855, especially Lemma 12.8.13(3).
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

public theorem point_inf_centers_eq_bot (F : InvariantFlag T V n) (g : G)
    (hg : g ∈ normalizer (V : Set G)) (hVC : V ⊓ F.ZU = F.Vi 1)
    (hdis : conjugate (F.Vi 1) g ⊓ F.ZU = ⊥) :
    F.Vi 1 ⊓ (F.ZU ⊓ conjugate F.ZU g) = ⊥ := by
  have hpZ : F.Vi 1 ≤ F.ZU := hVC ▸ inf_le_right
  have hmap : conjugate V g = V :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (V : Set G)).inv_mem hg)
  have hmeet : V ⊓ conjugate F.ZU g = conjugate (F.Vi 1) g := by
    rw [← hVC]
    simp only [conjugate]
    rw [map_inf V F.ZU (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective]
    change V ⊓ conjugate F.ZU g = conjugate V g ⊓ conjugate F.ZU g
    rw [hmap]
  apply le_bot_iff.mp
  rw [← hdis]
  exact le_inf ((le_inf (inf_le_left.trans (F.le_seed 1))
    (inf_le_right.trans inf_le_right)).trans hmeet.le) (inf_le_left.trans hpZ)

public theorem centers_commutator_le (F : InvariantFlag T V n)
    (g : G) (hg : g ∈ normalizer (V : Set G)) :
    ⁅F.ZU, conjugate F.ZU g⁆ ≤ F.ZU ⊓ conjugate F.ZU g := by
  have hZC : F.ZU ≤ centralizer (V : Set G) := by
    have hZU : F.ZU ≤ centralizer (F.U : Set G) := by
      rintro x ⟨x, hx, rfl⟩ y hy
      exact congrArg Subtype.val (mem_center_iff.mp hx ⟨y, hy⟩)
    exact hZU.trans (centralizer_le (le_conjugateSpanBy V F.H))
  have hCN : centralizer (V : Set G) ≤ normalizer (F.ZU : Set G) :=
    ((centralizer_le (F.le_seed 1)).trans (centralizer_le_normalizer _)).trans
      ((le_normalizer_conjugateSpanBy V F.H).trans
        (normalizer_le_normalizer_characteristic_image F.U (center F.U)))
  have hCg : conjugate (centralizer (V : Set G)) g = centralizer (V : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_centralizer V ((normalizer (V : Set G)).inv_mem hg))
  have hCN' : centralizer (V : Set G) ≤ normalizer (conjugate F.ZU g : Set G) := by
    rw [← hCg]
    simp only [conjugate]
    rw [← map_equiv_normalizer_eq]
    exact map_mono hCN
  exact le_inf
    ((le_normalizer_iff_commutator_le_left).mp
      ((F.conjugate_center_centralizes_seed g hg).trans hCN))
    ((le_normalizer_iff_commutator_le_right).mp (hZC.trans hCN'))

public theorem rankTwo_centers [Finite G] (F : InvariantFlag T V 2) (L : Subgroup G)
    (g : G) (hg : g ∈ normalizer (V : Set G))
    (hZ : sylowOmega T = F.Vi 1) (hUT : F.U ≤ (T : Subgroup G))
    (hI : (T : Subgroup G) ≤ normalizer (F.I₂ L : Set G))
    (hVC : V ⊓ F.ZU = F.Vi 1)
    (hdis : conjugate (F.Vi 1) g ⊓ F.ZU = ⊥)
    (hmeet : F.ZU ⊓ conjugate F.ZU g = centerIn (F.I₂ L)) :
    centerIn (F.I₂ L) = ⊥ ∧ F.ZU ⊓ conjugate F.ZU g = ⊥ ∧
      ⁅F.ZU, conjugate F.ZU g⁆ = ⊥ := by
  have hDT : centerIn (F.I₂ L) ≤ (T : Subgroup G) :=
    hmeet.ge.trans (inf_le_left.trans ((map_subtype_le (center F.U)).trans hUT))
  have hD : centerIn (F.I₂ L) = ⊥ := by
    apply Subgroup.eq_bot_of_normalized_of_omega_center_disjoint (T : Subgroup G) _
      T.isPGroup' hDT
      (hI.trans (normalizer_le_normalizer_characteristic_image (F.I₂ L) (center (F.I₂ L))))
    change sylowOmega T ⊓ centerIn (F.I₂ L) = ⊥
    rw [hZ, ← hmeet]
    exact F.point_inf_centers_eq_bot g hg hVC hdis
  refine ⟨hD, hmeet.trans hD, ?_⟩
  exact le_bot_iff.mp ((F.centers_commutator_le g hg).trans (hmeet.trans hD).le)
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
