module

public import CFSG.Quasithin.Chapter12.Section08.SourceGeometry
public import Theory.GroupTheory.ConjugationLocalGeometry
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The normalizer and displaced point of the marked parabolic

This supplies the corrected conjugate-span equality and relative normality
in 12.8.9(1), and the disjointness in 12.8.9(7). The inputs are the actual
preceding-source commutator bound from 12.8.4(2), the center intersection
from 12.8.8(3), and the natural-action image on V₂. The span is taken under
G₂, as established by the printed proof: the statement's H is a typo since
H already normalizes U.

The residual supplement, two-core, natural-module and action-kernel
assertions of 12.8.9 and the center assertions of 12.8.10 are separate
obligations. Nothing here identifies I₂ with a maximal parabolic.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 12.8.9, printed pp.852–853, PDF pp.869–870.
-/

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section08
variable {G : Type*} [Group G]

public theorem conjugate_le_of_normalizes {A B : Subgroup G} (hAB : A ≤ B)
    (g : G) (hg : g ∈ normalizer (B : Set G)) : conjugate A g ≤ B := by
  rintro x ⟨a, ha, rfl⟩
  exact (mem_normalizer_iff.mp ((normalizer (B : Set G)).inv_mem hg) a).mp (hAB ha)

public theorem conjugate_eq_iff (A : Subgroup G) (g : G) :
    conjugate A g = A ↔ g ∈ normalizer (A : Set G) := by
  change A.map (MulAut.conj g⁻¹).toMonoidHom = A ↔ _
  exact (mem_normalizer_iff_map_conj_eq (H := A) (g := g⁻¹)).symm.trans inv_mem_iff

public theorem centerIn_conjugate (A : Subgroup G) (g : G) :
    centerIn (conjugate A g) = conjugate (centerIn A) g :=
  (map_embeddedCenter A (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).symm

public theorem conjugate_inf (A B : Subgroup G) (g : G) :
    conjugate (A ⊓ B) g = conjugate A g ⊓ conjugate B g :=
  map_inf A B (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

public theorem conjugate_conjugate_inv (A : Subgroup G) (g : G) :
    conjugate (conjugate A g⁻¹) g = A := by
  simp only [conjugate, inv_inv, map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  rw [he, map_id]

public theorem conjugate_centralizer_le (A : Subgroup G) (g : G)
    (hg : g ∈ normalizer (A : Set G)) :
    conjugate (centralizer (A : Set G)) g ≤ centralizer (A : Set G) := by
  have h : conjugate (centralizer (A : Set G)) g ≤ centralizer (conjugate A g : Set G) :=
    map_centralizer_le_centralizer_image _ _
  rwa [(conjugate_eq_iff A g).mpr hg] at h

namespace InvariantFlag
variable {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

public theorem U_le_G₂_of_commutator (F : InvariantFlag T V n)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) : F.U ≤ F.Gi 2 := by
  apply le_normalizer_iff_commutator_le_right.mpr
  exact (commutator_mono le_rfl ((F.le_seed 2).trans (le_conjugateSpanBy V F.H))).trans
    (hcomm.trans (F.monotone (by omega)))

public theorem I₂_eq_G₂_span (F : InvariantFlag T V n) (L : Subgroup G)
    (hPG : F.P L ≤ F.Gi 2)
    (himage : ∀ k ∈ F.Gi 2, ∃ p ∈ F.P L,
      ∀ a ∈ F.Vi 2, k * a * k⁻¹ = p * a * p⁻¹) :
    F.I₂ L = conjugateSpanBy F.U (F.Gi 2) := by
  symm
  apply conjugateSpanBy_eq_of_action_image (F.Vi 2) F.U (F.P L) (F.Gi 2) hPG
  · exact ((centralizer_le (F.monotone (by omega))).trans
      (centralizer_le_normalizer (F.Vi 1 : Set G))).trans
      (le_normalizer_conjugateSpanBy V F.H)
  · exact himage

public theorem I₂_normal_in_G₂ (F : InvariantFlag T V n) (L : Subgroup G)
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1) (hPG : F.P L ≤ F.Gi 2)
    (himage : ∀ k ∈ F.Gi 2, ∃ p ∈ F.P L,
      ∀ a ∈ F.Vi 2, k * a * k⁻¹ = p * a * p⁻¹) :
    (F.I₂ L).subgroupOf (F.Gi 2) |>.Normal := by
  rw [F.I₂_eq_G₂_span L hPG himage]
  exact (normal_subgroupOf_iff_le_normalizer
    (conjugateSpanBy_le_self (F.U_le_G₂_of_commutator hcomm))).mpr
    (le_normalizer_conjugateSpanBy F.U (F.Gi 2))

public theorem conjugate_point_inf_ZU (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hcenter : V ⊓ F.ZU = F.Vi 1) (g : G)
    (hgV : g ∈ normalizer (V : Set G)) (hgH : g ∉ F.H) :
    conjugate (F.Vi 1) g ⊓ F.ZU = ⊥ := by
  have hcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  have hc : Nat.card (conjugate (F.Vi 1) g) = 2 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hcard]
  have hne : conjugate (F.Vi 1) g ≠ F.Vi 1 := by
    intro he
    exact hgH ((conjugate_eq_iff (F.Vi 1) g).mp he)
  apply le_antisymm _ bot_le
  calc
    conjugate (F.Vi 1) g ⊓ F.ZU ≤ conjugate (F.Vi 1) g ⊓ (V ⊓ F.ZU) :=
      le_inf inf_le_left (le_inf
        (inf_le_left.trans (conjugate_le_of_normalizes (F.le_seed 1) g hgV)) inf_le_right)
    _ = ⊥ := by rw [hcenter, inf_eq_bot_of_card_two_of_ne _ _ hc hcard hne]

public theorem P_le_G₂ (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G)) : F.P L ≤ F.Gi 2 := by
  by_cases he : n = 2
  · subst n
    simpa only [Gi, F.last] using F.P_le_seed_normalizer L hL
  · intro x hx
    exact (mem_iInf.mp (mem_iInf.mp hx.2 2) ⟨le_rfl, by omega⟩)

public theorem ZU_le_W (F : InvariantFlag T V n) : F.ZU ≤ F.W := by
  apply le_inf (map_subtype_le _)
  rintro x ⟨u, hu, rfl⟩ a ha
  exact congrArg Subtype.val (mem_center_iff.mp hu
    ⟨a, (le_conjugateSpanBy V F.H) (F.le_seed 2 ha)⟩)

public theorem X_le_plane_centralizer (F : InvariantFlag T V n) (g : G)
    (hg : g ∈ F.Gi 2) : F.X g ≤ centralizer (F.Vi 2 : Set G) :=
  (map_mono (show F.W ≤ centralizer (F.Vi 2 : Set G) from inf_le_right)).trans
    (conjugate_centralizer_le (F.Vi 2) g hg)

public theorem X_le_H (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) :
    F.X g ≤ F.H :=
  (F.X_le_plane_centralizer g hg).trans ((centralizer_le (F.monotone (by omega))).trans
    (centralizer_le_normalizer _))

public theorem X_normalizes_U (F : InvariantFlag T V n) (g : G) (hg : g ∈ F.Gi 2) :
    F.X g ≤ normalizer (F.U : Set G) :=
  (F.X_le_H g hg).trans (le_normalizer_conjugateSpanBy V F.H)

public theorem conjugate_ZU_le_X (F : InvariantFlag T V n) (g : G) :
    conjugate F.ZU g ≤ F.X g := map_mono F.ZU_le_W

public theorem point_inf_conjugate_ZU (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hcenter : V ⊓ F.ZU = F.Vi 1) (g : G)
    (hgV : g ∈ normalizer (V : Set G)) (hgH : g ∉ F.H) :
    F.Vi 1 ⊓ conjugate F.ZU g = ⊥ := by
  have h := F.conjugate_point_inf_ZU hn hcenter g⁻¹
    ((normalizer (V : Set G)).inv_mem hgV) (fun hh => hgH (F.H.inv_mem_iff.mp hh))
  have he := congrArg (fun A : Subgroup G => conjugate A g) h
  rw [conjugate_inf, conjugate_conjugate_inv] at he
  simpa only [conjugate, Subgroup.map_bot] using he

public theorem parabolic_displaced_centers (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcenter : V ⊓ F.ZU = F.Vi 1) (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H) :
    conjugate (F.Vi 1) g ⊓ F.ZU = ⊥ ∧
    F.Vi 1 ⊓ conjugate F.ZU g = ⊥ ∧
    conjugate F.ZU g ≤ F.X g ∧ F.X g ≤ F.H ∧
    F.X g ≤ normalizer (F.U : Set G) := by
  have hgV := F.P_le_seed_normalizer L hL hgP
  have hgG := F.P_le_G₂ hn L hL hgP
  exact ⟨F.conjugate_point_inf_ZU (by omega) hcenter g hgV hgH,
    F.point_inf_conjugate_ZU (by omega) hcenter g hgV hgH,
    F.conjugate_ZU_le_X g, F.X_le_H g hgG, F.X_normalizes_U g hgG⟩

public theorem U_sup_conjugate_le_I₂ (F : InvariantFlag T V n) (L : Subgroup G)
    (g : G) (hg : g ∈ F.P L) : F.U ⊔ conjugate F.U g ≤ F.I₂ L := by
  apply sup_le (le_conjugateSpanBy _ _)
  rintro x ⟨u, hu, rfl⟩
  exact subset_closure ⟨g⁻¹, (F.P L).inv_mem hg, u, hu, by simp⟩

public theorem parabolic_span_normality (F : InvariantFlag T V n) (hn : 2 ≤ n)
    (L : Subgroup G) (hL : L ≤ normalizer (V : Set G))
    (hcomm : ⁅F.U, F.U⁆ ≤ F.Vi 1)
    (himage : ∀ k ∈ F.Gi 2, ∃ p ∈ F.P L,
      ∀ a ∈ F.Vi 2, k * a * k⁻¹ = p * a * p⁻¹) :
    F.I₂ L = conjugateSpanBy F.U (F.Gi 2) ∧
    F.I₂ L ≤ F.Gi 2 ∧ ((F.I₂ L).subgroupOf (F.Gi 2)).Normal := by
  have hPG := F.P_le_G₂ hn L hL
  refine ⟨F.I₂_eq_G₂_span L hPG himage, ?_, F.I₂_normal_in_G₂ L hcomm hPG himage⟩
  rw [F.I₂_eq_G₂_span L hPG himage]
  exact conjugateSpanBy_le_self (F.U_le_G₂_of_commutator hcomm)

end InvariantFlag
end CFSG.Quasithin.Chapter12.Section08
