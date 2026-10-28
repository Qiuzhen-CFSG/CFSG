module

public import Theory.GroupTheory.WeakClosureSetFusion
public import Stellmacher.ElementaryAbelianMaxNormalizerAction

/-!
# Weak closure from the elementary Thompson normalizer

If all maximum elementary subgroups are normalized by J(T), the Burnside
fusion lemma and N(J(T))=T make every T-normal member weakly closed. A second
application controls its element fusion in its own normalizer. This is the
ambient argument in Aschbacher–Smith 13.9.2(3–5).
-/

public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Subgroup

namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

theorem maxJ_weakly_closed_normalizer (T : Sylow 2 G) (g : G)
    (hg : (elementaryAbelianMaxJ (T : Subgroup G)).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    g ∈ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) :=
  mem_normalizer_iff_map_conj_eq.mpr
    (elementaryAbelianMaxJ_map_eq_of_le (T : Subgroup G) (MulAut.conj g) hg)

theorem maxFamily_weakly_closed_of_normalizer_eq
    (T : Sylow 2 G)
    (hN : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) = (T : Subgroup G))
    (hnorm : ∀ E ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (E : Set G))
    (D : Subgroup G) (hD : D ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hDT : (T : Subgroup G) ≤ normalizer (D : Set G))
    (g : G) (hg : D.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    D.map (MulAut.conj g).toMonoidHom = D := by
  have hmap : D.map (MulAut.conj g).toMonoidHom ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) := by
    refine ⟨hg, hD.2.1.map _, ?_⟩
    intro E hET hE
    rw [card_map_of_injective (MulAut.conj g).injective]
    exact hD.2.2 E hET hE
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le (fun _ h => h.1)
  obtain ⟨n, hn, hconj⟩ := T.weakly_closed_normalizer_controls_set_fusion
    (elementaryAbelianMaxJ (T : Subgroup G)) hJT (maxJ_weakly_closed_normalizer T)
    (D : Set G) (D.map (MulAut.conj g).toMonoidHom : Set G)
    (hnorm D hD) (hnorm _ hmap) g rfl
  have hnT : n ∈ (T : Subgroup G) := hN ▸ hn
  have hnD := mem_normalizer_iff_conj_image_eq.mp (hDT hnT)
  exact SetLike.coe_injective (hconj.symm.trans hnD)

theorem maxFamily_element_fusion_of_weakly_closed
    (T : Sylow 2 G) (D : Subgroup G)
    (hD : D ∈ elementaryAbelianMaxSubgroups (T : Subgroup G))
    (hweak : ∀ g : G, D.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
      D.map (MulAut.conj g).toMonoidHom = D)
    {x y : G} (hx : x ∈ D) (hy : y ∈ D) (hxy : IsConj x y) :
    ∃ n ∈ normalizer (D : Set G), n * x * n⁻¹ = y := by
  let : IsElementaryAbelian 2 D := hD.2.1
  have hcentral {z : G} (hz : z ∈ D) : z ∈ centralizer (D : Set G) := by
    intro a ha
    exact congrArg Subtype.val
      ((IsElementaryAbelian.toIsMulCommutative (p := 2) (G := D)).is_comm.comm
        (⟨a, ha⟩ : D) ⟨z, hz⟩)
  exact T.weakly_closed_normalizer_controls_centralizer_fusion D hD.1
    (fun g hg => mem_normalizer_iff_map_conj_eq.mpr (hweak g hg))
    (hcentral hx) (hcentral hy) hxy

end Stellmacher
