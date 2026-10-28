module

public import Stellmacher.ElementaryAbelianMaxGlobal
public import Stellmacher.ElementaryAbelianMaxJMap
public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CharacteristicNormalizerClosure

/-!
# Frattini generation by the elementary Thompson subgroup

Intersect a Sylow two-subgroup S with the normal subgroup J(G).
The intersection contains J(S), hence has the same Thompson subgroup.
The Sylow Frattini argument consequently gives G = J(G) N_G(J(S)).
If J(S) is nontrivial and J(S) ≤ B ≤ S, then J(S) = J(B) is
characteristic in B, so its normalizer belongs to C(G,B).

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
the Frattini argument in 15.3.11(11), printed p.1124.
-/

public section
namespace Stellmacher
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A subgroup between J(S) and S has the same elementary Thompson subgroup. -/
theorem elementaryAbelianMaxJ_eq_of_intermediate (S B : Subgroup G)
    (hJB : elementaryAbelianMaxJ S ≤ B) (hBS : B ≤ S) :
    elementaryAbelianMaxJ B = elementaryAbelianMaxJ S := by
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq B S hBS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le S B hJB
  have he := le_antisymm hsmall.1 hlarge.1
  exact le_antisymm (hsmall.2 he) (hlarge.2 he.symm)

/-- The elementary Thompson form of the Sylow Frattini argument. -/
theorem elementaryAbelianMaxJ_frattini (S : Sylow 2 G) :
    normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G) ⊔
      elementaryAbelianMaxJ (⊤ : Subgroup G) = ⊤ := by
  let J := elementaryAbelianMaxJ (⊤ : Subgroup G)
  let : J.Characteristic := elementaryAbelianMaxJ_top_characteristic
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal J
  let R := (P : Subgroup J).map J.subtype
  have hR : R = (S : Subgroup G) ⊓ J := by
    rw [show R = (P : Subgroup J).map J.subtype from rfl, hP, subgroupOf_map_subtype]
  have hJR : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (S : Subgroup G) :=
    elementaryAbelianMaxJ_eq_of_intermediate _ _
      (hR ▸ le_inf (sSup_le fun _ hA => hA.1) (elementaryAbelianMaxJ_sylow_le_top S))
      (hR ▸ inf_le_left)
  have hN : normalizer (R : Set G) ≤
      normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq] at hg ⊢
    change R.map (MulAut.conj g).toMonoidHom = R at hg
    change (elementaryAbelianMaxJ (S : Subgroup G)).map (MulAut.conj g).toMonoidHom = _
    rw [← hJR, ← elementaryAbelianMaxJ_map_equiv, hg]
  exact top_unique (P.normalizer_sup_eq_top.symm.le.trans (sup_le_sup_right hN J))

/-- Characteristic-normalizer generation controls the normalizer of J(S)
whenever the intermediate subgroup B contains the nontrivial J(S). -/
theorem normalizer_maxJ_le_characteristicNormalizerClosure (S B : Subgroup G)
    (hJB : elementaryAbelianMaxJ S ≤ B) (hBS : B ≤ S)
    (hne : elementaryAbelianMaxJ S ≠ ⊥) :
    normalizer (elementaryAbelianMaxJ S : Set G) ≤ B.characteristicNormalizerClosure := by
  let D := elementaryAbelianMaxJ (⊤ : Subgroup B)
  let : D.Characteristic := elementaryAbelianMaxJ_top_characteristic
  have hmap : D.map B.subtype = elementaryAbelianMaxJ S := by
    rw [← elementaryAbelianMaxJ_map_injective B.subtype B.subtype_injective,
      ← MonoidHom.range_eq_map, range_subtype]
    exact elementaryAbelianMaxJ_eq_of_intermediate S B hJB hBS
  have hD : D ≠ ⊥ := by
    intro he
    apply hne
    rw [← hmap, he, Subgroup.map_bot]
  rw [← hmap]
  exact normalizer_le_characteristicNormalizerClosure B D hD

end Stellmacher
end
