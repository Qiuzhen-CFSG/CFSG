module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Frattini bounds inside normalizers

If H is normalized by W and R is a Sylow subgroup of H, then W lies in
the join of H with the ambient normalizer of R. Apply the ordinary
Frattini argument inside W and map back to the ambient group.

For H = Q C_G(Q), this is the factorization used in GLS2,
Proposition 22.4 (`refs/KGroup/GLS2/ChapterF.tex`).
-/

namespace Subgroup

/-- The Frattini argument in an intermediate subgroup, expressed in the
ambient group. -/
public theorem le_normalizer_sylow_sup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (H W : Subgroup G) (hHW : H ≤ W) (hWH : W ≤ normalizer (H : Set G))
    (R : Sylow p H) :
    W ≤ normalizer ((R : Subgroup H).map H.subtype : Set G) ⊔ H := by
  let H' := H.subgroupOf W
  let _ : H'.Normal := (normal_subgroupOf_iff_le_normalizer hHW).mpr hWH
  let e : H ≃* H' := (subgroupOfEquivOfLe hHW).symm
  let R' : Sylow p H' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  have hmap : ((R' : Subgroup H').map H'.subtype).map W.subtype =
      (R : Subgroup H).map H.subtype := by
    change (((R : Subgroup H).map e.toMonoidHom).map H'.subtype).map W.subtype = _
    rw [map_map, map_map]
    rfl
  have hfr := congrArg (fun K : Subgroup W => K.map W.subtype)
    R'.normalizer_sup_eq_top
  rw [map_sup, ← MonoidHom.range_eq_map, W.range_subtype, subgroupOf_map_subtype,
    inf_of_le_left hHW] at hfr
  rw [← hfr]
  apply sup_le_sup_right
  have hn := ((R' : Subgroup H').map H'.subtype).le_normalizer_map W.subtype
  rwa [hmap] at hn

/-- The subgroup Q C_G(Q) is normalized by N_G(Q). -/
public theorem normalizer_le_normalizer_sup_centralizer
    {G : Type*} [Group G] (Q : Subgroup G) :
    normalizer (Q : Set G) ≤ normalizer ((Q ⊔ centralizer (Q : Set G) : Subgroup G) : Set G) := by
  have hC : normalizer (Q : Set G) ≤ normalizer (centralizer (Q : Set G) : Set G) :=
    le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer (Q : Set G))
  exact (le_inf le_rfl hC).trans (normalizer_inf_normalizer_le_normalizer_sup Q _)

/-- Frattini reduction for Q C_G(Q). -/
public theorem normalizer_le_sylow_normalizer_sup_centralizer
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q : Subgroup G) (R : Sylow p (Q ⊔ centralizer (Q : Set G) : Subgroup G))
    (hQR : Q ≤ (R : Subgroup (Q ⊔ centralizer (Q : Set G) : Subgroup G)).map
      (Q ⊔ centralizer (Q : Set G)).subtype) :
    normalizer (Q : Set G) ≤
      normalizer ((R : Subgroup (Q ⊔ centralizer (Q : Set G) : Subgroup G)).map
        (Q ⊔ centralizer (Q : Set G)).subtype : Set G) ⊔ centralizer (Q : Set G) := by
  have h := le_normalizer_sylow_sup (Q ⊔ centralizer (Q : Set G))
    (normalizer (Q : Set G))
    (sup_le Q.le_normalizer (centralizer_le_normalizer _))
    (normalizer_le_normalizer_sup_centralizer Q) R
  refine h.trans (sup_le le_sup_left (sup_le ?_ le_sup_right))
  exact hQR.trans (le_normalizer.trans le_sup_left)

end Subgroup
