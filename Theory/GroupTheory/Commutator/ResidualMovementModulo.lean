module
public import Theory.GroupTheory.Commutator.CentralizingComplement
public import Theory.GroupTheory.Commutator.NilpotentSaturation

/-!
# Removing a p-group supplement from full movement

Let A be a normal finite p-subgroup and let the ambient group be L R, with
R a p-group and L normal. If A is fully moved by the ambient group modulo
a normal layer Z, then it is fully moved by L modulo Z. Pass to the quotient
by [A,L]Z; L centralizes the image of A, so its full movement is already
movement by R. Nilpotence of the p-group A R kills that image.
This supplies the residual-movement step in MS93 (3.6), printed p.871.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem normal_p_subgroup_moved_modulo_supplement
    {p : ℕ} [Fact p.Prime] (A L R Z : Subgroup G)
    [A.Normal] [L.Normal] [Z.Normal]
    (hA : IsPGroup p A) (hR : IsPGroup p R) (hgen : L ⊔ R = ⊤)
    (hmove : A ≤ ⁅A,⊤⁆ ⊔ Z) :
    A ≤ ⁅A,L⁆ ⊔ Z := by
  let K := ⁅A,L⁆ ⊔ Z
  let q := QuotientGroup.mk' K
  let V := A.map q
  let P := R.map q
  have hqker : q.ker = K := QuotientGroup.ker_mk' K
  have hVL : ⁅V,L.map q⁆ = ⊥ := by
    rw [←map_commutator]
    apply (map_eq_bot_iff _).mpr
    rw [hqker]
    exact le_sup_left
  have hgenq : L.map q ⊔ P = ⊤ := by
    rw [←map_sup,hgen,←MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)
  have hcomm : ⁅V,P⁆ = ⁅V,⊤⁆ :=
    commutator_eq_of_centralizing_sup hgenq
      (commutator_eq_bot_iff_le_centralizer.mp ((commutator_comm (L.map q) V).trans hVL))
      le_normalizer_of_normal
  have hm : V ≤ ⁅V,⊤⁆ := by
    have hh := map_mono (f := q) hmove
    rw [Subgroup.map_sup,map_commutator] at hh
    have hZ : Z.map q = ⊥ := (map_eq_bot_iff _).mpr (by rw [hqker];exact le_sup_right)
    rw [hZ,sup_bot_eq,←MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective K)] at hh
    exact hh
  have hbot : V ≤ ⊥ := le_of_le_sup_commutator_of_isPGroup V ⊥ P
    (hA.map q) (hR.map q) bot_le le_normalizer_of_normal le_normalizer_of_normal
    (by simpa only [bot_sup_eq,hcomm] using hm)
  have hmap : A.map q = ⊥ := bot_unique hbot
  simpa only [hqker] using (map_eq_bot_iff _).mp hmap
end Subgroup
