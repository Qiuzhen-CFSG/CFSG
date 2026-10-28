module
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.PCoreSurjective
public import Mathlib.GroupTheory.IndexNormal
public import Theory.GroupTheory.TwoLayerCentralizer
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.SpecificGroups.KleinFourAut
/-!
# Lifting the normal cubic image

The kernel of the action on a normal four-group and the radical modulo that
four-group lies in the radical. The cubic image in the six-element
automorphism group is normal, so the original subgroup is normal modulo
the radical. Source: Aschbacher–Smith C.5.13, printed p.162.
-/
public section
open Subgroup Theory.GroupTheory
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]
/-- A cubic subgroup fixing the radical modulo a normal four-group is
normal modulo the radical, by the faithful two-layer action. -/
theorem cubic_join_core_normal (K U : Subgroup G) [U.Normal]
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hcomm : ⁅K,pCore 2 G⁆ ≤ U)
    (himage : Nat.card (K.map (MulAut.conjNormal : G →* MulAut U)) = 3) :
    (K ⊔ pCore 2 G).Normal := by
  let Q := pCore 2 G
  let D := commutatorPreimage ⊤ Q U
  let f : G →* MulAut U := MulAut.conjNormal
  have hKD : K ≤ D := le_commutatorPreimage le_top hcomm
  have hDN : (D : Subgroup G).Normal := normalizer_eq_top_iff.mp
    (top_le_iff.mp (commutatorPreimage_normalized ⊤ Q U ⊤
      le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
      le_normalizer_of_normal))
  let : D.Normal := hDN
  have hquot : pCore 2 (G ⧸ Q) = ⊥ := by
    let q := QuotientGroup.mk' Q
    have hk : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
    have he := q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective Q) hk
    have hm := congrArg (Subgroup.map q) he
    rw [map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q)] at hm
    exact hm.trans ((Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']))
  have hfix : f.ker ⊓ D ≤ Q := by
    rw [show f.ker = centralizer (U : Set G) from MulAut.conjNormal_ker_eq_centralizer U]
    exact two_layer_le_radical Q U Q (IsElementaryAbelian.isPGroup 2 U)
      hquot (inf_le_right.trans hself)
  let : Nontrivial U := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour U := ⟨hU,IsElementaryAbelian.exponent_eq_prime⟩
  have hi : (K.map f).index = 2 := by
    have hh := (K.map f).card_mul_index
    rw [IsKleinFour.card_mulAut U,himage] at hh
    omega
  let : (K.map f).Normal := normal_of_index_eq_two hi
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  apply le_normalizer_iff.mpr
  intro g _ a ha
  have hKconj : ∀ k ∈ K, g*k*g⁻¹ ∈ K ⊔ Q := by
    intro k hk
    have him : f (g*k*g⁻¹) ∈ K.map f := by
      rw [map_mul,map_mul,map_inv]
      exact (inferInstance : (K.map f).Normal).conj_mem _ (mem_map_of_mem f hk) _
    obtain ⟨l,hl,hel⟩ := him
    have hd : g*k*g⁻¹ / l ∈ Q := hfix ⟨by
      apply MonoidHom.mem_ker.mpr
      rw [map_div,hel,div_self'],D.div_mem
        ((inferInstance : D.Normal).conj_mem k (hKD hk) g) (hKD hl)⟩
    have hm := (K ⊔ Q).mul_mem ((show Q ≤ K ⊔ Q from le_sup_right) hd)
      ((show K ≤ K ⊔ Q from le_sup_left) hl)
    simpa only [div_mul_cancel] using hm
  have hmap : (K ⊔ Q).map (MulAut.conj g).toMonoidHom ≤ K ⊔ Q := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨k,hk,rfl⟩
      exact hKconj k hk
    · rintro _ ⟨q,hq,rfl⟩
      exact (show Q ≤ K ⊔ Q from le_sup_right) ((inferInstance : Q.Normal).conj_mem q hq g)
  exact hmap (mem_map_of_mem (MulAut.conj g).toMonoidHom ha)
end Theory.GroupTheory
