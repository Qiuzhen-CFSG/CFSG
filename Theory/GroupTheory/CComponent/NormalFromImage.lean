module
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Detecting normality of a C-component from an action image

An action killing the solvable radical cannot identify two distinct
nonabelian component images: distinct components commute modulo that
radical. Thus a C-component with nonabelian normal action image is itself
normal. The action kernel need not be solvable.

Source application: Aschbacher–Smith 13.3.2(2), in the original marked
A₅ module case used by 13.5.7. Here the image lies between A₅ and S₅.
-/

public section
namespace Subgroup
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- A nonabelian normal action image detects normality of its original
C-component when the ambient solvable radical acts trivially. -/
theorem IsCComponent.normal_of_normal_nonabelian_image
    {L : Subgroup G} (hL : L.IsCComponent) (f : G →* Q)
    (hR : solvableRadical G ≤ f.ker) (hn : (L.map f).Normal)
    (hna : ¬ IsMulCommutative (L.map f)) : L.Normal := by
  let R := solvableRadical G
  let q := QuotientGroup.mk' R
  let fbar := QuotientGroup.lift R f hR
  have hf : fbar.comp q = f := by ext x; rfl
  let := hn
  apply normal_iff_map_conj_eq.mpr
  intro g
  by_contra hne
  have hconj := hL.map_equiv (MulAut.conj g)
  have hneq : L.map q ≠ (L.map (MulAut.conj g).toMonoidHom).map q := by
    intro he
    exact hne (hconj.eq_of_map_quotient_eq hL R he.symm)
  have hq := (hL.map_quotient R).commutator_eq_bot_of_ne_of_solvableRadical_eq_bot
    (solvableRadical_quotient_solvableRadical (G := G)) (hconj.map_quotient R) hneq
  have himage : (L.map (MulAut.conj g).toMonoidHom).map f = L.map f := by
    have hmap : (L.map (MulAut.conj g).toMonoidHom).map f =
        (L.map f).map (MulAut.conj (f g)).toMonoidHom := by
      rw [map_map,map_map]
      congr 1
      ext x
      simp
    rw [hmap]
    apply mem_normalizer_iff_map_conj_eq.mp
    rw [normalizer_eq_top]
    exact mem_top _
  have hc : (⁅L,L.map (MulAut.conj g).toMonoidHom⁆ : Subgroup G).map f = ⊥ := by
    rw [← hf,← map_map,map_commutator,hq,map_bot]
  rw [map_commutator,himage] at hc
  exact hna (commutator_self_eq_bot_iff.mp hc)
end Subgroup
