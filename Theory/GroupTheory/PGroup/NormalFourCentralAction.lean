module

public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing
public import Theory.GroupTheory.PGroup.NormalFourAbelianBase
public import Theory.ElementaryAbelian.Join

/-!
# Central involution actions above a normal four

Let D be a normal self-centralizing abelian subgroup with omega subgroup W
of order four. Suppose an involution x outside D centralizes W and its action
on D commutes with the whole conjugation image. If every element of D inverted
by x has square one, then W together with x is a normal elementary subgroup
of order at least eight.

Indeed, every conjugation difference of x lies in the conjugation kernel D.
Since x and its conjugates are involutions, x inverts these differences; hence
they belong to W. This makes the elementary join normal. Unlike the central
omega version, W need only be normal, and need not lie in the group center.

This is the local obstruction used in investigating the maximal C₄-square
extension in Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386.
-/

namespace Subgroup

/-- A central involution action whose inverted elements are binary produces a
normal elementary eight above the omega four. -/
public theorem exists_normal_eight_of_involution_central_action
    {P : Type*} [Group P] [Finite P]
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (x : P) (hx : x ^ 2 = 1) (hxD : x ∉ D)
    (hxW : x ∈ centralizer (W : Set P))
    (hcomm : ∀ g : P, Commute (MulAut.conjNormal (H := D) g)
      (MulAut.conjNormal (H := D) x))
    (hinv : ∀ d ∈ D, x * d * x⁻¹ = d⁻¹ → d ^ 2 = 1) :
    ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E := by
  let : IsElementaryAbelian 2 (zpowers x) := IsElementaryAbelian.zpowers_of_pow_eq_one hx
  let U := W ⊔ zpowers x
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.sup_of_le_centralizer
    (zpowers_le.mpr hxW)
  have hdiff (g : P) : g * x * g⁻¹ * x⁻¹ ∈ W := by
    let d := g * x * g⁻¹ * x⁻¹
    let f : P →* MulAut D := MulAut.conjNormal
    have hk : d ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      dsimp [d, f]
      simp only [map_mul, map_inv]
      rw [(hcomm g).eq]
      group
    have hd : d ∈ D := by
      rwa [conjNormal_ker_eq_of_selfCentralizing_abelian D hDC] at hk
    have hde : (d * x) ^ 2 = 1 := by
      change (g * x * g⁻¹ * x⁻¹ * x) ^ 2 = 1
      rw [inv_mul_cancel_right, ← MulAut.conj_apply, ← map_pow, hx, map_one]
    have hdi : x * d * x⁻¹ = d⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      calc
        d * (x * d * x⁻¹) = (d * x) ^ 2 * (x ^ 2)⁻¹ := by
          simp only [pow_two]
          group
        _ = 1 := by rw [hde, hx]; simp
    rw [← hO]
    refine ⟨⟨d, hd⟩, subset_closure ?_, rfl⟩
    change (⟨d, hd⟩ : D) ^ (2 ^ 1) = 1
    apply Subtype.ext
    simpa using hinv d hd hdi
  let : U.Normal := by
    constructor
    intro y hy g
    have hmap : U.map (MulAut.conj g).toMonoidHom ≤ U := by
      rw [show U = W ⊔ zpowers x from rfl, map_sup, MonoidHom.map_zpowers]
      apply sup_le
      · rintro _ ⟨w, hw, rfl⟩
        exact (le_sup_left : W ≤ U) (Subgroup.Normal.conj_mem ‹W.Normal› w hw g)
      · apply zpowers_le.mpr
        have hh : MulAut.conj g x = (g * x * g⁻¹ * x⁻¹) * x := by
          simp [MulAut.conj_apply]
        change MulAut.conj g x ∈ U
        rw [hh]
        exact U.mul_mem ((le_sup_left : W ≤ U) (hdiff g))
          ((le_sup_right : zpowers x ≤ U) (mem_zpowers x))
    exact hmap (mem_map_of_mem _ hy)
  refine ⟨U, inferInstance, inferInstance, ?_⟩
  have hdiv : 4 ∣ Nat.card U := hW ▸ card_dvd_of_le (show W ≤ U from le_sup_left)
  have hle : Nat.card W ≤ Nat.card U := card_le_of_le le_sup_left
  have hne : Nat.card U ≠ 4 := by
    intro hc
    have heq : W = U := eq_of_le_of_card_ge le_sup_left (by omega)
    have hxU : x ∈ U := (le_sup_right : zpowers x ≤ U) (mem_zpowers x)
    have hxW : x ∈ W := heq ▸ hxU
    exact hxD (map_subtype_le _ (hO ▸ hxW))
  omega

end Subgroup
