module
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.Algebra.Group.Subgroup.Pointwise
/-!
# Removing a normalized commutator supplement in a nilpotent group

Let W,H,Q lie in a nilpotent ambient subgroup T. If Q normalizes H and
W is contained in H[W,Q], then W is contained in H. No normality of H in W,
and no normality of W in T, is assumed. A finite p-group wrapper takes
T=WQ when Q normalizes W and both factors are p-groups.

Inductively W is contained in H joined with the n-th lower central subgroup
of T. That join is a product because H normalizes the lower central series.
For w=h*l, the identity [h*l,q]=h[l,q]h⁻¹[h,q] puts its commutator in H
joined with the next central subgroup: [h,q] lies in H by normalization.
Nilpotence makes the final lower central subgroup trivial.

This elementary saturation is used in the contained-center branch of
Stellmacher (9.10), printed p.59, to pass from Wsource=Wlambda[Wsource,Q]C
to Wsource=WlambdaC. It does not form a quotient by the possibly nonnormal
neighborhood subgroup. The statement and proof are independent of that
campaign and its graph hypotheses.
-/

namespace Subgroup
open scoped commutatorElement Pointwise

public theorem le_of_le_sup_commutator_of_isNilpotent
    {G : Type*} [Group G] (T W H Q : Subgroup G)
    (hT : Group.IsNilpotent T) (hWT : W≤T) (hHT : H≤T) (hQT : Q≤T)
    (hQH : Q≤normalizer (H:Set G)) (hcover : W≤H⊔⁅W,Q⁆) : W≤H := by
  obtain ⟨n,hn⟩ := (isNilpotent_iff_lowerCentralSeries T).mp hT
  have hseries : ∀ n, W≤H⊔T.lowerCentralSeries n := by
    intro n
    induction n with
    | zero => exact hWT.trans le_sup_right
    | succ n ih =>
      apply hcover.trans
      apply sup_le le_sup_left
      apply commutator_le.mpr
      intro w hw q hq
      have hwProduct : w∈(H:Set G)*(T.lowerCentralSeries n:Set G) := by
        rw [←coe_mul_of_left_le_normalizer_right H (T.lowerCentralSeries n)
          (hHT.trans (T.self_le_normalizer_lowerCentralSeries n))]
        exact ih hw
      obtain ⟨h,hh,l,hl,rfl⟩ := hwProduct
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hlq : ⁅l,q⁆∈T.lowerCentralSeries (n+1) :=
        commutator_mem_commutator hl (hQT hq)
      have hconj : h*⁅l,q⁆*h⁻¹∈T.lowerCentralSeries (n+1) :=
        le_normalizer_iff.mp (hHT.trans (T.self_le_normalizer_lowerCentralSeries (n+1)))
          h hh _ hlq
      have hhq : ⁅h,q⁆∈H := (le_normalizer_iff_commutator_le_left.mp hQH)
        (commutator_mem_commutator hh hq)
      exact (H⊔T.lowerCentralSeries (n+1)).mul_mem
        (mem_sup_right hconj) (mem_sup_left hhq)
  simpa only [hn,sup_bot_eq] using hseries n

end Subgroup

namespace Subgroup
public theorem le_of_le_sup_commutator_of_isPGroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (W H Q : Subgroup G) (hW : IsPGroup p W) (hQ : IsPGroup p Q)
    (hHW : H≤W) (hQW : Q≤normalizer (W:Set G))
    (hQH : Q≤normalizer (H:Set G)) (hcover : W≤H⊔⁅W,Q⁆) : W≤H :=
  le_of_le_sup_commutator_of_isNilpotent (W⊔Q) W H Q
    (hW.to_sup_of_normal_left' hQ hQW).isNilpotent le_sup_left
      (hHW.trans le_sup_left) le_sup_right hQH hcover
end Subgroup
