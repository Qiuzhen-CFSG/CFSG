module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Normality
/-!
# Small actions in the moving-symmetry argument

For a finite group with the genuine simple SL₃(2) quotient and a two-group
kernel, its two-residual fixes any set of at most four points. Otherwise
the permutation image would have a section of order 168, although its
order is at most 24. This also controls normal subgroup sections of order
at most four, without assuming that an arbitrary subgroup of that index
is normal.

The fixed-factor lemma removes a small natural component from a normal
subgroup of a fixed/moving product. These are the two local algebra steps
in MS93 (4.3.7)(ii), printed p.888.
-/

public section

open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving.Symmetry

/-- The two-residual fixes every point of a set of size at most four. -/
theorem residual_le_small_action_kernel {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    {A : Type*} [Finite A] (f : G →* Equiv.Perm A) (hA : Nat.card A ≤ 4) :
    pResidual 2 G ≤ f.ker := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  have hn : (f.ker.map π).Normal := f.normal_ker.map π hπ
  have hm : f.ker.map π = ⊤ := by
    rcases hn.eq_bot_or_eq_top with h | h
    · have hk : f.ker ≤ π.ker := (Subgroup.map_eq_bot_iff _).mp h
      have hdiv := index_dvd_of_le hk
      have hpi : π.ker.index = 168 := by
        rw [index_ker, MonoidHom.range_eq_top.mpr hπ,
          Nat.card_congr topEquiv.toEquiv, Atlas.Comparisons.Exceptional.sl3Two_card]
      have hle : f.ker.index ≤ 24 := by
        rw [index_ker]
        calc
          Nat.card f.range ≤ Nat.card (Equiv.Perm A) := card_le_card_group _
          _ = (Nat.card A).factorial := Nat.card_perm
          _ ≤ (4 : ℕ).factorial := Nat.factorial_le hA
          _ = 24 := rfl
      have hpos := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := f.ker))
      rw [hpi] at hdiv
      have := Nat.le_of_dvd hpos hdiv
      omega
    · exact h
  have hsup : f.ker ⊔ π.ker = ⊤ := by
    rw [← comap_map_eq, hm, comap_top]
  exact sInf_le ⟨f.normal_ker, isPGroup_quotient_of_sup_eq_top f.ker π.ker hp hsup⟩

/-- A small normal subgroup is centralized by the two-residual. -/
theorem small_normal_centralizes_residual {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    (A : Subgroup G) [A.Normal] (hA : Nat.card A ≤ 4) :
    ⁅A, pResidual 2 G⁆ = ⊥ := by
  let f : G →* Equiv.Perm A :=
    (MulAction.toPermHom (MulAut A) A).comp MulAut.conjNormal
  have hker := residual_le_small_action_kernel π hπ hp f hA
  rw [commutator_comm]
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro g hg a ha
  have he := congrArg (fun e : Equiv.Perm A => (e ⟨a, ha⟩ : G)) (hker hg)
  change g * a * g⁻¹ = a at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The same small-action bound for an actual normal section of the kernel. -/
theorem small_normal_section_residual {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    (Q N : Subgroup G) [Q.Normal] [N.Normal] (hNQ : N ≤ Q) (hQ : Q ≤ π.ker)
    (hsmall : N.relIndex Q ≤ 4) : ⁅Q, pResidual 2 G⁆ ≤ N := by
  let q := QuotientGroup.mk' N
  let π' := QuotientGroup.lift N π (hNQ.trans hQ)
  have hs : Function.Surjective π' := by
    intro x
    obtain ⟨g, rfl⟩ := hπ x
    exact ⟨q g, rfl⟩
  have hk : π'.ker = π.ker.map q := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    change g ∈ π.ker ↔ g ∈ (π.ker.map q).comap q
    rw [comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left (hNQ.trans hQ)]
  have hp' : IsPGroup 2 π'.ker := hk ▸ hp.map q
  have hcard : Nat.card (Q.map q) ≤ 4 := by
    rw [← relIndex_ker, QuotientGroup.ker_mk']
    exact hsmall
  have hz := small_normal_centralizes_residual π' hs hp' (Q.map q) hcard
  rw [← map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective N),
    ← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hz
  exact hz
/-- A normal subgroup in a fixed factor times a small moving subgroup
lies in the fixed factor when the moving group has no residual-fixed points. -/
theorem le_fixed_factor_of_normal {G : Type*} [Group G] [Finite G]
    (π : G →* SL) (hπ : Function.Surjective π) (hp : IsPGroup 2 π.ker)
    (K H U E : Subgroup G) [K.Normal] [H.Normal] [U.Normal]
    (hHU : H ≤ centralizer (pResidual 2 G : Set G))
    (hU : U ⊓ centralizer (pResidual 2 G : Set G) = ⊥)
    (hEU : E ≤ U) (hE : Nat.card E ≤ 4) (hK : K ≤ H ⊔ E) : K ≤ H := by
  let N := (K ⊔ H) ⊓ U
  have hNE : N ≤ E := by
    rintro x ⟨hx, hxU⟩
    have hprod : x ∈ H ⊔ E := (sup_le hK le_sup_left) hx
    obtain ⟨h, hh, e, he, rfl⟩ := mem_sup_of_normal_left.mp hprod
    have hhU : h ∈ U := by
      simpa only [mul_inv_cancel_right] using U.mul_mem hxU (U.inv_mem (hEU he))
    have hh1 : h = 1 := hU.le ⟨hhU, hHU hh⟩
    simpa only [hh1, one_mul] using he
  have hcard : Nat.card N ≤ 4 := (card_le_of_le hNE).trans hE
  have hNC := commutator_eq_bot_iff_le_centralizer.mp
    (small_normal_centralizes_residual π hπ hp N hcard)
  have hN : N = ⊥ := le_bot_iff.mp (hU ▸ le_inf inf_le_right hNC)
  intro x hx
  obtain ⟨h, hh, e, he, rfl⟩ := mem_sup_of_normal_left.mp (hK hx)
  have heN : e ∈ N := by
    refine ⟨?_, hEU he⟩
    have hm := (K ⊔ H).mul_mem ((K ⊔ H).inv_mem (mem_sup_right hh)) (mem_sup_left hx)
    change e ∈ K ⊔ H
    simpa only [inv_mul_cancel_left] using hm
  have he1 : e = 1 := hN.le heN
  simpa only [he1, mul_one] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward.Moving.Symmetry
