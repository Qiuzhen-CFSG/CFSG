module
public import Theory.Representation.SL3.DualLiftCentralizers
public import Theory.GroupTheory.ClassTwoCommutator

/-!
# Small central quotients of a natural-center, doubled-dual group

In a group with the SL₃ natural/dual geometry, a noncentral element on a
single dual axis has a commutator row of order |F|². Split an arbitrary
element across the two elementary axes. If all its commutators lie in a
smaller subgroup, the same is true of each axis component, so both are
central. No new central elements appear after killing that subgroup.

The original nonblock application uses the root of order |F| to identify
the second center of R₂ and control its full ambient normalizer.
Source: Aschbacher--Smith, C.1.35(2), pp.137--138, and the characteristic
subgroup argument in original 4.3.14(1), pp.617--618.
-/

public section
open Subgroup
open scoped MatrixGroups commutatorElement
namespace Representation.SL3ParabolicNatural
variable {F A Q : Type*} [Field F] [Finite F] [Group A] [Group Q] [Finite Q]
  [MulDistribMulAction A Q]

private theorem first_axis_small_commutators
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hp : Function.Surjective p) (hc : p.ker = center Q)
    (he : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (N : Subgroup Q) (hN : Nat.card N < (Nat.card F)^2)
    (w : Q) (f : Module.Dual F (Fin 3 → F)) (hw : (p w).toAdd = (f,0))
    (hcomm : ∀ z : Q, ⁅w,z⁆ ∈ N) : f = 0 := by
  by_contra hf
  have hclass : _root_.commutator Q ≤ center Q := by
    rw [←hc]
    exact Abelianization.commutator_subset_ker p
  have hrow : (ClassTwo.commutatorHom hclass w).range ≤ N := by
    rintro _ ⟨z,rfl⟩
    exact hcomm z
  have hbound := Nat.card_le_card_of_injective (inclusion hrow) (inclusion_injective hrow)
  have hcard := (ClassTwo.commutatorHom hclass w).ker.index_mul_card
  rw [index_ker,ClassTwo.commutatorHom_ker,
    dual_first_axis_centralizer_card α hα p hp hc he hel w f hf hw] at hcard
  have hQ := p.ker.index_mul_card
  rw [index_ker,MonoidHom.range_eq_top.mpr hp,
    Nat.card_congr (Subgroup.topEquiv).toEquiv,hc] at hQ
  have htarget : Nat.card (Multiplicative (Module.Dual F (Fin 3 → F) ×
      Module.Dual F (Fin 3 → F))) = (Nat.card F)^6 := by
    change Nat.card (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)) = _
    rw [Nat.card_prod,Module.natCard_eq_pow_finrank (K := F),
      Subspace.dual_finrank_eq,Module.finrank_fin_fun]
    ring
  rw [htarget] at hQ
  have heq : Nat.card (ClassTwo.commutatorHom hclass w).range = (Nat.card F)^2 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < (Nat.card F)^4 * Nat.card (center Q) from Nat.mul_pos (pow_pos Nat.card_pos _) Nat.card_pos)
    calc
      _ = Nat.card Q := hcard
      _ = (Nat.card F)^6 * Nat.card (center Q) := hQ.symm
      _ = _ := by ring
  rw [heq] at hbound
  exact (not_lt_of_ge hbound) hN

/-- Killing a central subgroup smaller than a dual-axis commutator row does
not create new central elements in a natural-center/doubled-dual group. -/
theorem dual_small_central_quotient
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hp : Function.Surjective p) (hc : p.ker = center Q)
    (he : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (N : Subgroup Q) (hN : Nat.card N < (Nat.card F)^2)
    (w : Q) (hcomm : ∀ z : Q, ⁅w,z⁆ ∈ N) : w ∈ center Q := by
  let D := Module.Dual F (Fin 3 → F)
  let X := (dualDiagonal (1:F) 0).range.comap p
  let Y := (dualDiagonal (0:F) 1).range.comap p
  have hX (z : Q) : z ∈ X ↔ (p z).toAdd.2 = 0 := by
    constructor
    · rintro ⟨f,hf⟩
      have hh := congrArg (fun z => z.toAdd.2) hf
      change 0 • f.toAdd = _ at hh
      simpa only [zero_smul] using hh.symm
    · intro hz
      refine ⟨Multiplicative.ofAdd (p z).toAdd.1,?_⟩
      apply Multiplicative.toAdd.injective
      change (1 • (p z).toAdd.1,0 • (p z).toAdd.1) = (p z).toAdd
      simp only [one_smul,zero_smul]
      exact Prod.ext rfl hz.symm
  have hY (z : Q) : z ∈ Y ↔ (p z).toAdd.1 = 0 := by
    constructor
    · rintro ⟨f,hf⟩
      have hh := congrArg (fun z => z.toAdd.1) hf
      change 0 • f.toAdd = _ at hh
      simpa only [zero_smul] using hh.symm
    · intro hz
      refine ⟨Multiplicative.ofAdd (p z).toAdd.2,?_⟩
      apply Multiplicative.toAdd.injective
      change (0 • (p z).toAdd.2,1 • (p z).toAdd.2) = (p z).toAdd
      simp only [one_smul,zero_smul]
      exact Prod.ext hz.symm rfl
  have split (z : Q) : ∃ x ∈ X, ∃ y ∈ Y, z = x*y := by
    obtain ⟨x,hx⟩ := hp (Multiplicative.ofAdd ((p z).toAdd.1,0))
    refine ⟨x,(hX x).mpr (by rw [hx]; rfl),x⁻¹*z,(hY _).mpr ?_,by group⟩
    rw [map_mul,map_inv]
    change -(p x).toAdd.1 + (p z).toAdd.1 = 0
    rw [hx]
    exact neg_add_cancel _
  have hsup : X ⊔ Y = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨x,hx,y,hy,rfl⟩ := split z
    exact mul_mem (mem_sup_left hx) (mem_sup_right hy)
  let := hel 1 0
  let := hel 0 1
  have hclass : _root_.commutator Q ≤ center Q := by
    rw [←hc]
    exact Abelianization.commutator_subset_ker p
  obtain ⟨x,hx,y,hy,rfl⟩ := split w
  have hcommx : ∀ z : Q, ⁅x,z⁆ ∈ N := by
    have hb : X ⊔ Y ≤ N.comap (ClassTwo.commutatorHom hclass x) := by
      apply sup_le
      · intro z hz
        change ⁅x,z⁆ ∈ N
        have hh : Commute x z := congrArg Subtype.val (mul_comm' (⟨x,hx⟩ : X) ⟨z,hz⟩)
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hh.eq]
        exact N.one_mem
      · intro z hz
        change ⁅x,z⁆ ∈ N
        have hzy : Commute z y := congrArg Subtype.val (mul_comm' (⟨z,hz⟩ : Y) ⟨y,hy⟩)
        have hh := N.inv_mem (hcomm z)
        rw [commutatorElement_inv] at hh
        have heq := (ClassTwo.commutatorHom hclass z).map_mul x y
        change ⁅z,x*y⁆ = ⁅z,x⁆ * ⁅z,y⁆ at heq
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hzy.eq,mul_one] at heq
        rw [heq] at hh
        have hh' := N.inv_mem hh
        rwa [commutatorElement_inv] at hh'
    intro z
    exact hb (hsup.ge (mem_top z))
  have hcommy : ∀ z : Q, ⁅y,z⁆ ∈ N := by
    intro z
    have hh := N.inv_mem (hcomm z)
    rw [commutatorElement_inv] at hh
    have heq := (ClassTwo.commutatorHom hclass z).map_mul x y
    change ⁅z,x*y⁆ = ⁅z,x⁆ * ⁅z,y⁆ at heq
    rw [heq] at hh
    have hxz := N.inv_mem (hcommx z)
    rw [commutatorElement_inv] at hxz
    have hyz := N.mul_mem (N.inv_mem hxz) hh
    simp only [inv_mul_cancel_left] at hyz
    have hyz' := N.inv_mem hyz
    rwa [commutatorElement_inv] at hyz'
  have hxf : (p x).toAdd.1 = 0 := first_axis_small_commutators α hα p hp hc he hel N hN x _
    (Prod.ext rfl ((hX x).mp hx)) hcommx
  let swap : Multiplicative (D × D) ≃* Multiplicative (D × D) :=
    (AddEquiv.prodComm : D × D ≃+ D × D).toMultiplicative
  let s := swap.toMonoidHom.comp p
  have hs : Function.Surjective s := swap.surjective.comp hp
  have hsc : s.ker = center Q := by
    change (swap.toMonoidHom.comp p).ker = center Q
    exact (MonoidHom.ker_comp_of_injective p swap.toMonoidHom swap.injective).trans hc
  have hse : ∀ a q, (s (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (s q).toAdd := by
    intro a q
    change ((p (a • q)).toAdd.2,(p (a • q)).toAdd.1) = _
    rw [he]
    rfl
  have hsel (a b : F) : IsElementaryAbelian 2 ((dualDiagonal a b).range.comap s) := by
    have heq : (dualDiagonal a b).range.comap s = (dualDiagonal b a).range.comap p := by
      ext z
      constructor <;> rintro ⟨f,hf⟩ <;> refine ⟨f,?_⟩
      · have hh := congrArg (fun z => (z.toAdd.2,z.toAdd.1)) hf
        exact Multiplicative.toAdd.injective hh
      · have hh := congrArg (fun z => (z.toAdd.2,z.toAdd.1)) hf
        exact Multiplicative.toAdd.injective hh
    rw [heq]
    exact hel b a
  have hyg : (p y).toAdd.2 = 0 := first_axis_small_commutators α hα s hs hsc hse hsel N hN y _
    (Prod.ext rfl ((hY y).mp hy)) hcommy
  rw [←hc]
  change p (x*y) = 1
  rw [map_mul]
  apply Multiplicative.toAdd.injective
  change (p x).toAdd + (p y).toAdd = 0
  exact Prod.ext (by simp [hxf,(hY y).mp hy]) (by simp [(hX x).mp hx,hyg])

end Representation.SL3ParabolicNatural
