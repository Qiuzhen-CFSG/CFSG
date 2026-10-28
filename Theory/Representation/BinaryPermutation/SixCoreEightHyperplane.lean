module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
public import Theory.GroupTheory.TwoElementaryIndexTwo
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.ElementaryAbelian.Basic
public import Theory.Representation.BinaryPermutation.SixCoreSmallImage

/-!
# Fixed hyperplanes for elementary eight-groups on six letters

The two elementary index-two subgroups of a Sylow two-subgroup of S₆
are its literal point and syntheme radicals. Their common transposition,
transported by Sylow conjugacy, gives a transposition in every elementary
subgroup of order at least eight. A coordinate difference identifies its
fixed hyperplane in the five-dimensional augmentation core.

The actual returning-conjugate application is the weak-closure argument
of Aschbacher–Smith 13.4.16, printed p.913, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace BinaryPermutation.SixCoreWeightFour
open Theory.SpecificGroups.SymmetricSix
open BinaryFlags BinaryFlags.NaturalGeometry
private abbrev F := H1 ⊓ H2
private theorem flag_card : Nat.card F = 16 := by
  change Nat.card (H1 ⊓ H2 : Subgroup S) = 16
  rw [←canonicalSylow_coe]
  exact (Nat.card_congr (Sylow.equiv canonicalSylow borelSylow).toEquiv).trans borel_order
private theorem D_le_flag : D ≤ F := le_inf D_le_H1 D_le_H2
private theorem flag_not_elementary : ¬ IsElementaryAbelian 2 F := by
  intro h
  let g : F := ⟨Equiv.swap 0 1 * (Equiv.swap 0 2 * Equiv.swap 1 3),by
    constructor
    · change _ • pair 4 5 = pair 4 5
      decide
    · change _ • baseSyntheme = baseSyntheme
      decide⟩
  have hh := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
    (IsElementaryAbelian.exponent_dvd_p 2 F) g
  have hn : g ^ 2 ≠ 1 := by decide
  exact hn hh
private theorem two_cores_ne : pointCore ≠ D := by
  intro he
  have hm : swap01 ∈ pointCore := he ▸ swap01_mem_D
  have hn : swap01 ∉ pointCore := by
    change ¬ ∃ x : DuadProduct, x ∈ DuadCalculation.productCore ∧
      ((MulAut.conj flagRelabel).toMonoidHom.comp duadProductHom) x = swap01
    simp only [DuadCalculation.productCore,mem_prod,mem_top,true_and,DuadCalculation.core_mem_iff]
    decide +kernel
  exact hn hm

theorem eight_contains_swap (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hcard : 8 ≤ Nat.card A) :
    ∃ t ∈ A, t.IsSwap := by
  obtain ⟨P,hAP⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg,_⟩ := sylow_flag P
  let E := A.conjBy g⁻¹
  have hEF : E ≤ F := by
    rw [←hg] at hAP
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hAP
    change E ≤ (F.conjBy g).conjBy g⁻¹ at hh
    rwa [conjBy_inv] at hh
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  let X := pointCore.subgroupOf F
  let Y := D.subgroupOf F
  let : IsElementaryAbelian 2 pointCore := pointCore_elementary
  let : IsElementaryAbelian 2 D := D_elementary
  have hX : IsElementaryAbelian 2 X := IsElementaryAbelian.subgroupOf pointCore_le_flag
  have hY : IsElementaryAbelian 2 Y := IsElementaryAbelian.subgroupOf D_le_flag
  have hXc : Nat.card X = 8 := (Nat.card_congr (subgroupOfEquivOfLe pointCore_le_flag).toEquiv).trans pointCore_card
  have hYc : Nat.card Y = 8 := (Nat.card_congr (subgroupOfEquivOfLe D_le_flag).toEquiv).trans D_card
  have hXi : X.index = 2 := by have hh := X.card_mul_index; rw [hXc,flag_card] at hh; omega
  have hYi : Y.index = 2 := by have hh := Y.card_mul_index; rw [hYc,flag_card] at hh; omega
  have hne : X ≠ Y := by
    intro he
    have hh := congrArg (map F.subtype) he
    rw [map_subgroupOf_eq_of_le pointCore_le_flag,map_subgroupOf_eq_of_le D_le_flag] at hh
    exact two_cores_ne hh
  have hE := elementary_le_one_of_two_index_two X Y hX hY hXi hYi hne
    flag_not_elementary (E.subgroupOf F) (IsElementaryAbelian.subgroupOf hEF)
  have hEc : 8 ≤ Nat.card E := by
    change 8 ≤ Nat.card (A.map (MulAut.conj g⁻¹).toMonoidHom)
    rwa [card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hs : swap45 ∈ E := by
    rcases hE with he | he
    · have he' : E ≤ pointCore := fun e hee => he (show (⟨e,hEF hee⟩ : F) ∈ E.subgroupOf F from hee)
      have heq := eq_of_le_of_card_ge he' (pointCore_card ▸ hEc)
      rw [heq,pointCore_eq_closure]
      exact subset_closure (by simp)
    · have he' : E ≤ D := fun e hee => he (show (⟨e,hEF hee⟩ : F) ∈ E.subgroupOf F from hee)
      have heq := eq_of_le_of_card_ge he' (D_card ▸ hEc)
      rw [heq]
      exact swap45_mem_D
  have hm : MulAut.conj g swap45 ∈ A := by
    have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom hs
    change MulAut.conj g swap45 ∈ (A.conjBy g⁻¹).conjBy g at hh
    rwa [conjBy_inv'] at hh
  refine ⟨_,hm,?_⟩
  change (g * Equiv.swap (4 : Fin 6) 5 * g⁻¹).IsSwap
  rw [←Equiv.swap_apply_apply]
  exact ⟨_,_,g.injective.ne (by decide),rfl⟩

open Representation Representation.BinaryOffender
private def difference (i j : Fin 6) : core (Fin 6) →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun v => v.val i - v.val j
    map_add' := fun x y => by simp only [Submodule.coe_add,Pi.add_apply]; abel
    map_smul' := fun c v => by simp [mul_sub] }
private theorem swap_fixed_test : ∀ i j : Fin 6, ∀ v : Fin 6 → ZMod 2,
    representation (Fin 6) (Equiv.swap i j) v = v ↔ v i = v j := by
  decide +kernel

theorem swap_fixedCodim_le_one (t : Equiv.Perm (Fin 6)) (ht : t.IsSwap) :
    fixedCodim (coreRepresentation (Fin 6)) (zpowers t) ≤ 1 := by
  obtain ⟨i,j,_,rfl⟩ := ht
  have he : fixedSpace (coreRepresentation (Fin 6)) (zpowers (Equiv.swap i j)) =
      (difference i j).ker := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change coreRepresentation (Fin 6) (Equiv.swap i j) v = v ↔ v.val i - v.val j = 0
    rw [sub_eq_zero]
    exact Subtype.ext_iff.trans (swap_fixed_test i j v.val)
  rw [fixedCodim,he,(difference i j).quotKerEquivRange.finrank_eq]
  exact (Submodule.finrank_le _).trans (by simp)


end BinaryPermutation.SixCoreWeightFour
