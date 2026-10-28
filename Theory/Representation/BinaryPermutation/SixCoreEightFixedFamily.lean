module
public import Theory.Representation.BinaryPermutation.SixCoreEightHyperplane
public import Theory.Representation.BinaryOffender.PermutationConjugacy

/-!
# Fixed-space alternatives for elementary eight-groups on the augmentation core

Sylow conjugacy puts an elementary eight-group in one of the two elementary
maximal subgroups of the six-letter Sylow two-group. The point radical fixes
at most a two-space in the five-dimensional core, whereas the syntheme
radical contains distinct transpositions. A transposition is determined by
its fixed hyperplane, checked on the coordinate-pair generators.

These alternatives exclude the returning-conjugate hyperplane in
Aschbacher–Smith 13.4.16, printed p.913, refs/quasithin.pdf. The actual
consumer is FixedCoreSource/Nonsolvable/WeightFourClosure.
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

theorem eight_conjugate_cases (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hcard : 8 ≤ Nat.card A) :
    ∃ g, A = pointCore.conjBy g ∨ A = D.conjBy g := by
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
  have hcases : E = pointCore ∨ E = D := by
    rcases hE with he | he
    · left
      have he' : E ≤ pointCore := fun e hee => he
        (show (⟨e,hEF hee⟩ : F) ∈ E.subgroupOf F from hee)
      exact eq_of_le_of_card_ge he' (pointCore_card ▸ hEc)
    · right
      have he' : E ≤ D := fun e hee => he
        (show (⟨e,hEF hee⟩ : F) ∈ E.subgroupOf F from hee)
      exact eq_of_le_of_card_ge he' (D_card ▸ hEc)
  refine ⟨g,?_⟩
  have he : E.conjBy g = A := conjBy_inv' A g
  rcases hcases with h | h
  · exact Or.inl (he.symm.trans (congrArg (fun X : Subgroup S => X.conjBy g) h))
  · exact Or.inr (he.symm.trans (congrArg (fun X : Subgroup S => X.conjBy g) h))

open Representation Representation.BinaryOffender
private abbrev coreR := coreRepresentation (Fin 6)
private theorem point_fixed_test : ∀ v : Fin 6 → ZMod 2,
    representation (Fin 6) swap45 v = v →
    representation (Fin 6) (swap01 * swap23) v = v →
    representation (Fin 6) (Equiv.swap 0 2 * Equiv.swap 1 3) v = v →
    ∀ i : Fin 6, v i = if i.val < 4 then v 0 else v 4 := by
  decide +kernel

private theorem point_fixed_card : Nat.card (fixedSpace coreR pointCore) ≤ 4 := by
  let f : fixedSpace coreR pointCore → ZMod 2 × ZMod 2 := fun v => (v.val.val 0,v.val.val 4)
  have hf : Function.Injective f := by
    intro v w he
    have hs : swap45 ∈ pointCore := by
      rw [pointCore_eq_closure]; exact subset_closure (by simp)
    have ha : swap01 * swap23 ∈ pointCore := by
      rw [pointCore_eq_closure]; exact subset_closure (by simp)
    have hb : Equiv.swap (0 : Fin 6) 2 * Equiv.swap 1 3 ∈ pointCore := by
      rw [pointCore_eq_closure]; exact subset_closure (by simp)
    have hv := point_fixed_test v.val.val
      (congrArg Subtype.val (v.property ⟨_,hs⟩))
      (congrArg Subtype.val (v.property ⟨_,ha⟩))
      (congrArg Subtype.val (v.property ⟨_,hb⟩))
    have hw := point_fixed_test w.val.val
      (congrArg Subtype.val (w.property ⟨_,hs⟩))
      (congrArg Subtype.val (w.property ⟨_,ha⟩))
      (congrArg Subtype.val (w.property ⟨_,hb⟩))
    apply Subtype.ext
    apply Subtype.ext
    funext i
    rw [hv i,hw i,show v.val.val 0 = w.val.val 0 from congrArg Prod.fst he,
      show v.val.val 4 = w.val.val 4 from congrArg Prod.snd he]
  exact (Nat.card_le_card_of_injective f hf).trans (by rw [Nat.card_prod,Nat.card_zmod])

private theorem point_fixedCodim : 3 ≤ fixedCodim coreR pointCore := by
  have hc := point_fixed_card
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hc
  have hf : Module.finrank (ZMod 2) (fixedSpace coreR pointCore) ≤ 2 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    omega
  have hh := fixedCodim_add_finrank coreR pointCore
  rw [finrank_core] at hh
  norm_num at hh
  omega

/-- An elementary eight-group either fixes at most a two-space in the
augmentation core, or contains two distinct transpositions. -/
theorem eight_fixed_alternative (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsElementaryAbelian 2 A] (hcard : 8 ≤ Nat.card A) :
    3 ≤ fixedCodim (coreRepresentation (Fin 6)) A ∨
      ∃ s ∈ A, ∃ t ∈ A, s.IsSwap ∧ t.IsSwap ∧ s ≠ t := by
  obtain ⟨g,hg | hg⟩ := eight_conjugate_cases A hcard
  · left
    rw [hg]
    exact (fixedCodim_map_conj coreR pointCore g).symm ▸ point_fixedCodim
  · right
    rw [hg]
    refine ⟨MulAut.conj g swap01,mem_map_of_mem _ swap01_mem_D,
      MulAut.conj g swap23,mem_map_of_mem _ swap23_mem_D,?_,?_,?_⟩
    · change (g * Equiv.swap (0 : Fin 6) 1 * g⁻¹).IsSwap
      rw [←Equiv.swap_apply_apply]
      exact ⟨_,_,g.injective.ne (by decide),rfl⟩
    · change (g * Equiv.swap (2 : Fin 6) 3 * g⁻¹).IsSwap
      rw [←Equiv.swap_apply_apply]
      exact ⟨_,_,g.injective.ne (by decide),rfl⟩
    · exact (MulAut.conj g).injective.ne (by decide)
private def testPair (i j : Fin 6) : core (Fin 6) :=
  ⟨Pi.single i 1 + Pi.single j 1, by
    simp [mem_core, Finset.sum_add_distrib, Pi.single_apply, CharTwo.add_self_eq_zero]⟩
private theorem swap_fixed_test : ∀ i j k l : Fin 6, i ≠ j → k ≠ l →
    (∀ a b : Fin 6,
      coreR (Equiv.swap i j) (testPair a b) = testPair a b →
      coreR (Equiv.swap k l) (testPair a b) = testPair a b) →
    Equiv.swap i j = Equiv.swap k l := by
  decide +kernel

/-- A transposition is determined by its fixed hyperplane in the full core. -/
theorem swap_eq_of_fixed_le (s t : Equiv.Perm (Fin 6)) (hs : s.IsSwap) (ht : t.IsSwap)
    (h : ∀ v : core (Fin 6), coreRepresentation (Fin 6) s v = v →
      coreRepresentation (Fin 6) t v = v) : s = t := by
  obtain ⟨i,j,hij,rfl⟩ := hs
  obtain ⟨k,l,hkl,rfl⟩ := ht
  exact swap_fixed_test i j k l hij hkl (fun a b => h (testPair a b))
end BinaryPermutation.SixCoreWeightFour
