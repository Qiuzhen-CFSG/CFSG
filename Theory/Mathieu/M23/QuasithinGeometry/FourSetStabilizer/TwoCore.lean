module

public import Theory.Mathieu.M23.QuasithinGeometry.FourSetStabilizer.Basic
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.SplitExtension
public import Theory.Mathieu.M23.QuasithinGeometry.HeptadStructure.LocalQuotients.Labelled
public import Theory.PGroupCore
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Tactic

/-!
# The two-core of the actual four-set stabilizer in M23

The labelled action preserves the partition into the first three and last four
heptad labels, and its image consists of even permutations. The displayed
Klein four-group is normal under this action; its inverse image is a two-group
because the pointwise heptad kernel has order sixteen.

For the opposite inclusion, let t be the three-cycle on the first three labels.
For any even block permutation p outside the Klein group, either p^4 or
(p * (t * p * t⁻¹))^4 is a nonidentity element of order three. Small kernel-checked
permutation calculations verify this assertion. The actual alternating section
lifts t into the four-set stabilizer, so normality excludes such p from the
image of its two-core. All cores and normality are relative to that stabilizer.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of `refs/quasithin.pdf`); GLS3, Table 5.3d. The actual heptad
kernel and alternating section are constructed in `HeptadStructure`.
-/

public section

open Equiv Subgroup
open scoped Pointwise
namespace Sporadic.Mathieu.M23Geometry.FourSetStabilizer
private def blockPerm (a : Perm (Fin 3)) (b : Perm (Fin 4)) : Perm (Fin 7) :=
  finSumFinEquiv.permCongr (Equiv.sumCongr a b)

private theorem block_cases (p : Perm (Fin 7))
    (hp : p • heptadFourLabels = heptadFourLabels) :
    ∃ a b, p = blockPerm a b := by
  have hiff (i : Fin 7) : p i ∈ heptadFourLabels ↔ i ∈ heptadFourLabels := by
    conv_lhs => rw [← hp]
    exact Finset.smul_mem_smul_finset_iff p
  have ht (i : Fin 3) : (p (i.castAdd 4)).val < 3 := by
    have hn : i.castAdd 4 ∉ heptadFourLabels := by fin_cases i <;> decide
    have hn' := (hiff (i.castAdd 4)).not.mpr hn
    have hd : ∀ j : Fin 7, j ∉ heptadFourLabels → j.val < 3 := by decide +kernel
    exact hd _ hn'
  have hf (i : Fin 4) : 3 ≤ (p (i.natAdd 3)).val := by
    have hn : i.natAdd 3 ∈ heptadFourLabels := by fin_cases i <;> decide
    have hn' := (hiff (i.natAdd 3)).mpr hn
    have hd : ∀ j : Fin 7, j ∈ heptadFourLabels → 3 ≤ j.val := by decide +kernel
    exact hd _ hn'
  let f : Fin 3 → Fin 3 := fun i => ⟨(p (i.castAdd 4)).val, ht i⟩
  have hfi : Function.Injective f := by
    intro i j h
    have he : p (i.castAdd 4) = p (j.castAdd 4) := Fin.ext (congrArg (Fin.val : Fin 3 → ℕ) h)
    exact Fin.ext (congrArg (Fin.val : Fin 7 → ℕ) (p.injective he))
  let g : Fin 4 → Fin 4 := fun i => ⟨(p (i.natAdd 3)).val - 3, by have := (p (i.natAdd 3)).isLt; omega⟩
  have hgi : Function.Injective g := by
    intro i j h
    have hv := congrArg Fin.val h
    change (p (i.natAdd 3)).val - 3 = (p (j.natAdd 3)).val - 3 at hv
    have he : p (i.natAdd 3) = p (j.natAdd 3) := Fin.ext (by have := hf i; have := hf j; omega)
    have he' := congrArg Fin.val (p.injective he)
    apply Fin.ext
    simp only [Fin.val_natAdd] at he'
    omega
  let a : Perm (Fin 3) := Equiv.ofBijective f ⟨hfi, Finite.surjective_of_injective hfi⟩
  let b : Perm (Fin 4) := Equiv.ofBijective g ⟨hgi, Finite.surjective_of_injective hgi⟩
  refine ⟨a, b, ?_⟩
  have ha (i : Fin 3) : (a i).val = (p (i.castAdd 4)).val := rfl
  have hb (i : Fin 4) : (b i).val + 3 = (p (i.natAdd 3)).val := by
    change (p (i.natAdd 3)).val - 3 + 3 = _
    exact Nat.sub_add_cancel (hf i)
  have hab : ∀ a : Perm (Fin 3), ∀ b : Perm (Fin 4),
      (∀ i : Fin 3, (blockPerm a b (i.castAdd 4)).val = (a i).val) ∧
      (∀ i : Fin 4, (blockPerm a b (i.natAdd 3)).val = (b i).val + 3) := by
    intro a b
    constructor
    · intro i
      simp only [blockPerm, permCongr_apply]
      rw [finSumFinEquiv_symm_apply_castAdd]
      rfl
    · intro i
      simp only [blockPerm, permCongr_apply]
      rw [finSumFinEquiv_symm_apply_natAdd]
      exact Nat.add_comm _ _
  apply Equiv.ext
  intro i
  apply Fin.ext
  fin_cases i
  · exact (ha 0).symm.trans ((hab a b).1 0).symm
  · exact (ha 1).symm.trans ((hab a b).1 1).symm
  · exact (ha 2).symm.trans ((hab a b).1 2).symm
  · exact (hb 0).symm.trans ((hab a b).2 0).symm
  · exact (hb 1).symm.trans ((hab a b).2 1).symm
  · exact (hb 2).symm.trans ((hab a b).2 2).symm
  · exact (hb 3).symm.trans ((hab a b).2 3).symm

private def triple : Perm (Fin 7) := swap 0 1 * swap 1 2

private theorem block_conj_double (a : Perm (Fin 3)) (b : Perm (Fin 4))
    (i j k l : Fin 4) :
    blockPerm a b * (swap (i.natAdd 3) (j.natAdd 3) *
      swap (k.natAdd 3) (l.natAdd 3)) * (blockPerm a b)⁻¹ =
    swap ((b i).natAdd 3) ((b j).natAdd 3) *
      swap ((b k).natAdd 3) ((b l).natAdd 3) := by
  have hr (i : Fin 4) : blockPerm a b (i.natAdd 3) = (b i).natAdd 3 := by
    simp only [blockPerm, permCongr_apply]
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  have hc : ∀ p x y : Perm (Fin 7),
      p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) := by
    intros
    group
  rw [hc, ← swap_apply_apply, ← swap_apply_apply, hr, hr, hr, hr]

private theorem block_normalizes : ∀ a b, ∀ k ∈ labelKlein,
    blockPerm a b * k * (blockPerm a b)⁻¹ ∈ labelKlein := by
  have hn : ∀ b : Perm (Fin 4),
      (swap ((b 0).natAdd 3) ((b 1).natAdd 3) *
        swap ((b 2).natAdd 3) ((b 3).natAdd 3) ∈ labelKlein) ∧
      (swap ((b 0).natAdd 3) ((b 2).natAdd 3) *
        swap ((b 1).natAdd 3) ((b 3).natAdd 3) ∈ labelKlein) := by
    simp only [labelKlein, Subgroup.mem_mk, Submonoid.mem_mk,
      Subsemigroup.mem_mk, Set.mem_ofPred_eq]
    decide +kernel
  intro a b k hk
  have hfirst : blockPerm a b * firstDoubleSwap * (blockPerm a b)⁻¹ ∈ labelKlein := by
    change blockPerm a b * (swap ((0 : Fin 4).natAdd 3) ((1 : Fin 4).natAdd 3) *
      swap ((2 : Fin 4).natAdd 3) ((3 : Fin 4).natAdd 3)) * (blockPerm a b)⁻¹ ∈ _
    rw [block_conj_double]
    exact (hn b).1
  have hsecond : blockPerm a b * secondDoubleSwap * (blockPerm a b)⁻¹ ∈ labelKlein := by
    change blockPerm a b * (swap ((0 : Fin 4).natAdd 3) ((2 : Fin 4).natAdd 3) *
      swap ((1 : Fin 4).natAdd 3) ((3 : Fin 4).natAdd 3)) * (blockPerm a b)⁻¹ ∈ _
    rw [block_conj_double]
    exact (hn b).2
  rcases hk with rfl | rfl | rfl | rfl
  · simpa only [mul_one, mul_inv_cancel] using labelKlein.one_mem
  · exact hfirst
  · exact hsecond
  · have h := labelKlein.mul_mem hfirst hsecond
    simpa only [mul_assoc, inv_mul_cancel_left] using h

/-- The six explicit first-block representatives keep each finite check small. -/
private theorem block_obstruction : ∀ a b,
    (blockPerm a b).sign = 1 → blockPerm a b ∉ labelKlein →
    ((blockPerm a b)^4)^3 = 1 ∧ (blockPerm a b)^4 ≠ 1 ∨
    ((blockPerm a b * (triple * blockPerm a b * triple⁻¹))^4)^3 = 1 ∧
      (blockPerm a b * (triple * blockPerm a b * triple⁻¹))^4 ≠ 1 := by
  have ha : ∀ a : Perm (Fin 3), a = 1 ∨ a = swap 0 1 ∨ a = swap 0 2 ∨
      a = swap 1 2 ∨ a = swap 0 1 * swap 1 2 ∨ a = swap 1 2 * swap 0 1 := by
    decide +kernel
  intro a
  rcases ha a with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [mem_labelKlein] <;> decide +kernel

private theorem label_mem_four (i : Fin 7) : label i ∈ lambda ↔ i ∈ heptadFourLabels := by
  revert i
  decide +kernel

private theorem four_action_mem (g : heptadStabilizer) :
    (g : M23) ∈ fourStabilizer ↔
      heptadAction g ∈ MulAction.stabilizer (Perm (Fin 7)) heptadFourLabels := by
  constructor
  · intro h
    apply MulAction.mem_stabilizer_finset'.mpr
    intro i hi
    apply (label_mem_four _).mp
    change label (heptadAction g i) ∈ lambda
    rw [heptadAction_apply]
    exact MulAction.mem_stabilizer_finset'.mp h ((label_mem_four i).mpr hi)
  · intro h
    apply MulAction.mem_stabilizer_finset'.mpr
    intro a ha
    have hL : heptadFourLabels.image label = lambda := by decide +kernel
    rw [← hL] at ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    rw [← heptadAction_apply]
    exact (label_mem_four _).mpr (MulAction.mem_stabilizer_finset'.mp h hi)

private theorem labelAction_preserves (g : fourStabilizer) :
    labelAction g • heptadFourLabels = heptadFourLabels :=
  (four_action_mem (inclusion fourStabilizer_le g)).mp g.property

private theorem labelAction_even (g : fourStabilizer) : (labelAction g).sign = 1 := by
  apply Perm.mem_alternatingGroup.mp
  rw [← heptadAction_range]
  exact ⟨inclusion fourStabilizer_le g, rfl⟩

private theorem triple_lift : ∃ t : fourStabilizer, labelAction t = triple := by
  have ht : triple ∈ alternatingGroup (Fin 7) := by
    simp [triple, Perm.mem_alternatingGroup]
  let t := AlternatingSection.s ⟨triple, ht⟩
  have hta : heptadAction t = triple := AlternatingSection.heptadAction_s _
  have ht4 : (t : M23) ∈ fourStabilizer := by
    apply (four_action_mem t).mpr
    rw [hta]
    change triple • heptadFourLabels = heptadFourLabels
    decide +kernel
  exact ⟨⟨t, ht4⟩, hta⟩

/-- The concrete inverse image of the label four-group is normal in the
actual four-set stabilizer. -/
private theorem coreCandidate_normal : coreCandidate.Normal := by
  constructor
  intro k hk g
  change labelAction (g * k * g⁻¹) ∈ labelKlein
  rw [map_mul, map_mul, map_inv]
  obtain ⟨a, b, hab⟩ := block_cases (labelAction g) (labelAction_preserves g)
  rw [hab]
  exact block_normalizes a b _ hk

/-- The inverse image is a two-group: the pointwise heptad kernel and the
label four-group are both two-groups. -/
private theorem coreCandidate_isPGroup : IsPGroup 2 coreCandidate := by
  have hK : IsPGroup 2 labelKlein := by
    intro k
    exact ⟨1, by simpa using labelKlein_square k⟩
  have hU : IsPGroup 2 heptadKernel := IsPGroup.of_card (n := 4) heptadKernel_card
  have hk : IsPGroup 2 labelAction.ker := by
    change IsPGroup 2 (heptadKernel.comap (inclusion fourStabilizer_le))
    exact hU.comap_of_injective _ (inclusion_injective fourStabilizer_le)
  exact hK.comap_of_ker_isPGroup labelAction hk

private theorem no_three_in_two_image (p : Perm (Fin 7))
    (hp : p ∈ (pCore 2 fourStabilizer).map labelAction)
    (hpow : p^3 = 1) (hne : p ≠ 1) : False := by
  let N := (pCore 2 fourStabilizer).map labelAction
  have hN : IsPGroup 2 N := pCore_isPGroup.map labelAction
  let u : N := ⟨p, hp⟩
  have hc := hN.orderOf_coprime (n := 3) (by decide) u
  have hd : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext hpow)
  have he : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hc (dvd_refl _) hd
  exact hne (congrArg Subtype.val (orderOf_eq_one_iff.mp he))

/-- The two-core is precisely the inverse image of the double transpositions
on the four chosen heptad labels. The two-core here is computed inside the
actual four-set stabilizer. -/
theorem fourStabilizer_twoCore_eq : pCore 2 fourStabilizer = coreCandidate := by
  apply le_antisymm
  · intro g hg
    change labelAction g ∈ labelKlein
    by_contra hout
    obtain ⟨a, b, hab⟩ := block_cases (labelAction g) (labelAction_preserves g)
    have he : (blockPerm a b).sign = 1 := hab ▸ labelAction_even g
    have ho : blockPerm a b ∉ labelKlein := hab ▸ hout
    obtain ⟨t, ht⟩ := triple_lift
    let N := (pCore 2 fourStabilizer).map labelAction
    have hgN : labelAction g ∈ N := Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hqN : labelAction g * (triple * labelAction g * triple⁻¹) ∈ N := by
      apply N.mul_mem hgN
      have hc := (pCore_normal (p := 2) (G := fourStabilizer)).conj_mem g hg t
      have hm : labelAction (t * g * t⁻¹) ∈ N := Subgroup.mem_map.mpr ⟨_, hc, rfl⟩
      simpa only [map_mul, map_inv, ht] using hm
    rcases block_obstruction a b he ho with ⟨hpow, hne⟩ | ⟨hpow, hne⟩
    · rw [← hab] at hpow hne
      exact no_three_in_two_image _ (N.pow_mem hgN 4) hpow hne
    · rw [← hab] at hpow hne
      exact no_three_in_two_image _ (N.pow_mem hqN 4) hpow hne
  · exact le_sSup ⟨coreCandidate_normal, coreCandidate_isPGroup⟩

end Sporadic.Mathieu.M23Geometry.FourSetStabilizer
