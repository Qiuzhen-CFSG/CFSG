module
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.ModelNormalizers.BlockCalculations
public import Theory.SpecificGroups.AlternatingSeven.InvolutionResidual

/-!
# The four-group and its cubic normalizer on seven letters

The normalizer of the cubic on {4,5,6} preserves the Klein four on
{0,1,2,3}. Every even two-subgroup centralizing that cubic lies in this
four-group. The product of the cubics on {0,1,2} and {4,5,6} is an actual
order-nine subgroup of its alternating normalizer.

The calculation uses the faithful S₄ × S₃ block action. Cubing every even
centralizing block permutation lands in the four-group; the cube map on
any two-group is bijective. All word checks use at most 144 block elements.
Source: Aschbacher–Smith, proof of 12.6.26, printed p.832.
-/

@[expose] public section
open Equiv Subgroup
open Representation.AlternatingSevenConjugatePair.ElementaryGeometry
open AlternatingSeven.ThreeResidualLocals
namespace AlternatingSeven.CubicFour
abbrev cubic : S7 := swap 4 5 * swap 5 6
abbrev fourWord (v : Fin 2 × Fin 2) : S7 :=
  (swap 0 1 * swap 2 3) ^ v.1.val * (swap 0 2 * swap 1 3) ^ v.2.val

def four : Subgroup S7 := rangeSubgroup fourWord ⟨(0,0),by decide +kernel⟩
  (by intro i j; exact ⟨(i.1+j.1,i.2+j.2), (by decide +kernel :
    ∀ i j : Fin 2 × Fin 2, fourWord (i.1+j.1,i.2+j.2) = fourWord i * fourWord j) i j⟩)
  (by intro i; exact ⟨i, (by decide +kernel : ∀ i, fourWord i = (fourWord i)⁻¹) i⟩)

theorem four_card : Nat.card four = 4 := by
  change Nat.card (Set.range fourWord) = _
  rw [Nat.card_congr (Equiv.ofInjective fourWord (by decide +kernel)).symm]
  simp

theorem four_two : IsPGroup 2 four := IsPGroup.of_card (n := 2) four_card

theorem four_even : four ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨i,rfl⟩
  exact (by decide +kernel : ∀ i, (fourWord i).sign = 1) i

private theorem normalizer_le_block : normalizer (zpowers cubic : Set S7) ≤ fourPointSetwiseStabilizer := by
  intro g hg x
  have hfix (x : Fin 7) : x.val < 4 ↔ ∀ a ∈ zpowers cubic, a x = x := by
    constructor
    · intro hx a ha
      obtain ⟨k,rfl⟩ := ha
      exact Perm.zpow_apply_eq_self_of_apply_eq_self (by
        have h : ∀ x : Fin 7, x.val < 4 → cubic x = x := by decide +kernel
        exact h x hx) k
    · intro hx
      have hh := hx cubic (mem_zpowers _)
      exact (by decide +kernel : ∀ x : Fin 7, cubic x = x → x.val < 4) x hh
  change x.val < 4 ↔ (g x).val < 4
  rw [hfix,hfix]
  constructor
  · intro hx a ha
    have hm : g⁻¹ * a * g ∈ zpowers cubic :=
      (mem_normalizer_iff.mp ((normalizer _).inv_mem hg) a).mp ha
    have hh := congrArg g (hx _ hm)
    simpa using hh
  · intro hx a ha
    have hm : g * a * g⁻¹ ∈ zpowers cubic := (mem_normalizer_iff.mp hg a).mp ha
    have hh := hx _ hm
    simpa using g.injective hh

set_option maxRecDepth 4096 in
private theorem block_normalizes_four (p : Perm (Fin 4) × Perm (Fin 3)) :
    ∀ i : Fin 2 × Fin 2, ∃ j : Fin 2 × Fin 2,
      blockHom p * fourWord i * (blockHom p)⁻¹ = fourWord j := by
  decide +revert +kernel

theorem normalizer_cubic_le_normalizer_four :
    normalizer (zpowers cubic : Set S7) ≤ normalizer (four : Set S7) := by
  intro g hg
  obtain ⟨p,rfl⟩ := blockHom_range.ge (normalizer_le_block hg)
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj _).injective])
  rintro _ ⟨x,⟨i,rfl⟩,rfl⟩
  obtain ⟨j,hj⟩ := block_normalizes_four p i
  exact ⟨j,hj.symm⟩

set_option maxRecDepth 4096 in
private theorem block_cube_mem_four (p : Perm (Fin 4) × Perm (Fin 3))
    (hc : cubic * blockHom p = blockHom p * cubic)
    (he : (blockHom p).sign = 1) : ∃ i, fourWord i = (blockHom p)^3 := by
  decide +revert +kernel

theorem two_subgroup_le_four (R : Subgroup S7) (hR : IsPGroup 2 R)
    (he : R ≤ alternatingGroup (Fin 7))
    (hc : R ≤ centralizer (zpowers cubic : Set S7)) : R ≤ four := by
  intro r hr
  obtain ⟨s,hs⟩ := (hR.powEquiv (by decide : Nat.Coprime 2 3)).surjective ⟨r,hr⟩
  have hsr : (s.val : S7)^3 = r := congrArg Subtype.val hs
  obtain ⟨p,hp⟩ := blockHom_range.ge (normalizer_le_block
    (Subgroup.centralizer_le_normalizer _ (hc s.property)))
  obtain ⟨i,hi⟩ := block_cube_mem_four p (hp ▸ hc s.property cubic (mem_zpowers _))
    (hp ▸ he s.property)
  exact ⟨i,hi.trans ((congrArg (fun x : S7 => x^3) hp).trans hsr)⟩
end AlternatingSeven.CubicFour

namespace AlternatingSeven.CubicFour
abbrev nineWord (v : Fin 3 × Fin 3) : S7 :=
  (swap 0 1 * swap 1 2) ^ v.1.val * cubic ^ v.2.val

def nine : Subgroup S7 := rangeSubgroup nineWord ⟨(0,0),by decide +kernel⟩
  (by intro i j; exact ⟨(i.1+j.1,i.2+j.2), (by decide +kernel :
    ∀ i j : Fin 3 × Fin 3, nineWord (i.1+j.1,i.2+j.2) = nineWord i * nineWord j) i j⟩)
  (by intro i; exact ⟨(-i.1,-i.2), (by decide +kernel :
    ∀ i : Fin 3 × Fin 3, nineWord (-i.1,-i.2) = (nineWord i)⁻¹) i⟩)

theorem nine_card : Nat.card nine = 9 := by
  change Nat.card (Set.range nineWord) = _
  rw [Nat.card_congr (Equiv.ofInjective nineWord (by decide +kernel)).symm]
  simp

theorem nine_even : nine ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨i,rfl⟩
  exact (by decide +kernel : ∀ i, (nineWord i).sign = 1) i

theorem nine_normalizes_four : nine ≤ normalizer (four : Set S7) := by
  apply le_trans ?_ normalizer_cubic_le_normalizer_four
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.le_centralizer_iff]
  apply zpowers_le.mpr
  rintro _ ⟨i,rfl⟩
  exact (by decide +kernel : ∀ i, nineWord i * cubic = cubic * nineWord i) i
end AlternatingSeven.CubicFour
