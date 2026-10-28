module
public import Theory.SpecificGroups.PSL3Three.Basic
public import Theory.SpecificGroups.SL3.InvolutionConjugacy
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Group

/-!
# Conjugacy of the inner four-group actors

Every elementary four-subgroup of SL₃(3) is conjugate to the diagonal sign
subgroup. Conjugate one involution to diag(-1,-1,1), then use a checked
GL₂ block change of basis for a commuting independent involution. The two
signs generate four elements, so containment and equal orders retain the
whole actor. This gives conjugacy of any two elementary four-subgroups.

The twelve block matrices and the 243-case scalar certificate are reused
from `PSL3Three.InnerFourGeneration`. Only these small matrix identities are
computed. This supplies actor conjugacy for the concrete E.1.2 placement
used in Aschbacher–Smith E.1.14(7), printed pp.209–210, 214; Asc82a 4.11.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup
open Matrix.PSL3Three
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors

private def sign : SL := ⟨!![1,0,0; 0,2,0; 0,0,2], by decide⟩
private abbrev z := Matrix.SL3.standardInvolution (ZMod 3)
private def blockConjugator : Fin 12 → SL :=
  ![⟨!![1,1,0; 1,2,0; 0,0,1], by decide⟩,
    ⟨!![1,2,0; 1,1,0; 0,0,2], by decide⟩,
    ⟨!![1,0,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![1,0,0; 1,1,0; 0,0,1], by decide⟩,
    ⟨!![1,0,0; 1,2,0; 0,0,2], by decide⟩,
    ⟨!![1,2,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![1,1,0; 0,1,0; 0,0,1], by decide⟩,
    ⟨!![0,1,0; 1,0,0; 0,0,2], by decide⟩,
    ⟨!![1,2,0; 1,0,0; 0,0,1], by decide⟩,
    ⟨!![1,1,0; 1,0,0; 0,0,2], by decide⟩,
    ⟨!![0,1,0; 1,1,0; 0,0,2], by decide⟩,
    ⟨!![0,1,0; 1,2,0; 0,0,2], by decide⟩]

private theorem blockConjugator_commute (i : Fin 12) :
    Commute (blockConjugator i) z := by
  change blockConjugator i * z = z * blockConjugator i
  apply Subtype.ext
  revert i
  decide

private theorem block_certificate : ∀ a b c d e : ZMod 3,
    let M : Matrix (Fin 3) (Fin 3) (ZMod 3) := !![a,b,0; c,d,0; 0,0,e]
    M * M = 1 → M.det = 1 → M ≠ 1 → M ≠ z.val →
      ∃ i : Fin 12, (blockConjugator i).val * M = sign.val * (blockConjugator i).val := by
  decide

private theorem second_involution (u : SL) (hu : u ^ 2 = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) (hc : Commute u z) :
    ∃ c : SL, c * z * c⁻¹ = z ∧ c * u * c⁻¹ = sign := by
  have hoff := (Matrix.SL3.mem_standardInvolution_centralizer_iff (ZMod 3)
    (by decide) u).mp (mem_centralizer_singleton_iff.mpr hc.eq)
  have he : u.val = !![u 0 0, u 0 1, 0; u 1 0, u 1 1, 0; 0, 0, u 2 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all
  obtain ⟨i, hi⟩ := block_certificate (u 0 0) (u 0 1) (u 1 0) (u 1 1) (u 2 2)
    (by rw [← he]; exact congrArg Subtype.val (by simpa [pow_two] using hu))
    (by rw [← he]; exact u.property)
    (by rw [← he]; exact fun h => hu1 (Subtype.ext h))
    (by rw [← he]; exact fun h => huz (Subtype.ext h))
  refine ⟨blockConjugator i, ?_, ?_⟩
  · rw [(blockConjugator_commute i).eq, mul_inv_cancel_right]
  · have hh : blockConjugator i * u = sign * blockConjugator i := by
      apply Subtype.ext
      change (blockConjugator i).val * u.val = sign.val * (blockConjugator i).val
      simpa only [← he] using hi
    rw [hh, mul_inv_cancel_right]

open scoped IsMulCommutative in
private theorem normalize_four (A : Subgroup SL) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 4) :
    ∃ s : SL, z ∈ A.map (MulAut.conj s).toMonoidHom ∧
      sign ∈ A.map (MulAut.conj s).toMonoidHom := by
  have hA : A ≠ ⊥ := by intro he; simp [he] at hcard
  obtain ⟨t, htA, ht1⟩ := A.bot_or_exists_ne_one.resolve_left hA
  have ht2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) t htA
  have hto : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hlt : zpowers t < A := by
    refine lt_of_le_of_ne (zpowers_le.mpr htA) ?_
    intro he
    have hh := congrArg (fun B : Subgroup SL => Nat.card B) he
    rw [Nat.card_zpowers, hto, hcard] at hh
    omega
  obtain ⟨u, huA, hut⟩ := SetLike.exists_of_lt hlt
  have hu1 : u ≠ 1 := fun he => hut (he ▸ (zpowers t).one_mem)
  have hutz : u ≠ t := fun he => hut (he ▸ mem_zpowers t)
  have hu2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) u huA
  have hcomm : Commute u t :=
    congrArg Subtype.val (mul_comm (⟨u, huA⟩ : A) ⟨t, htA⟩)
  obtain ⟨s, hs⟩ := isConj_iff.mp
    (Matrix.SL3.involution_isConj_standard (ZMod 3) t hto (by decide))
  let α := MulAut.conj s
  have hαt : α t = z := hs
  have hαu : α u ≠ 1 := by simpa using hu1
  have hαuz : α u ≠ z := by rw [← hαt]; exact α.injective.ne hutz
  have hαu2 : (α u) ^ 2 = 1 := by rw [← map_pow, hu2, map_one]
  obtain ⟨c, hcz, hcu⟩ := second_involution (α u) hαu2 hαu hαuz
    (hαt ▸ hcomm.map α.toMonoidHom)
  let β := MulAut.conj (c * s)
  have hβt : β t = z := by
    change (c * s) * t * (c * s)⁻¹ = z
    calc
      _ = c * (s * t * s⁻¹) * c⁻¹ := by group
      _ = z := by rw [hs]; exact hcz
  have hβu : β u = sign := by
    change (c * s) * u * (c * s)⁻¹ = sign
    calc
      _ = c * (s * u * s⁻¹) * c⁻¹ := by group
      _ = sign := hcu
  exact ⟨c * s, hβt ▸ mem_map_of_mem β.toMonoidHom htA,
    hβu ▸ mem_map_of_mem β.toMonoidHom huA⟩

private def diagonalFour : Subgroup SL := closure {z, sign}

private theorem diagonalFour_le (H : Subgroup SL) (hz : z ∈ H) (hs : sign ∈ H) :
    diagonalFour ≤ H := by
  apply (closure_le H).mpr
  intro x hx
  rcases hx with rfl | rfl
  · exact hz
  · exact hs

private theorem diagonalFour_card_ge : 4 ≤ Nat.card diagonalFour := by
  let e : Fin 4 → SL := ![1, z, sign, z * sign]
  have he : ∀ i, e i ∈ diagonalFour := by
    intro i
    have hz : z ∈ diagonalFour := subset_closure (by simp)
    have hs : sign ∈ diagonalFour := subset_closure (by simp)
    fin_cases i
    · exact diagonalFour.one_mem
    · exact hz
    · exact hs
    · exact diagonalFour.mul_mem hz hs
  have hinj : Function.Injective e := by
    have hh : ∀ i j, (e i).val = (e j).val → i = j := by decide
    exact fun i j hij => hh i j (congrArg Subtype.val hij)
  have hi := Nat.card_le_card_of_injective (fun i => (⟨e i, he i⟩ : diagonalFour))
    (fun _ _ h => hinj (congrArg Subtype.val h))
  simpa using hi

private theorem normalize_four_eq (A : Subgroup SL) [IsElementaryAbelian 2 A]
    (hcard : Nat.card A = 4) :
    ∃ s : SL, A.map (MulAut.conj s).toMonoidHom = diagonalFour := by
  obtain ⟨s, hz, hs⟩ := normalize_four A hcard
  refine ⟨s, (Subgroup.eq_of_le_of_card_ge (diagonalFour_le _ hz hs) ?_).symm⟩
  rw [card_map_of_injective (MulAut.conj s).injective, hcard]
  exact diagonalFour_card_ge

/-- Every two elementary four-subgroups of the literal SL₃(3) are conjugate. -/
theorem four_conjugate (A B : Subgroup SL) [IsElementaryAbelian 2 A]
    [IsElementaryAbelian 2 B] (hA : Nat.card A = 4) (hB : Nat.card B = 4) :
    ∃ s : SL, A.map (MulAut.conj s).toMonoidHom = B := by
  obtain ⟨a, ha⟩ := normalize_four_eq A hA
  obtain ⟨b, hb⟩ := normalize_four_eq B hB
  refine ⟨b⁻¹ * a, ?_⟩
  apply Subgroup.map_injective (f := (MulAut.conj b).toMonoidHom) (MulAut.conj b).injective
  rw [hb, ← ha, map_map]
  apply congrArg (fun f : SL →* SL => A.map f)
  apply MonoidHom.ext
  intro x
  change b * ((b⁻¹ * a) * x * (b⁻¹ * a)⁻¹) * b⁻¹ = a * x * a⁻¹
  group

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors
