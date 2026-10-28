module
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme.Calculation
public import Theory.GroupTheory.SymmetricThree.TranspositionCharacter
import Mathlib.Tactic

/-!
# Large binary kernel in the three-block wreath model

For a subgroup of the literal `C₂³ ⋊ S₃` syntheme model whose block
projection is onto `S₃`, the kernel on the three binary flips is normal.
The existing even-core calculation leaves only the even four-group or all
three flips once the kernel has order at least four.  A nontrivial character
which kills the even flips and one transposition lift forces the latter case;
this is the finite wreath input for the M₁₂ branch of Goldschmidt §6.12.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.SynthemeCalculation

/-- The even four-group, regarded as a subgroup of the full wreath model. -/
abbrev evenKernel : Subgroup Model := evenCore.map evenModel.subtype

theorem evenKernel_card : Nat.card evenKernel = 4 := by
  rw [Subgroup.card_subtype, evenCore_card]

private theorem kernel_normal (H : Subgroup Model)
    (hsurj : Function.Surjective (quotientHom.comp H.subtype)) :
    (H ⊓ core).Normal := by
  refine ⟨?_⟩
  intro x hx g
  have hxcore : x.right = 1 := hx.2
  have hxeq : x = SemidirectProduct.inl x.left :=
    SemidirectProduct.ext rfl hxcore
  obtain ⟨h, hh⟩ := hsurj g.right
  have hr : h.val.right = g.right := hh
  have hc : g * x * g⁻¹ = h.val * x * h.val⁻¹ := by
    rw [hxeq, conjugate_inl, conjugate_inl, hr]
  refine ⟨?_, ?_⟩
  · rw [hc]
    exact H.mul_mem (H.mul_mem h.property hx.1) (H.inv_mem h.property)
  · exact quotientHom.normal_ker.conj_mem x hx.2 g

private theorem even_index : evenModel.index = 2 := by
  have hh := evenModel.card_mul_index
  rw [evenModel_card, model_card] at hh
  omega

private theorem evenKernel_eq : evenKernel = core ⊓ evenModel := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨hy, y.property⟩
  · intro hx
    exact ⟨⟨x, hx.2⟩, hx.1, rfl⟩

private theorem evenKernel_le_of_card (K : Subgroup Model) [K.Normal]
    (hK : K ≤ core) (hcard : 4 ≤ Nat.card K) : evenKernel ≤ K := by
  have hle : K.subgroupOf evenModel ≤ evenCore := fun x hx => hK hx
  rcases normal_subgroup_evenCore (K.subgroupOf evenModel) hle with hb | he
  · let : evenModel.Normal := by
      change ((alternatingGroup (Fin 6)).comap modelHom).Normal
      infer_instance
    have hi : K ⊓ evenModel = ⊥ := disjoint_iff.mp (subgroupOf_eq_bot.mp hb)
    have hh : evenModel.relIndex K ≤ 2 := by
      have hd := evenModel.relIndex_dvd_index_of_normal K
      rw [even_index] at hd
      exact Nat.le_of_dvd (by decide) hd
    rw [← inf_relIndex_left, hi, relIndex_bot_left] at hh
    omega
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ K.subgroupOf evenModel := by rw [he]; exact hy
    exact hy'

theorem large_kernel_dichotomy (H : Subgroup Model)
    (hsurj : Function.Surjective (quotientHom.comp H.subtype))
    (hcard : 4 ≤ Nat.card (H ⊓ core : Subgroup Model)) :
    H ⊓ core = evenKernel ∨ H ⊓ core = core := by
  let K := H ⊓ core
  let : K.Normal := kernel_normal H hsurj
  have hK : K ≤ core := inf_le_right
  have hEven : evenKernel ≤ K := evenKernel_le_of_card K hK hcard
  have hDiv : Nat.card K ∣ 8 := by
    rw [← core_card]
    exact card_dvd_of_le hK
  have hUpper : Nat.card K ≤ 8 := by
    rw [← core_card]
    exact card_le_of_le hK
  have hCases : Nat.card K = 4 ∨ Nat.card K = 8 := by
    interval_cases hn : Nat.card K <;> norm_num at *
  rcases hCases with h4 | h8
  · left
    apply Eq.symm
    apply eq_of_le_of_card_ge hEven
    rw [Subgroup.card_subtype, evenCore_card, h4]
  · right
    apply eq_of_le_of_card_ge hK
    rw [h8, core_card]


theorem large_kernel_of_mixed_flip (H : Subgroup Model)
    (hsurj : Function.Surjective (quotientHom.comp H.subtype))
    (g : Model) (hg : g ∈ H ⊓ core)
    (h0 : g.left.toAdd 0 = 0) (h1 : g.left.toAdd 1 = 1) :
    4 ≤ Nat.card (H ⊓ core : Subgroup Model) := by
  let K := H ⊓ core
  let : K.Normal := kernel_normal H hsurj
  let u : Model := SemidirectProduct.inr (Equiv.swap (0 : Fin 3) 1)
  let y : Model := g * (u * g * u⁻¹)⁻¹
  have hyK : y ∈ K := K.mul_mem hg
    (K.inv_mem (Subgroup.Normal.conj_mem inferInstance g hg u))
  have hgeq : g = SemidirectProduct.inl g.left :=
    SemidirectProduct.ext rfl hg.2
  have hyleft : y.left = Multiplicative.ofAdd ![1, 1, 0] := by
    change (g * (u * g * u⁻¹)⁻¹).left = Multiplicative.ofAdd ![1, 1, 0]
    rw [hgeq, conjugate_inl, ← map_inv, ← map_mul]
    rw [SemidirectProduct.left_inl]
    funext i
    change g.left.toAdd i + - g.left.toAdd ((Equiv.swap (0 : Fin 3) 1)⁻¹ i) =
      ![1, 1, 0] i
    have hs : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
    fin_cases i <;> simp [h0, h1, hs, ZModModule.add_self]
  have hyEven : y ∈ evenModel := by
    rw [mem_evenModel, hyleft]
    decide
  have hyne : y ≠ 1 := by
    intro he
    have hcoord := congrArg (fun a : Model => a.left.toAdd 0) he
    rw [hyleft] at hcoord
    norm_num at hcoord
  have hEven : evenKernel ≤ K := by
    have hle : K.subgroupOf evenModel ≤ evenCore := fun x hx => hx.2
    rcases normal_subgroup_evenCore (K.subgroupOf evenModel) hle with hb | he
    · have hy : (⟨y, hyEven⟩ : evenModel) ∈ K.subgroupOf evenModel := hyK
      rw [hb, Subgroup.mem_bot] at hy
      exact (hyne (congrArg Subtype.val hy)).elim
    · rintro x ⟨z, hz, rfl⟩
      have hz' : z ∈ K.subgroupOf evenModel := by rw [he]; exact hz
      exact hz'
  have hc := card_le_of_le hEven
  rw [Subgroup.card_subtype, evenCore_card] at hc
  exact hc


theorem core_le_of_nontrivial_character {C : Type*} [Group C]
    (H : Subgroup Model)
    (hsurj : Function.Surjective (quotientHom.comp H.subtype))
    (hcard : 4 ≤ Nat.card (H ⊓ core : Subgroup Model))
    (χ : H →* C) (hχ : χ ≠ 1)
    (hEven : ∀ x : H, x.val ∈ evenKernel → χ x = 1)
    (t : H) (ht : (quotientHom t.val).IsSwap) (hχt : χ t = 1) : core ≤ H := by
  rcases large_kernel_dichotomy H hsurj hcard with he | hf
  · have hker : (quotientHom.comp H.subtype).ker ≤ χ.ker := by
      intro x hx
      apply hEven x
      rw [← he]
      exact ⟨x.property, hx⟩
    exact (hχ (MonoidHom.eq_one_of_ker_le_of_swap
      (quotientHom.comp H.subtype) hsurj χ hker t ht hχt)).elim
  · rw [← hf]
    exact inf_le_left

def singleFlip (i : Fin 3) : Model :=
   SemidirectProduct.inl (Multiplicative.ofAdd (fun j => if j = i then 1 else 0))

theorem singleFlips_mem_of_nontrivial_character {C : Type*} [Group C]
    (H : Subgroup Model)
    (hsurj : Function.Surjective (quotientHom.comp H.subtype))
    (hcard : 4 ≤ Nat.card (H ⊓ core : Subgroup Model))
    (χ : H →* C) (hχ : χ ≠ 1)
    (hEven : ∀ x : H, x.val ∈ evenKernel → χ x = 1)
    (t : H) (ht : (quotientHom t.val).IsSwap) (hχt : χ t = 1) :
    ∀ i : Fin 3, singleFlip i ∈ H := by
  intro i
  apply core_le_of_nontrivial_character H hsurj hcard χ hχ hEven t ht hχt
  rfl


theorem singleFlips_mem_of_nontrivial_parity_of_mixed_flip
    (H : Subgroup Model)
    (hsurj : Function.Surjective (quotientHom.comp H.subtype))
    (g : Model) (hg : g ∈ H ⊓ core)
    (h0 : g.left.toAdd 0 = 0) (h1 : g.left.toAdd 1 = 1)
    (hParity : ((Equiv.Perm.sign.comp modelHom).comp H.subtype) ≠ 1)
    (t : H) (ht : (quotientHom t.val).IsSwap)
    (htEven : (modelHom t.val).sign = 1) :
    ∀ i : Fin 3, singleFlip i ∈ H := by
  apply singleFlips_mem_of_nontrivial_character H hsurj
    (large_kernel_of_mixed_flip H hsurj g hg h0 h1)
    ((Equiv.Perm.sign.comp modelHom).comp H.subtype) hParity ?_ t ht htEven
  intro x hx
  have hxEven : x.val ∈ evenModel := (evenKernel_eq ▸ hx).2
  exact hxEven

end Theory.SpecificGroups.SymmetricSix.SynthemeCalculation
