module
public import Theory.GroupTheory.PairedInvolutiveExtension.Fusion
public import Theory.GroupTheory.PairedInvolutiveExtension.Centralizers
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Mathlib.Tactic.NormNum

/-!
# Marked local geometry of the paired binary linear model

The two natural actor kernels have index two. The paired-factor fusion
formulas give their marked three-class involution covers. Centralizer orders
168·4 and 6²·4, compared with the paired Sylow order 8²·4, give the extremal
centralizer bound by divisibility. The interchange centralizer has the marked
four-class cover needed for the final transfer contradiction.

The hypotheses refer to a literal involutive action and its stable subgroup;
there is no assumed class-cover record. Source: Aschbacher--Smith, proof of
2.4.34, printed p.548 of the 1 March 2004 manuscript.
-/

@[expose] public section
namespace Theory.GroupTheory.PairedInvolutiveExtension
open Subgroup
variable {K : Type*} [Group K] (α : MulAut K) (hα : Function.Involutive α)
instance [Finite K] : Finite (Model α hα) :=
  Finite.of_equiv ((K × K) × (Bit × Bit)) SemidirectProduct.equivProd.symm
variable (D : Subgroup K) (hD : ∀ a ∈ D, α a ∈ D)

abbrev PairedSubgroup := subgroup α hα D hD

def graphIn : PairedSubgroup α hα D hD := ⟨graph α hα, D.one_mem, D.one_mem⟩
def swapIn : PairedSubgroup α hα D hD := ⟨swap α hα, D.one_mem, D.one_mem⟩
def graphSwapIn : PairedSubgroup α hα D hD := ⟨graphSwap α hα, D.one_mem, D.one_mem⟩
def diagonalIn (t : K) (ht : t∈D) : PairedSubgroup α hα D hD := ⟨base α hα t t,ht,ht⟩
def pureIn (t : K) (ht : t∈D) : PairedSubgroup α hα D hD := ⟨base α hα 1 t,D.one_mem,ht⟩

def firstBit : PairedSubgroup α hα D hD →* Bit :=
  (MonoidHom.fst Bit Bit).comp (SemidirectProduct.rightHom.comp (subgroup α hα D hD).subtype)
def differenceBit : PairedSubgroup α hα D hD →* Bit :=
  ((MonoidHom.fst Bit Bit)*(MonoidHom.snd Bit Bit)).comp
    (SemidirectProduct.rightHom.comp (subgroup α hα D hD).subtype)

theorem firstBit_surjective : Function.Surjective (firstBit α hα D hD) := by
  intro p
  refine ⟨⟨mk α hα 1 1 p 1,D.one_mem,D.one_mem⟩,rfl⟩
theorem differenceBit_surjective : Function.Surjective (differenceBit α hα D hD) := by
  intro p
  refine ⟨⟨mk α hα 1 1 p 1,D.one_mem,D.one_mem⟩,?_⟩
  change p*1=p
  exact mul_one p

theorem index_firstBit_ker : (firstBit α hα D hD).ker.index=2 := by
  rw [index_ker, MonoidHom.range_eq_top.mpr (firstBit_surjective α hα D hD), card_top, card_bit]
theorem index_differenceBit_ker : (differenceBit α hα D hD).ker.index=2 := by
  rw [index_ker, MonoidHom.range_eq_top.mpr (differenceBit_surjective α hα D hD), card_top, card_bit]

theorem mem_firstBit_ker (u : PairedSubgroup α hα D hD) :
    u ∈ (firstBit α hα D hD).ker ↔ u.val.right.1=1 := Iff.rfl

theorem mem_differenceBit_ker (u : PairedSubgroup α hα D hD) :
    u ∈ (differenceBit α hα D hD).ker ↔ u.val.right.1=u.val.right.2 := by
  change u.val.right.1*u.val.right.2=1 ↔ _
  rcases bit_cases u.val.right.1 with h|h <;> rcases bit_cases u.val.right.2 with h'|h' <;>
    simp [h,h',eq_comm]

private def centralizerInEquiv {G : Type*} [Group G] (H : Subgroup G) (j : H) :
    centralizer ({j} : Set H) ≃ (H ⊓ centralizer ({(j : G)} : Set G) : Subgroup G) where
  toFun u := ⟨u.val.val,u.val.property,mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp u.property))⟩
  invFun u := ⟨⟨u.val,u.property.1⟩,mem_centralizer_singleton_iff.mpr
    (Subtype.ext (mem_centralizer_singleton_iff.mp u.property.2))⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_centralizer_swapIn :
    Nat.card (centralizer ({swapIn α hα D hD} : Set (PairedSubgroup α hα D hD))) = Nat.card D*4 := by
  rw [Nat.card_congr (centralizerInEquiv _ _)]
  exact card_subgroup_inf_centralizer_swap α hα D hD

theorem centralizer_le_swap_of_outer_conjugate [Finite K]
    (hK : Nat.card K=168) (hfix : Nat.card α.fixedSubgroup=6) (hcardD : Nat.card D=8)
    (u : PairedSubgroup α hα D hD)
    (hc : IsConj u.val (graph α hα) ∨ IsConj u.val (swap α hα) ∨
      IsConj u.val (graphSwap α hα)) :
    Nat.card (centralizer ({u} : Set (PairedSubgroup α hα D hD))) ≤
      Nat.card (centralizer ({swapIn α hα D hD} : Set (PairedSubgroup α hα D hD))) := by
  rw [card_centralizer_swapIn, hcardD]
  have h256 : Nat.card (centralizer ({u} : Set (PairedSubgroup α hα D hD))) ∣ 256 := by
    have h := (centralizer ({u} : Set (PairedSubgroup α hα D hD))).card_subgroup_dvd_card
    change Nat.card (centralizer ({u} : Set (PairedSubgroup α hα D hD))) ∣
      Nat.card (subgroup α hα D hD) at h
    rw [card_subgroup,hcardD] at h
    exact h
  have hfull : Nat.card (centralizer ({u} : Set (PairedSubgroup α hα D hD))) ∣
      Nat.card (centralizer ({u.val} : Set (Model α hα))) := by
    rw [Nat.card_congr (centralizerInEquiv _ _)]
    exact card_dvd_of_le inf_le_right
  rcases hc with hc|hc|hc
  · rw [card_centralizer_eq_of_isConj _ _ hc,card_centralizer_graph,hfix] at hfull
    have hd := Nat.dvd_gcd h256 hfull
    have hle := Nat.le_of_dvd (by decide : 0 < Nat.gcd 256 (6^2*4)) hd
    exact hle.trans (by decide)
  · rw [card_centralizer_eq_of_isConj _ _ hc,card_centralizer_swap,hK] at hfull
    have hd := Nat.dvd_gcd h256 hfull
    exact Nat.le_of_dvd (by decide : 0 < Nat.gcd 256 (168*4)) hd
  · rw [card_centralizer_eq_of_isConj _ _ hc,card_centralizer_graphSwap,hK] at hfull
    have hd := Nat.dvd_gcd h256 hfull
    exact Nat.le_of_dvd (by decide : 0 < Nat.gcd 256 (168*4)) hd

variable (t : K) (ht : t∈D)
variable (hclass : ∀ a : K, a^2=1 → a≠1 → IsConj a t)
variable (hcocycle : ∀ a : K, a*α a=1 → ∃ b : K,b*a*(α b)⁻¹=1)
include hclass in
theorem first_kernel_cover (u : PairedSubgroup α hα D hD)
    (hu : u ∈ (firstBit α hα D hD).ker) (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨
      IsConj (pureIn α hα D hD t ht).val u.val ∨ IsConj (swapIn α hα D hD).val u.val := by
  have hu2 : u.val^2=1 := by simpa only [hord] using pow_orderOf_eq_one u.val
  have hne : u.val≠1 := by intro he; simp [he] at hord
  exact (first_kernel_fusion α hα t hclass u.val hu hu2 hne).imp IsConj.symm
    (Or.imp IsConj.symm IsConj.symm)

include hclass in
theorem equal_bits_cover (u : PairedSubgroup α hα D hD)
    (hu : u ∈ (differenceBit α hα D hD).ker) (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨
      IsConj (pureIn α hα D hD t ht).val u.val ∨ IsConj (graphSwapIn α hα D hD).val u.val := by
  have hu2 : u.val^2=1 := by simpa only [hord] using pow_orderOf_eq_one u.val
  have hne : u.val≠1 := by intro he; simp [he] at hord
  exact (equal_bits_fusion α hα t hclass u.val
    ((mem_differenceBit_ker α hα D hD u).mp hu) hu2 hne).imp IsConj.symm
      (Or.imp IsConj.symm IsConj.symm)

include hclass hcocycle in
theorem centralizer_class_bound [Finite K] (hK : Nat.card K=168) (hfix : Nat.card α.fixedSubgroup=6)
    (hcardD : Nat.card D=8) (u : PairedSubgroup α hα D hD) (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨ IsConj (pureIn α hα D hD t ht).val u.val ∨
      Nat.card (centralizer ({u} : Set (PairedSubgroup α hα D hD))) ≤
        Nat.card (centralizer ({swapIn α hα D hD} : Set (PairedSubgroup α hα D hD))) := by
  have hu2 : u.val^2=1 := by simpa only [hord] using pow_orderOf_eq_one u.val
  have hne : u.val≠1 := by intro he; simp [he] at hord
  rcases involution_fusion α hα t hclass hcocycle u.val hu2 hne with hz|hp|ho
  · exact Or.inl hz.symm
  · exact Or.inr (Or.inl hp.symm)
  · exact Or.inr (Or.inr (centralizer_le_swap_of_outer_conjugate α hα D hD hK hfix hcardD u ho))

include hclass hcocycle in
theorem swap_centralizer_cover (u : PairedSubgroup α hα D hD)
    (hu : u ∈ centralizer ({swapIn α hα D hD} : Set (PairedSubgroup α hα D hD)))
    (hord : orderOf u.val=2) :
    IsConj (diagonalIn α hα D hD t ht).val u.val ∨ IsConj (graphIn α hα D hD).val u.val ∨
      IsConj (swapIn α hα D hD).val u.val ∨ IsConj (graphSwapIn α hα D hD).val u.val := by
  have hu2 : u.val^2=1 := by simpa only [hord] using pow_orderOf_eq_one u.val
  have hne : u.val≠1 := by intro he; simp [he] at hord
  have hcomm : Commute u.val (swap α hα) :=
    congrArg Subtype.val (mem_centralizer_singleton_iff.mp hu)
  exact (swap_centralizer_fusion α hα t hclass hcocycle u.val hcomm hu2 hne).imp IsConj.symm
    (Or.imp IsConj.symm (Or.imp IsConj.symm IsConj.symm))

end Theory.GroupTheory.PairedInvolutiveExtension
