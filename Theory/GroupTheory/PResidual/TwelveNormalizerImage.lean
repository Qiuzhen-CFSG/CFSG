module
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.NormalizerCore
public import Theory.GroupTheory.Commutator.NormalizesSupplement
public import Theory.GroupTheory.InvolutionCentralizerControl

/-! A normalizer image of index dividing twelve is forced by its four-group
and the residual of the centralizer preimage. The residual normalizes AU
because its commutators with A lie in O²(G)∩ker(f)≤U. Source:14.3.18(6). -/

public section
open Subgroup
namespace Subgroup
variable {G D:Type*} [Group G] [Finite G] [Group D] [Finite D]

theorem normalizer_image_eq_twelve_centralizer
    (f:G→*D) (hf:Function.Surjective f) (A U R:Subgroup G) [U.Normal]
    (hres:pResidual 2 G⊓f.ker≤U)
    (hjoin:normalizer ((A⊔U:Subgroup G):Set G)≤normalizer (A:Set G))
    (hR:R≤normalizer (A:Set G)) (hR4:Nat.card (R.map f)=4)
    (hA2:Nat.card (A.map f)=2)
    (hC12:Nat.card (centralizer (A.map f:Set D))=12) :
    (normalizer (A:Set G)).map f=centralizer (A.map f:Set D) := by
  let C:=centralizer (A.map f:Set D)
  let K:=C.comap f
  let L:Subgroup G:=(pResidual 2 K).map K.subtype
  let N:Subgroup D:=(normalizer (A:Set G)).map f
  have hNC:N≤C := (A.le_normalizer_map f).trans
    (normalizer_le_centralizer_of_card_two (A.map f) hA2)
  have hAK:A≤K := by
    intro a ha
    exact (normalizer_le_centralizer_of_card_two (A.map f) hA2)
      ((A.map f).le_normalizer (mem_map_of_mem f ha))
  have hAL:A≤normalizer (L:Set G) := hAK.trans (le_normalizer_embedded_pResidual 2 K)
  have hcf:⁅A,L⁆≤f.ker := by
    apply (map_eq_bot_iff _).mp
    rw [map_commutator]
    apply (commutator_eq_bot_iff_le_centralizer).mpr
    apply le_centralizer_iff.mpr
    exact (map_le_iff_le_comap).mpr (map_subtype_le (pResidual 2 K))
  have hcomm:⁅A,L⁆≤U := by
    apply le_trans (le_inf ?_ hcf) hres
    exact (le_normalizer_iff_commutator_le_right.mp hAL).trans (map_pResidual_le 2 K.subtype)
  have hLN:L≤normalizer (A:Set G) :=
    (le_normalizer_sup_of_commutator_le A L A U le_rfl hcomm).trans hjoin
  let fC:K→*C := {
    toFun:=fun x=>⟨f x,x.property⟩
    map_one':=Subtype.ext (map_one f)
    map_mul':=fun x y=>Subtype.ext (map_mul f (x:G) (y:G)) }
  have hfC:Function.Surjective fC := by
    intro c
    obtain ⟨x,hx⟩:=hf c
    exact ⟨⟨x,show f x∈C from hx ▸ c.property⟩,Subtype.ext hx⟩
  have hLf:L.map f=(pResidual 2 C).map C.subtype := by
    change ((pResidual 2 K).map K.subtype).map f=(pResidual 2 C).map C.subtype
    rw [map_map,show f.comp K.subtype=C.subtype.comp fC from rfl,←map_map,
      map_pResidual_of_surjective 2 fC hfC]
  have h3:3∣Nat.card (L.map f) := by
    rw [hLf,card_map_of_injective C.subtype_injective]
    have hcard:3∣Nat.card C := by rw [hC12];decide
    rw [←(pResidual 2 C).card_mul_index] at hcard
    apply (Nat.prime_three.dvd_mul.mp hcard).resolve_right
    obtain ⟨n,hn⟩:=(isPGroup_quotient_pResidual (G:=C) 2).exists_card_eq
    rw [index_eq_card,hn]
    exact Nat.prime_three.coprime_iff_not_dvd.mp
      (((Nat.coprime_primes Nat.prime_three Nat.prime_two).mpr (by decide)).pow_right n)
  have h3N:3∣Nat.card N := h3.trans (card_dvd_of_le (map_mono hLN))
  have h4N:4∣Nat.card N := hR4 ▸ card_dvd_of_le (map_mono (f:=f) hR)
  have h12N:12∣Nat.card N := by
    have hh:Nat.lcm 3 4∣Nat.card N := Nat.lcm_dvd h3N h4N
    exact (show Nat.lcm 3 4=12 by decide) ▸ hh
  apply eq_of_le_of_card_ge hNC
  rw [hC12]
  exact Nat.le_of_dvd (Nat.card_pos) h12N
end Subgroup
