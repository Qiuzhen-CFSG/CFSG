module

public import BenderSuzuki.SE.Interfaces
public import BenderSuzuki.SE.Lemma312
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Borel and strong-embedding lifts

A solvable Sylow normalizer lifts through a central kernel to the actual
Sylow normalizer in its full preimage. Strong embedding lifts through an
odd kernel: involutions survive the quotient and their transporter condition
is reflected by the full preimage.

These are the quotient comparisons in Aschbacher--Smith I.8.3--I.8.5,
printed p.430. They retain the original quotient map and subgroup.
-/

namespace BenderSuzuki
open PFAppendixIII PFchapter1section1 Subgroup

/-- Central-kernel preimages of Borels are Borels. -/
public theorem IsBorelSubgroup.of_central_kernel
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    (B : Subgroup G) (hkerB : f.ker ≤ B) (hB : IsBorelSubgroup (B.map f)) :
    IsBorelSubgroup B := by
  have hcomap : (B.map f).comap f = B := comap_map_eq_self hkerB
  have hsolv : Group.IsSolvable B := by
    let : Group.IsSolvable f.ker := Group.isSolvable_of_comm (fun a b =>
      Subtype.ext (mem_center_iff.mp (hk b.property) a))
    let : Group.IsSolvable (B.map f) := hB.1
    have hs := isSolvable_comap_of_solvable_ker f (B.map f)
    rwa [hcomap] at hs
  obtain ⟨T, hT⟩ := hB.2
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective hf 2 T
  refine ⟨hsolv, S, ?_⟩
  calc
    B = (B.map f).comap f := hcomap.symm
    _ = (normalizer (S.mapSurjective hf : Set H)).comap f := congrArg (fun K => K.comap f) hT
    _ = normalizer (S : Set G) := S.normalizer_comap_of_central_kernel f hf hk

/-- Strong embedding lifts through an odd quotient with the original
subgroup equal to the full preimage of its image. -/
public theorem IsStronglyEmbedded.of_odd_quotient
    {G : Type*} [Group G] [Finite G]
    (O N : Subgroup G) [O.Normal] (hON : O ≤ N) (hodd : Odd (Nat.card O))
    (hN : IsStronglyEmbedded (N.map (QuotientGroup.mk' O))) : IsStronglyEmbedded N := by
  let q := QuotientGroup.mk' O
  have hker : q.ker ≤ N := by simpa only [q, QuotientGroup.ker_mk'] using hON
  have hcomap : (N.map q).comap q = N := comap_map_eq_self hker
  have htwo : 2 ∣ Nat.card N :=
    (even_iff_two_dvd.mp hN.card_even).trans (card_map_dvd N q)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 htwo
  have hxInv : IsInvolution (x : G) := by
    have hx' : orderOf (x : G) = 2 := by simpa only [orderOf_coe] using hx
    exact ⟨(orderOf_eq_prime_iff.mp hx').2, (orderOf_eq_prime_iff.mp hx').1⟩
  refine ⟨?_, ⟨x, x.property, hxInv⟩, ?_⟩
  · intro htop
    apply hN.ne_top
    rw [htop, map_top_of_surjective q (QuotientGroup.mk'_surjective O)]
  · intro g hg y hy hyg hyInv
    apply hN.2.2 (g := q g) (x := q y) ?_ ⟨y, hy, rfl⟩ ?_
      (IsInvolution.quotient_mk_of_odd_kernel O hodd hyInv)
    · intro hqg
      exact hg (show g ∈ N from hcomap ▸ hqg)
    · rw [← rightConjugate_map]
      exact ⟨y, hyg, rfl⟩

end BenderSuzuki
