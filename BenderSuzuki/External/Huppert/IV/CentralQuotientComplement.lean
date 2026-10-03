module

public import BenderSuzuki.External.Huppert.IV.ComplementTransfer

/-!
# Lifting normal complements through central quotients

A finite group has a normal p-complement if its quotient by a central
subgroup does. Pull back the normal p-complement of the quotient. Every
p-element of this inverse image lies in the central kernel, so Burnside
transfer gives a normal p-complement of the inverse image. The remaining
quotient is a p-group, and the normal-subgroup extension theorem finishes.

This is the lifting step used in Lyons, *A Characterization of the Group
U₃(4)* (1972), Lemma 1, pp. 372–373.
-/

namespace BenderSuzuki.External

/-- Normal p-complements lift through central kernels, without a restriction
on the order of the kernel. -/
public theorem hasNormalPComplement_of_central_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (N : Subgroup G) [N.Normal] (hN : N ≤ Subgroup.center G)
    (hquot : HasNormalPComplement p (G ⧸ N)) : HasNormalPComplement p G := by
  classical
  obtain ⟨M, hM, hcop, hMp⟩ := hquot
  let := hM
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let L : Subgroup G := M.comap q
  let : L.Normal := hM.comap q
  let f : G →* (G ⧸ N) ⧸ M := (QuotientGroup.mk' M).comp q
  have hf : Function.Surjective f :=
    (QuotientGroup.mk'_surjective M).comp (QuotientGroup.mk'_surjective N)
  have hker : f.ker = L := by
    ext x
    exact QuotientGroup.eq_one_iff (N := M) (q x)
  have hLp : IsPGroup p (G ⧸ L) := by
    exact (hMp.of_equiv (QuotientGroup.quotientKerEquivOfSurjective f hf).symm).of_equiv
      (QuotientGroup.quotientMulEquivOfEq hker)
  apply hkt_hasNormalPComplement_of_normal_subgroup_and_pgroup_quotient L hLp
  let P : Sylow p L := Classical.choice inferInstance
  apply hkt_hasNormalPComplement_of_sylow_le_center_normalizer P
  intro x hx
  have hxN : (x : G) ∈ N := by
    let xP : P := ⟨x, hx⟩
    let xM : M := ⟨q x, x.property⟩
    have hdiv : orderOf xM ∣ orderOf xP := by
      rw [← Subgroup.orderOf_coe xM, ← Subgroup.orderOf_coe xP]
      change orderOf (q (x : G)) ∣ orderOf x
      rw [← Subgroup.orderOf_coe x]
      exact orderOf_map_dvd q (x : G)
    have hxCop : Nat.Coprime (orderOf xP) (Nat.card M) :=
      P.isPGroup'.orderOf_coprime hcop xP
    have hxOne : xM = 1 := orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes hxCop hdiv (orderOf_dvd_natCard xM))
    exact (QuotientGroup.eq_one_iff (N := N) (x : G)).mp
      (congrArg Subtype.val hxOne)
  refine ⟨(P : Subgroup L).le_normalizer hx, ?_⟩
  intro y _hy
  apply Subtype.ext
  exact Subgroup.mem_center_iff.mp (hN hxN) (y : G)

end BenderSuzuki.External
