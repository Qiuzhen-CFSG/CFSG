module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Weak closure descends through quotient maps

A weakly closed subgroup J of a Sylow p-subgroup S of a finite group
has weakly closed image in q(S) under every surjective homomorphism q.
There is no restriction on the kernel.

Lift a quotient conjugator g and work inside K=q⁻¹(q(S)). Its conjugate
of J is a p-subgroup of K, and S is a Sylow subgroup of K. Sylow conjugacy
therefore supplies k in K sending that conjugate into S. Weak closure makes
kg normalize J. Since weak closure also implies that S normalizes J,
q(k) normalizes q(J); cancellation gives the same for q(g).

This is the quotient subgroup-control step used in the Frattini argument
of Stellmacher (2.2), Journal of Algebra 190 (1997), p.20. The theorem itself
uses only finite-group and Sylow theory and is independent of that campaign.
-/

open scoped Pointwise
open MulAction

private theorem exists_conjugate_le_sylow_in_subgroup
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (K P : Subgroup G) (hSK : (S : Subgroup G) ≤ K)
    (hPK : P ≤ K) (hP : IsPGroup p P) :
    ∃ k : K, P.map (MulAut.conj (k : G)).toMonoidHom ≤ (S : Subgroup G) := by
  have hPKp : IsPGroup p (P.subgroupOf K) :=
    hP.comap_of_injective K.subtype K.subtype_injective
  obtain ⟨T, hPT⟩ := hPKp.exists_le_sylow
  obtain ⟨k, hk⟩ := exists_smul_eq K T (S.subtype hSK)
  refine ⟨k, ?_⟩
  rintro x ⟨y, hy, rfl⟩
  have hyT : (⟨y, hPK hy⟩ : K) ∈ (T : Subgroup K) := hPT hy
  have hm : k * (⟨y, hPK hy⟩ : K) * k⁻¹ ∈ (S.subtype hSK : Subgroup K) := by
    rw [← hk]
    exact Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hyT
  exact hm

public theorem weakly_closed_map_of_surjective
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) (J : Subgroup G)
    (hJS : J ≤ (S : Subgroup G))
    (hweak : ∀ g : G, J.map (MulAut.conj g).toMonoidHom ≤ (S : Subgroup G) →
      J.map (MulAut.conj g).toMonoidHom = J)
    (q : G →* H) (hq : Function.Surjective q) (b : H)
    (hb : (J.map q).map (MulAut.conj b).toMonoidHom ≤ (S : Subgroup G).map q) :
    (J.map q).map (MulAut.conj b).toMonoidHom = J.map q := by
  obtain ⟨g, rfl⟩ := hq b
  have hSnorm : (S : Subgroup G) ≤ Subgroup.normalizer J := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply hweak
    rintro x ⟨j, hj, rfl⟩
    exact (S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hs (hJS hj)) ((S : Subgroup G).inv_mem hs)
  let K : Subgroup G := ((S : Subgroup G).map q).comap q
  let P : Subgroup G := J.map (MulAut.conj g).toMonoidHom
  have hSK : (S : Subgroup G) ≤ K := fun s hs => Subgroup.mem_map_of_mem q hs
  have hPK : P ≤ K := by
    rintro x ⟨j, hj, rfl⟩
    have hm := hb (Subgroup.mem_map_of_mem (MulAut.conj (q g)).toMonoidHom
      (Subgroup.mem_map_of_mem q hj))
    simpa [K, MulAut.conj_apply] using hm
  have hP : IsPGroup p P := (S.isPGroup'.to_le hJS).map _
  obtain ⟨k, hk⟩ := exists_conjugate_le_sylow_in_subgroup S K P hSK hPK hP
  have hkg : k.val * g ∈ Subgroup.normalizer J := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply hweak
    rintro x ⟨j, hj, rfl⟩
    have hm := hk (Subgroup.mem_map_of_mem (MulAut.conj (k : G)).toMonoidHom
      (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hj))
    simpa [MulAut.conj_apply, mul_assoc] using hm
  have hqk : q k ∈ Subgroup.normalizer (J.map q) := by
    have hkn : q k ∈ ((S : Subgroup G).map q) := k.property
    exact (Subgroup.le_normalizer_map q)
      ((Subgroup.map_mono hSnorm) hkn)
  have hqkg : q k * q g ∈ Subgroup.normalizer (J.map q) := by
    simpa using (Subgroup.le_normalizer_map q) (Subgroup.mem_map_of_mem q hkg)
  have hqg : q g ∈ Subgroup.normalizer (J.map q) := by
    simpa [mul_assoc] using (Subgroup.normalizer (J.map q : Set H)).mul_mem
      ((Subgroup.normalizer (J.map q : Set H)).inv_mem hqk) hqkg
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hqg
