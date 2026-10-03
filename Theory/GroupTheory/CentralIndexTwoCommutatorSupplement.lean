module
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic

/-!
# A central index-two commutator supplement

Let Z≤I≤Q≤P and E≤P, with P normalizing Q, E, I and Z. Suppose Z has
index two in I, centralizes Q, and satisfies [I,Q]=Z=[Z,E]. Then
|Q|=|Z||C_Q(I)| and Q=[Q,E]∨C_Q(I). The centralizer and commutator here
are the actual ambient subgroups; no replacement action is chosen.

Choose x in I\Z. The displacement q↦[q,x] is a homomorphism Q→G because
its values lie in the Q-central subgroup Z. The two cosets of Z in I show
that every nontrivial displacement is the same as displacement at x.
Consequently this homomorphism has image Z and kernel C_Q(I), which gives
the order formula by the first isomorphism theorem. Normalization by E
preserves the nonidentity coset in I/Z, so the displacement is E-equivariant.
It therefore maps [Q,E] onto [Z,E]=Z. Correcting each q∈Q by a preimage
in [Q,E] leaves an element of C_Q(I), proving the supplement equality.

This is the standard central translation argument used for the second-core
action in the proof of Stellmacher (9.10), Journal of Algebra 190 (1997).
The theorem is independent of that application and makes all centrality,
normalization and commutator hypotheses explicit.
-/

namespace Subgroup
open scoped commutatorElement

public theorem central_index_two_commutator_supplement
    {G : Type*} [Group G] [Finite G]
    (P Q E I Z : Subgroup G)
    (hQP : Q ≤ P) (hEP : E ≤ P) (hIQ : I ≤ Q) (hZI : Z ≤ I)
    (hindex : Z.relIndex I = 2)
    (hPQ : P ≤ normalizer (Q : Set G))
    (hPE : P ≤ normalizer (E : Set G))
    (hPI : P ≤ normalizer (I : Set G))
    (hPZ : P ≤ normalizer (Z : Set G))
    (hcentral : Z ≤ centralizer (Q : Set G))
    (hcomm : ⁅I,Q⁆ = Z) (hZE : ⁅Z,E⁆ = Z) :
    Nat.card Q = Nat.card Z * Nat.card (Q ⊓ centralizer (I : Set G) : Subgroup G) ∧
    Q = ⁅Q,E⁆ ⊔ (Q ⊓ centralizer (I : Set G)) := by
  have hnot : ¬ I ≤ Z := by
    intro hIZ
    have heq : I = Z := le_antisymm hIZ hZI
    rw [heq, relIndex_self] at hindex
    omega
  obtain ⟨x,hx,hxZ⟩ := SetLike.not_le_iff_exists.mp hnot
  have hcommX (q : G) (hq : q ∈ Q) : ⁅q,x⁆ ∈ Z := by
    rw [← hcomm, commutator_comm]
    exact commutator_mem_commutator hq hx
  let f : Q →* G := {
    toFun := fun q => ⁅(q : G),x⁆
    map_one' := by simp
    map_mul' := by
      intro q r
      change ⁅(q : G)*(r : G),x⁆ = ⁅(q : G),x⁆ * ⁅(r : G),x⁆
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hqr : (q : G) * ⁅(r : G),x⁆ = ⁅(r : G),x⁆ * q :=
        mem_centralizer_iff.mp (hcentral (hcommX r r.property)) q q.property
      have hc : ⁅(r : G),x⁆ * ⁅(q : G),x⁆ = ⁅(q : G),x⁆ * ⁅(r : G),x⁆ :=
        mem_centralizer_iff.mp (hcentral (hcommX q q.property)) _
          (hIQ (hZI (hcommX r r.property)))
      rw [hqr, mul_inv_cancel_right, hc] }
  have hvalue (q : G) (hq : q ∈ Q) (i : G) (hi : i ∈ I) (hiZ : i ∉ Z) :
      ⁅q,i⁆ = ⁅q,x⁆ := by
    have hxinv : x⁻¹*i ∈ Z :=
      (Z.subgroupOf I).mul_mem_iff_of_index_two hindex
        (a := ⟨x⁻¹,I.inv_mem hx⟩) (b := ⟨i,hi⟩) |>.mpr (by
          simp only [mem_subgroupOf,inv_mem_iff,hxZ,hiZ])
    have hzero : ⁅q,x⁻¹*i⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
      (mem_centralizer_iff.mp (hcentral hxinv) q hq)
    have hh := commutatorElement_mul_right_eq_mul_conj q x (x⁻¹*i)
    simpa only [mul_inv_cancel_left, hzero, mul_one, mul_inv_cancel_right,
      mul_inv_cancel, mul_one] using hh
  have hZrange : Z ≤ f.range := by
    rw [← hcomm, commutator_comm]
    apply commutator_le.mpr
    intro q hq i hi
    by_cases hiZ : i ∈ Z
    · have hone : ⁅q,i⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp (hcentral hiZ) q hq)
      rw [hone]
      exact f.range.one_mem
    exact ⟨⟨q,hq⟩,(hvalue q hq i hi hiZ).symm⟩
  have hrange : f.range = Z := by
    refine le_antisymm ?_ hZrange
    rintro _ ⟨q,rfl⟩
    exact hcommX q q.property
  -- The central coset contributes no commutator, and the other coset is represented by x.
  have hker (q : Q) : f q = 1 ↔ (q : G) ∈ centralizer (I : Set G) := by
    refine ⟨?_,?_⟩
    · intro hq
      apply mem_centralizer_iff.mpr
      intro i hi
      apply Eq.symm
      apply commutatorElement_eq_one_iff_mul_comm.mp
      by_cases hiZ : i ∈ Z
      · exact commutatorElement_eq_one_iff_mul_comm.mpr
          (mem_centralizer_iff.mp (hcentral hiZ) q q.property)
      · exact (hvalue q q.property i hi hiZ).trans hq
    · intro hq
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp hq x hx).symm
  have hkerMap : f.ker.map Q.subtype = Q ⊓ centralizer (I : Set G) := by
    ext q
    constructor
    · rintro ⟨r,hr,rfl⟩
      exact ⟨r.property,(hker r).mp hr⟩
    · intro hq
      exact ⟨⟨q,hq.1⟩,(hker ⟨q,hq.1⟩).mpr hq.2,rfl⟩
  have hcard : Nat.card Q = Nat.card Z *
      Nat.card (Q ⊓ centralizer (I : Set G) : Subgroup G) := by
    rw [← hkerMap, card_map_of_injective Q.subtype_injective,
      ← f.ker.index_mul_card, index_ker, hrange]
  refine ⟨hcard,?_⟩
  have hconj (e : G) (he : e ∈ E) (q : G) (hq : q ∈ Q) :
      e*q*e⁻¹ ∈ Q :=
    (mem_normalizer_iff.mp (hPQ (hEP he)) q).mp hq
  have hDle : ⁅Q,E⁆ ≤ Q ⊓ E := by
    apply commutator_le.mpr
    intro q hq e he
    constructor
    · change ⁅q,e⁆ ∈ Q
      simpa only [commutatorElement_def,mul_assoc] using
        Q.mul_mem hq (hconj e he q⁻¹ (Q.inv_mem hq))
    · change ⁅q,e⁆ ∈ E
      exact E.mul_mem
        ((mem_normalizer_iff.mp (hPE (hQP hq)) e).mp he) (E.inv_mem he)
  have hDleQ : ⁅Q,E⁆ ≤ Q := hDle.trans inf_le_left
  -- Every E-conjugate of x remains in the nonidentity coset of I/Z.
  have hequiv (q : G) (hq : q ∈ Q) (e : G) (he : e ∈ E) :
      ⁅e*q*e⁻¹,x⁆ = e*⁅q,x⁆*e⁻¹ := by
    have hxi : e⁻¹*x*e ∈ I :=
      (mem_normalizer_iff''.mp (hPI (hEP he)) x).mp hx
    have hxiZ : e⁻¹*x*e ∉ Z := by
      simpa only [← (mem_normalizer_iff''.mp (hPZ (hEP he)) x)] using hxZ
    calc
      ⁅e*q*e⁻¹,x⁆ = e*⁅q,e⁻¹*x*e⁆*e⁻¹ := by
        rw [conjugate_commutatorElement]
        simp [mul_assoc]
      _ = e*⁅q,x⁆*e⁻¹ := by rw [hvalue q hq _ hxi hxiZ]
  have hcommMap (q : G) (hq : q ∈ Q) (e : G) (he : e ∈ E) :
      f ⟨⁅q,e⁆,hDleQ (commutator_mem_commutator hq he)⟩ = ⁅f ⟨q,hq⟩,e⁆ := by
    have heq : (⟨⁅q,e⁆,hDleQ (commutator_mem_commutator hq he)⟩ : Q) =
        ⟨q,hq⟩*⟨e*q⁻¹*e⁻¹,hconj e he q⁻¹ (Q.inv_mem hq)⟩ := by
      apply Subtype.ext
      simp only [coe_mul, commutatorElement_def,mul_assoc]
    rw [heq,f.map_mul]
    change ⁅q,x⁆*⁅e*q⁻¹*e⁻¹,x⁆ = ⁅⁅q,x⁆,e⁆
    rw [hequiv q⁻¹ (Q.inv_mem hq) e he]
    have hinv : ⁅q⁻¹,x⁆ = ⁅q,x⁆⁻¹ := f.map_inv ⟨q,hq⟩
    rw [hinv]
    simp only [commutatorElement_def,mul_assoc]
  -- Equivariance and [Z,E]=Z make the commutator subgroup surject onto the image.
  have hDimage : Z ≤ (⁅Q,E⁆.subgroupOf Q).map f := by
    rw [← hZE]
    apply commutator_le.mpr
    intro z hz e he
    obtain ⟨q,hq⟩ := hZrange hz
    refine ⟨⟨⁅(q : G),e⁆,hDleQ (commutator_mem_commutator q.property he)⟩,
      commutator_mem_commutator q.property he,?_⟩
    rw [hcommMap q q.property e he, hq]
  apply le_antisymm
  · intro q hq
    obtain ⟨d,hd,heq⟩ := hDimage (hcommX q hq)
    have hk : (d : G)⁻¹*q ∈ Q ⊓ centralizer (I : Set G) := by
      refine ⟨Q.mul_mem (Q.inv_mem d.property) hq,?_⟩
      apply (hker (d⁻¹*⟨q,hq⟩)).mp
      rw [map_mul,map_inv,heq]
      exact inv_mul_cancel _
    have hmul : (d : G)*((d : G)⁻¹*q) = q := mul_inv_cancel_left _ _
    rw [← hmul]
    exact mul_mem_sup hd hk
  · exact sup_le hDleQ inf_le_left

end Subgroup
