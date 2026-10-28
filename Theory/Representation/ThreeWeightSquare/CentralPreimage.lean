module
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.Representation.GeneralLinearThreeLargePrime
/-!
# Central preimages in a cross-characteristic degree-three action

The preimage of a p-group under a central quotient is its p-core times the
central kernel. Its p-core is abelian by the faithful degree-three bound
for p>3, and hence the entire preimage is abelian. The cardinality identity
also retains the cross-characteristic hypothesis through the quotient.
Source: lifting the odd degree-three actor in Aschbacher–Smith A.3.15.
-/
public section
noncomputable section
namespace Representation.ThreeWeightSquare
open Subgroup
open scoped IsMulCommutative
variable {F G H : Type*} [Field F] [Finite F] [Group G] [Finite G] [Group H]
variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime] [CharP F q]

/-- A central cover of a p-group in GL₃ is abelian when p>3 is nondefining. -/
theorem central_preimage_abelian (hp : 3<p) (hpq : p≠q)
    (j : G→*GL (Fin 3) F) (hj : Function.Injective j)
    (f : G→*H) (hf : Function.Surjective f) (hk : f.ker≤center G)
    (hH : IsPGroup p H) : IsMulCommutative G := by
  have htop : pCore p H=⊤ := top_unique (le_sSup ⟨inferInstance,hH.to_subgroup ⊤⟩)
  have hgen : pCore p G⊔f.ker=⊤ := by
    rw [← f.comap_pCore_of_central_kernel hf hk,htop,comap_top]
  have hab := generalLinear_three_large_prime_abelian hp hpq
    ((pCore p G).map j) (pCore_isPGroup.map j)
  let _ := hab
  have hPP (a b:G) (ha:a∈pCore p G) (hb:b∈pCore p G) : a*b=b*a := by
    apply hj
    rw [map_mul,map_mul]
    exact congrArg Subtype.val (mul_comm (⟨j a,mem_map_of_mem j ha⟩:(pCore p G).map j)
      ⟨j b,mem_map_of_mem j hb⟩)
  have hpc : pCore p G≤center G := by
    intro a ha
    apply mem_center_iff.mpr
    intro x
    have hle : pCore p G⊔f.ker≤centralizer {a} := by
      apply sup_le
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr (hPP b a hb ha)
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr ((mem_center_iff.mp (hk hb) a).symm)
    rw [hgen] at hle
    exact mem_centralizer_singleton_iff.mp (hle (mem_top x))
  have hc : (⊤ : Subgroup G)≤center G := hgen ▸ sup_le hpc hk
  exact IsMulCommutative.of_comm fun a b=>(mem_center_iff.mp (hc (mem_top b)) a)

omit [Finite F] in
/-- Cross-characteristic order is retained in a central preimage. -/
theorem central_preimage_order (hpq : p≠q)
    (f : G→*H) (hf : Function.Surjective f)
    (hk : (Nat.card f.ker:F)≠0) (hH : IsPGroup p H) : (Nat.card G:F)≠0 := by
  let _ : Finite H := Finite.of_surjective f hf
  have hc := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv] at hc
  rw [hc,Nat.cast_mul]
  apply mul_ne_zero ?_ hk
  obtain ⟨n,hn⟩ := hH.exists_card_eq
  rw [hn,Nat.cast_pow]
  apply pow_ne_zero
  intro he
  have hd := (CharP.cast_eq_zero_iff F q p).mp he
  exact hpq (((Nat.dvd_prime (Fact.out:p.Prime)).mp hd).resolve_left (Fact.out:q.Prime).ne_one).symm
end Representation.ThreeWeightSquare
