module
public import Theory.GroupAction.RankThreeBinaryCoatomFixedCard
public import Theory.GroupTheory.CenterlessProduct
/-!
# Independence of rank-three binary fixed factors

An elementary binary group A of order eight acts on an elementary cubic
group F with trivial whole-group fixed subgroup. The fixed subgroups of
its distinct index-two subgroups form an independent family. Independence
is from the entire join of all other factors, not only pairwise disjointness.

For an index-two K, multiply the translates of each element of F over K.
This defines an endomorphism because F is abelian. Its image is K-fixed,
and it fixes every K-fixed element, since |K|=4 and F has exponent three.
It preserves every L-fixed subgroup because A is abelian. If L is another
index-two subgroup, K and L generate A; thus this endomorphism kills the
L-fixed subgroup. Its kernel contains the entire join of the other factors
and intersects the K-fixed subgroup trivially, proving independence.

This is the direct-product step after Stellmacher (8.6)(21), printed p.45.
The graph application must separately establish its whole-fixed-free input,
factor orders, generation and the number of factors.
-/

open scoped IsMulCommutative

private theorem index_two_join_eq_top
    {A : Type*} [Group A] [Finite A]
    (hcard : Nat.card A = 8) (K L : Subgroup A)
    (hK : K.index = 2) (hL : L.index = 2) (hne : K ≠ L) : K ⊔ L = ⊤ := by
  have hKcard : Nat.card K = 4 := by
    have hh := K.index_mul_card
    rw [hK,hcard] at hh
    omega
  have hLcard : Nat.card L = 4 := by
    have hh := L.index_mul_card
    rw [hL,hcard] at hh
    omega
  have hdiv : (K ⊔ L : Subgroup A).index ∣ 2 := hK ▸ Subgroup.index_dvd_of_le le_sup_left
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
  · exact Subgroup.index_eq_one.mp h
  · have hsupcard : Nat.card (K ⊔ L : Subgroup A) = 4 := by
      have hh := (K ⊔ L : Subgroup A).index_mul_card
      rw [h,hcard] at hh
      omega
    have hKeq : K = K ⊔ L := Subgroup.eq_of_le_of_card_ge le_sup_left (by omega)
    have hLeq : L = K ⊔ L := Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
    exact (hne (hKeq.trans hLeq.symm)).elim

public theorem rank_three_binary_fixed_factors_independent
    {A F : Type*} [Group A] [Finite A] [Group F] [Finite F]
    [IsElementaryAbelian 2 A] [IsElementaryAbelian 3 F] [MulDistribMulAction A F]
    (hA : Nat.card A = 8)
    (hfixed : FixedPoints.subgroup (⊤ : Subgroup A) F = ⊥) :
    iSupIndep (fun K : {K : Subgroup A // K.index = 2} => FixedPoints.subgroup K.val F) := by
  classical
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  let _ : CommGroup F := IsMulCommutative.instCommGroup
  let _ : Fintype A := Fintype.ofFinite A
  let norm (K : Subgroup A) : F →* F := {
    toFun := fun x => ∏ k : K, (k:A) • x
    map_one' := by simp
    map_mul' := by intro x y; simp only [smul_mul',Finset.prod_mul_distrib] }
  have hnormFixed (K : Subgroup A) (x : F) : norm K x ∈ FixedPoints.subgroup K F := by
    intro a
    change (a:A) • (∏ k : K, (k:A) • x) = ∏ k : K, (k:A) • x
    rw [Finset.smul_prod']
    apply Fintype.prod_equiv (Equiv.mulLeft a)
    intro k
    rw [←mul_smul]
    rfl
  have hnormId (K : Subgroup A) (hK : K.index = 2) (x : F)
      (hx : x ∈ FixedPoints.subgroup K F) : norm K x = x := by
    have hKcard : Fintype.card K = 4 := by
      have hh := K.index_mul_card
      rw [hK,hA] at hh
      rw [←Nat.card_eq_fintype_card]
      omega
    change (∏ k : K, (k:A) • x) = x
    have hpoint (k : K) : (k:A) • x = x := hx k
    simp only [hpoint,Finset.prod_const,Finset.card_univ,hKcard]
    calc
      x^4 = x^3*x := by rw [show 4=3+1 from rfl,pow_succ]
      _ = x := by rw [Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 F) x,one_mul]
  have hnormPreserve (K L : Subgroup A) (x : F) (hx : x ∈ FixedPoints.subgroup L F) :
      norm K x ∈ FixedPoints.subgroup L F := by
    intro a
    change (a:A) • (∏ k : K, (k:A) • x) = ∏ k : K, (k:A) • x
    rw [Finset.smul_prod']
    apply Finset.prod_congr rfl
    intro k _
    change (a:A) • ((k:A) • x) = (k:A) • x
    rw [←mul_smul,mul_comm (a:A),mul_smul]
    exact congrArg (fun y : F => (k:A) • y) (hx a)
  have hnormKill (K L : Subgroup A) (hK : K.index = 2) (hL : L.index = 2)
      (hne : K ≠ L) : FixedPoints.subgroup L F ≤ (norm K).ker := by
    intro x hx
    have hjoin := index_two_join_eq_top hA K L hK hL hne
    have hKfix : K ≤ MulAction.stabilizer A (norm K x) := by
      intro a ha
      exact hnormFixed K x ⟨a,ha⟩
    have hLfix : L ≤ MulAction.stabilizer A (norm K x) := by
      intro a ha
      exact hnormPreserve K L x hx ⟨a,ha⟩
    have htop : (⊤ : Subgroup A) ≤ MulAction.stabilizer A (norm K x) :=
      hjoin ▸ sup_le hKfix hLfix
    have hz : norm K x ∈ FixedPoints.subgroup (⊤ : Subgroup A) F := by
      intro a
      exact htop a.property
    rw [hfixed] at hz
    exact hz
  rw [iSupIndep_def]
  intro K
  have hle : (⨆ L : {K : Subgroup A // K.index = 2}, ⨆ (_ : L ≠ K),
      FixedPoints.subgroup L.val F) ≤ (norm K.val).ker := by
    refine iSup_le fun L => iSup_le fun hne => ?_
    exact hnormKill K.val L.val K.property L.property
      (fun h => hne (Subtype.ext h.symm))
  rw [disjoint_iff_inf_le]
  intro x hx
  exact (hnormId K.val K.property x hx.1).symm.trans (MonoidHom.mem_ker.mp (hle hx.2))
