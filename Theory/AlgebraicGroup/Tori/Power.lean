module

public import Theory.AlgebraicGroup.Connected
public import Theory.AlgebraicGroup.Tori.Basic

universe u

/-! Power maps and connectedness of diagonal algebraic groups and tori. -/

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

private lemma units_pow_surjective_of_isAlgClosed (m : ℕ) (hm : 0 < m) :
    Function.Surjective (fun z : kˣ ↦ z ^ m) := by
  intro x
  obtain ⟨z, hzpow⟩ := IsAlgClosed.exists_pow_nat_eq (x : k) hm
  have hz : z ≠ 0 := by
    intro hzero
    subst z
    exact Units.ne_zero x (by simpa [hm.ne'] using hzpow.symm)
  refine ⟨Units.mk0 z hz, ?_⟩
  apply Units.ext
  exact hzpow

/-- Every nonzero integral power map on `kˣ` is surjective over an
algebraically closed field. -/
public lemma units_zpow_surjective_of_isAlgClosed (z : ℤ) (hz : z ≠ 0) :
    Function.Surjective (fun x : kˣ ↦ x ^ z) := by
  cases z with
  | ofNat n =>
      have hn : 0 < n := Nat.pos_of_ne_zero (by simpa using hz)
      simpa using units_pow_surjective_of_isAlgClosed (k := k) n hn
  | negSucc n =>
      intro y
      obtain ⟨x, hx⟩ :=
        units_pow_surjective_of_isAlgClosed (k := k) (n + 1)
          (Nat.succ_pos n) y⁻¹
      refine ⟨x, ?_⟩
      change x ^ Int.negSucc n = y
      change x ^ (n + 1) = y⁻¹ at hx
      rw [zpow_negSucc, hx, inv_inv]

/-- Every positive power map on `D_n(k)` is surjective. -/
public lemma dVariety_pow_surjective (n m : ℕ) (hm : 0 < m) :
    Function.Surjective
      (fun x : Variety.Point (dVariety k n) ↦ x ^ m) := by
  intro x
  choose y hy using fun i : Fin n ↦
    units_pow_surjective_of_isAlgClosed m hm (dPointEquiv n x i)
  refine ⟨(dPointEquiv n).symm y, ?_⟩
  apply (dPointEquiv n).injective
  rw [dPointEquiv_pow, (dPointEquiv n).apply_symm_apply]
  exact funext hy

/-- In characteristic `p`, the `p ^ n`-power map on a torus is bijective on
rational points. -/
public theorem IsTorus.pow_primePower_bijective
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T)
    (p n : ℕ) [CharP k p] [Fact p.Prime] :
    Function.Bijective (fun x : Variety.Point T ↦ x ^ p ^ n) := by
  rcases hT with ⟨d, ⟨e⟩⟩
  constructor
  · intro x y hxy
    apply e.toMulEquiv.symm.injective
    apply (dPointEquiv d).injective
    have hd : e.toMulEquiv.symm x ^ p ^ n =
        e.toMulEquiv.symm y ^ p ^ n := by
      simpa only [map_pow] using congrArg e.toMulEquiv.symm hxy
    have hd' := congrArg (dPointEquiv d) hd
    rw [dPointEquiv_pow, dPointEquiv_pow] at hd'
    funext i
    apply (show Function.Injective (fun z : kˣ ↦ z ^ p ^ n) by
      intro a b hab
      apply Units.ext
      apply (frobenius_inj k p).iterate n
      have hval := congrArg (Units.coeHom k) hab
      rw [map_pow, map_pow] at hval
      change ((a : k) ^ p ^ n) = ((b : k) ^ p ^ n) at hval
      simpa only [iterate_frobenius] using hval)
    exact congrFun hd' i
  · intro y
    obtain ⟨x, hx⟩ := dVariety_pow_surjective d (p ^ n)
      (pow_pos (Nat.Prime.pos (Fact.out : p.Prime)) n)
      (e.toMulEquiv.symm y)
    refine ⟨e.toMulEquiv x, ?_⟩
    simpa only [map_pow, e.toMulEquiv.apply_symm_apply] using
      congrArg e.toMulEquiv hx

/-- The standard diagonal algebraic group `D_n` is connected. -/
public theorem dVariety_isConnected (n : ℕ) :
    Variety.IsConnected (dVariety k n) := by
  apply (identityComponent_eq_univ_iff_isConnected (dVariety k n)).mp
  apply Set.eq_univ_of_univ_subset
  intro x _hx
  let H := AlgebraicGroup.identityComponentSubgroup (dVariety k n)
  let : H.FiniteIndex := by
    dsimp [H]
    infer_instance
  let : H.Normal := by
    simpa [H, AlgebraicGroup.identityComponentClosedSubgroup_carrier] using
      (AlgebraicGroup.identityComponentClosedSubgroup_isNormal (dVariety k n))
  rcases dVariety_pow_surjective n H.index
      (Nat.pos_of_ne_zero (inferInstance : H.FiniteIndex).index_ne_zero) x with
    ⟨y, hy⟩
  change x ∈ H
  rw [← hy]
  exact H.pow_index_mem y

/-- Every torus is connected. -/
public theorem IsTorus.isConnected
    {T : Variety k} [AlgebraicGroup T] (hT : IsTorus T) :
    Variety.IsConnected T := by
  rcases hT with ⟨n, ⟨e⟩⟩
  exact (algebraicGroupIso_isConnected_iff e).mp (dVariety_isConnected n)

/-- Every subtorus is connected. -/
public lemma IsSubtorus.isConnected
    {G : Variety k} [AlgebraicGroup G]
    {T : ClosedSubgroup G} (hT : IsSubtorus T) :
    Variety.IsConnected T.carrierVariety :=
  IsTorus.isConnected hT

end Theory.AlgebraicGroup
