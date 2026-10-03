module
public import ABG.ChapterII.Section1.LargestQuaternion
public import ABG.ChapterII.Section1.NormalQuaternionCenter
public import ABG.ChapterII.Section1.SemidihedralEquiv

/-!
# The quaternion layer through an actual semidihedral embedding

Let R embed in a semidihedral group S, and let the image of A ≤ R be an
index-two generalized quaternion subgroup Y of S. The center of R lies in A
and has order two. The quaternion layer has order `2^(n+1)` for some
`n ≥ 2`. Either A is all of R, or the embedding is surjective, R itself
is semidihedral, A has index two, and there is an actual involution outside A.

The image of R contains Y, so its index divides two. In the proper case it
equals Y, giving the quaternion model and center. In the full case the
semidihedral center and normal quaternion central intersection both have
order two, proving containment. The presentation reflection lies outside Y:
otherwise it and the quaternion generator ab would put both ambient
generators in Y. Pull this reflection back through the original embedding.

This is the semidihedral local step in Alperin--Brauer--Gorenstein, II.3
Proposition 3, article p26. It uses only the index-two quaternion layer,
rather than the later Q-group vocabulary. The largest-quaternion witness
in that application supplies the index-two hypothesis. The quaternion
boundary case and the smallest semidihedral group of order sixteen remain
included.
-/

namespace ABG.QuasiDihedral

private theorem eq_of_index_two_le {S : Type*} [Group S] [Finite S]
    (Y X : Subgroup S) (hYX : Y ≤ X) (hY : Y.index = 2) (hX : X.index = 2) : Y = X := by
  apply Subgroup.eq_of_le_of_card_ge hYX
  have hy := Y.card_mul_index
  have hx := X.card_mul_index
  rw [hY] at hy
  rw [hX] at hx
  omega

public theorem embedded_quaternion_layer_data
    {S R : Type*} [Group S] [Group R] (hS : Stellmacher.IsSemidihedralGroup S)
    (f : R →* S) (hf : Function.Injective f) (Y : Subgroup S)
    (hY : IsGeneralizedQuaternionGroup Y) (hYi : Y.index = 2)
    (A : Subgroup R) (hA : A.map f = Y) :
    Subgroup.center R ≤ A ∧
      ∃ n : ℕ, 2 ≤ n ∧ Nat.card A = 2 ^ (n + 1) ∧
        Nat.card (Subgroup.center R) = 2 ∧
        (A = ⊤ ∨ (Function.Surjective f ∧ A.index = 2 ∧
          Stellmacher.IsSemidihedralGroup R ∧ ∃ a : R, a ∉ A ∧ a ^ 2 = 1)) := by
  obtain ⟨m, hm, hcard, a, b, ha, hb, hab, hgen⟩ := hS
  have hS : Stellmacher.IsSemidihedralGroup S :=
    ⟨m, hm, hcard, a, b, ha, hb, hab, hgen⟩
  let : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  let : Finite R := Finite.of_injective f hf
  have hAY : Nat.card A = Nat.card Y := by
    rw [← hA, Subgroup.card_map_of_injective hf]
  have hAc : Nat.card A = 2 ^ ((m - 2) + 1) := by
    have h := Y.card_mul_index
    rw [hYi, hcard, ← hAY, show m = (m - 1) + 1 by omega, pow_succ] at h
    have he : (m - 2) + 1 = m - 1 := by omega
    rw [he]
    omega
  have hYX : Y ≤ f.range := hA ▸ A.map_le_range f
  have hXd : f.range.index ∣ 2 := hYi ▸ Subgroup.index_dvd_of_le hYX
  rcases (Nat.dvd_prime Nat.prime_two).mp hXd with hXt | hXi
  · have hfs : Function.Surjective f := MonoidHom.range_eq_top.mp
      (Subgroup.index_eq_one.mp hXt)
    let e : R ≃* S := MulEquiv.ofBijective f ⟨hf, hfs⟩
    have hR := ABG.semidihedral_equiv e.symm hS
    have hRi : A.index = 2 := by
      have hi := Subgroup.relIndex_map_map_of_injective A ⊤ hf
      rw [Subgroup.relIndex_top_right, hA, Subgroup.map_top_of_surjective f hfs,
        Subgroup.relIndex_top_right, hYi] at hi
      exact hi.symm
    let : A.Normal := A.normal_of_index_eq_two hRi
    have hAQ : IsGeneralizedQuaternionGroup A := by
      obtain ⟨k, hk, ⟨ek⟩⟩ := hY
      exact ⟨k, hk, ⟨(Subgroup.equivMapOfInjective A f hf).trans
        ((MulEquiv.subgroupCongr hA).trans ek)⟩⟩
    have hC : Nat.card (Subgroup.center R) = 2 := card_center hR
    have hCA : Subgroup.center R ≤ A := by
      have he : A ⊓ Subgroup.center R = Subgroup.center R :=
        Subgroup.eq_of_le_of_card_ge inf_le_right
          (by rw [normal_quaternion_inf_center_card A hAQ, hC])
      rw [← he]
      exact inf_le_left
    refine ⟨hCA, m - 2, by omega, hAc, hC, Or.inr ⟨hfs, hRi, hR, ?_⟩⟩
    obtain ⟨Y₀, hY₀, hY₀i, hmax⟩ := exists_largest_quaternion hS
    have heY : Y = Y₀ := eq_of_index_two_le Y Y₀ (hmax Y hY) hYi hY₀i
    have hQmodel := (explicit_subgroup_models hm a b hcard ha hb hab hgen).2.2.2.2.2
    have hQY : Subgroup.closure ({a ^ 2, a * b} : Set S) ≤ Y := by
      rw [heY]
      exact hmax _ ⟨m - 3, by omega, hQmodel⟩
    have hbY : b ∉ Y := by
      intro hbY
      have habY : a * b ∈ Y := hQY (Subgroup.subset_closure (by simp))
      have haY : a ∈ Y := by simpa using Y.mul_mem habY (Y.inv_mem hbY)
      have htop : Y = ⊤ := top_unique (hgen ▸ (Subgroup.closure_le Y).mpr (by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl
        · exact haY
        · exact hbY))
      simp [htop] at hYi
    obtain ⟨c, hc⟩ := hfs b
    refine ⟨c, ?_, ?_⟩
    · intro hcA
      exact hbY (hc ▸ (hA ▸ Subgroup.mem_map_of_mem f hcA))
    · apply hf
      rw [map_pow, hc, map_one, ← hb]
      exact pow_orderOf_eq_one b
  · have heY : Y = f.range := eq_of_index_two_le Y f.range hYX hYi hXi
    have hAt : A = ⊤ := by
      apply Subgroup.map_injective hf
      rw [hA, heY, ← MonoidHom.range_eq_map]
    have hRQ : IsGeneralizedQuaternionGroup R := by
      obtain ⟨k, hk, ⟨ek⟩⟩ := hY
      exact ⟨k, hk, ⟨(MonoidHom.ofInjective hf).trans
        ((MulEquiv.subgroupCongr heY.symm).trans ek)⟩⟩
    have hC : Nat.card (Subgroup.center R) = 2 := by
      obtain ⟨k, hk, ⟨ek⟩⟩ := hRQ
      rw [Nat.card_congr (Subgroup.centerCongr ek).toEquiv]
      exact QuaternionGroup.card_center_of_two_le (2 ^ k)
        (by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ 2) hk)
    exact ⟨hAt ▸ le_top, m - 2, by omega, hAc, hC, Or.inl hAt⟩

end ABG.QuasiDihedral

