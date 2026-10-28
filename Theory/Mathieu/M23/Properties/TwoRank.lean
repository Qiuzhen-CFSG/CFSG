module

public import Theory.Mathieu.M23.QuasithinGeometry.ElementarySylow.Checks
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Intrinsic two-rank bounds for M₂₃

The certified Sylow group has two elementary subgroups of order sixteen.
Every other involution has at most twelve commuting square-one elements.
Thus an elementary subgroup larger than sixteen would lie in the union
of the two candidates, hence in one candidate, a contradiction. Sylow
conjugacy proves the global bound. Every automorphism of native M₂₃ is
inner, so its automorphism group has the same bound.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.3,
printed p.348; the concrete Sylow calculations also underlie H.14.2(1).
-/

@[expose] public section
namespace Sporadic.Mathieu
namespace M23Geometry.ElementarySylow
open FusionCertificate

private theorem exceptional_card_bound (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hAS : A ≤ subgroup)
    (k : Fin 8) (g : A) (hg : (g.val : Equiv.Perm (Fin 23)) = perm (exceptionalIndex k)) :
    Nat.card A ≤ 12 := by
  have witnesses (a : A) : ∃ j, (a.val : Equiv.Perm (Fin 23)) = perm (commutingIndex k j) := by
    obtain ⟨i, hi⟩ := exists_perm ⟨a.val.val, hAS a.property⟩
    have hs : ∀ x, pointTable i (pointTable i x) = x := by
      have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hA.exponent_dvd_p a
      have he := congrArg (fun z : A => (z.val : Equiv.Perm (Fin 23))) hp
      rw [pow_two] at he
      change a.val.val * a.val.val = 1 at he
      rw [← hi] at he
      exact fun x => Equiv.congr_fun he x
    have hc : ∀ x, pointTable (exceptionalIndex k) (pointTable i x) =
        pointTable i (pointTable (exceptionalIndex k) x) := by
      have he := congrArg (fun z : A => (z.val : Equiv.Perm (Fin 23)))
        (hA.toIsMulCommutative.is_comm.comm g a)
      change g.val.val * a.val.val = a.val.val * g.val.val at he
      rw [hg, ← hi] at he
      exact fun x => Equiv.congr_fun he x
    obtain ⟨j, rfl⟩ := exceptional_commuting k i hs hc
    exact ⟨j, hi.symm⟩
  classical
  let f : A → Fin 12 := fun a => (witnesses a).choose
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact ((witnesses a).choose_spec.trans (congrArg (fun j => perm (commutingIndex k j)) hab)).trans
      (witnesses b).choose_spec.symm
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- Every elementary subgroup of the literal Sylow group has order at most sixteen. -/
theorem elementary_card_le_sixteen (A : Subgroup M23)
    (hA : IsElementaryAbelian 2 A) (hAS : A ≤ subgroup) : Nat.card A ≤ 16 := by
  by_contra hlarge
  have hcover : (A : Set M23) ⊆ (candidate 0 : Set M23) ∪ candidate 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := exists_perm ⟨a.val, hAS ha⟩
    have hs : ∀ x, pointTable i (pointTable i x) = x := by
      let _ := hA
      have he := congrArg (fun z : M23 => (z : Equiv.Perm (Fin 23)))
        (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha)
      rw [pow_two] at he
      change a.val * a.val = 1 at he
      rw [← hi] at he
      exact fun x => Equiv.congr_fun he x
    rcases square_cases i hs with ⟨b, j, rfl⟩ | ⟨k, rfl⟩
    · fin_cases b
      · exact Or.inl ⟨j, hi⟩
      · exact Or.inr ⟨j, hi⟩
    · have hb := exceptional_card_bound A hA hAS k ⟨a, ha⟩ hi.symm
      omega
  rcases SubgroupClass.subset_union.mp hcover with h | h
  · exact hlarge ((Subgroup.card_le_of_le h).trans_eq (candidate_card 0))
  · exact hlarge ((Subgroup.card_le_of_le h).trans_eq (candidate_card 1))

end M23Geometry.ElementarySylow

/-- The two-rank of native M₂₃ is at most four. -/
theorem m23_twoRank_le_four : primeRank 2 M23 ≤ 4 := by
  rw [M23Geometry.FusionCertificate.sylow.primeRank_eq]
  change primeRank 2 M23Geometry.FusionCertificate.subgroup ≤ 4
  apply (primeRank_le_iff_elementary_card_le _).mpr
  intro E hE
  let _ := hE
  have h := M23Geometry.ElementarySylow.elementary_card_le_sixteen
    (E.map M23Geometry.FusionCertificate.subgroup.subtype)
    IsElementaryAbelian.map_subtype (by
      rintro _ ⟨x, _, rfl⟩
      exact x.property)
  rw [Subgroup.card_map_of_injective Subtype.val_injective] at h
  exact h

/-- The full abstract automorphism group of native M₂₃ has two-rank at most four. -/
theorem m23_automorphism_twoRank_le_four : primeRank 2 (MulAut M23) ≤ 4 := by
  have hf : Function.Injective (MulAut.conj : M23 →* MulAut M23) := by
    rw [← MonoidHom.ker_eq_bot_iff]
    apply (MulAut.conj : M23 →* MulAut M23).ker.eq_bot_iff_forall.mpr
    intro x hx
    have hc : x ∈ Subgroup.center M23 := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := MulEquiv.congr_fun (show MulAut.conj x = 1 from hx) y
      change x * y * x⁻¹ = y at hy
      exact (mul_inv_eq_iff_eq_mul.mp hy).symm
    simpa only [M23Geometry.m23_center_eq_bot, Subgroup.mem_bot] using hc
  let e : M23 ≃* MulAut M23 := MulEquiv.ofBijective MulAut.conj
    ⟨hf, m23_conj_surjective⟩
  rw [← Theory.GroupTheory.primeRank_equiv 2 e]
  exact m23_twoRank_le_four

end Sporadic.Mathieu
