module
public import Theory.PGroupCore
public import Theory.PGroup
public import Mathlib.GroupTheory.Sylow

/-!
# A maximal Sylow subgroup controls homomorphism kernels

In a finite group with trivial two-core and a maximal Sylow two-subgroup,
a homomorphism is injective whenever an odd-order subgroup has nontrivial
image. The target is also assumed finite, as in the intended action images.

The join of the normal kernel and the Sylow subgroup is either the Sylow
subgroup or the whole group. In the first case the kernel is a normal
two-subgroup and hence trivial. In the second case the whole image is a
two-group, contradicting the retained nontrivial odd-order image.

This elementary maximal-subgroup argument is used to identify the faithful
chief action in Stellmacher (9.1)(10), Journal of Algebra190 (1997), p.47.
It is independent of the graph context and representation dimension.
-/

namespace MonoidHom
public theorem injective_of_coatom_sylow_of_nontrivial_odd_image
    {X Y : Type*} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (S : Sylow 2 X) (hS : IsCoatom (S : Subgroup X))
    (hcore : pCore 2 X = ⊥) (F : Subgroup X) (hodd : Odd (Nat.card F))
    (hne : F.map f ≠ ⊥) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases hS.le_iff.mp (show (S : Subgroup X) ≤ f.ker ⊔ (S : Subgroup X) from le_sup_right)
    with htop | heq
  · have hrange : f.range = (S : Subgroup X).map f := by
      apply le_antisymm ?_ (Subgroup.map_le_range _ _)
      rintro element ⟨x, rfl⟩
      have hx : x ∈ f.ker ⊔ (S : Subgroup X) := by rw [htop]; trivial
      obtain ⟨k, hk, s, hs, hks⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      refine ⟨s, hs, ?_⟩
      rw [← hks, map_mul, MonoidHom.mem_ker.mp hk, one_mul]
    have hFp : IsPGroup 2 (F.map f) :=
      (hrange ▸ S.isPGroup'.map f).to_le (Subgroup.map_le_range _ _)
    have hFodd : Odd (Nat.card (F.map f)) :=
      hodd.of_dvd_nat (Subgroup.card_map_dvd F f)
    have hcop : Nat.Coprime 2 (Nat.card (F.map f)) := hFodd.coprime_two_left
    have hbot : F.map f = ⊥ := by
      apply Subgroup.card_eq_one.mp
      obtain ⟨n, hn⟩ := hFp.exists_card_eq
      rw [hn] at hcop ⊢
      by_cases hnzero : n = 0
      · simp [hnzero]
      · have hdiv : 2 ∣ 2 ^ n := dvd_pow_self 2 hnzero
        have htwo := hcop.eq_one_of_dvd hdiv
        norm_num at htwo
    exact (hne hbot).elim
  · have hkerS : f.ker ≤ (S : Subgroup X) := le_sup_left.trans_eq heq
    have hkerCore : f.ker ≤ pCore 2 X :=
      le_sSup ⟨inferInstance, S.isPGroup'.to_le hkerS⟩
    exact bot_unique (hkerCore.trans_eq hcore)
end MonoidHom
