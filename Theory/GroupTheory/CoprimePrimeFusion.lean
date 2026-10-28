module

public import Theory.GroupTheory.CoprimeQuotientSubgroups

/-!
# Prime-order conjugacy through a coprime kernel

Elements of order p with the same image lie in the preimage of a cyclic
p-subgroup. Their cyclic subgroups are Sylow there: injectivity on any
p-subgroup prevents enlargement. Sylow conjugacy, followed by injectivity
on the target cyclic subgroup, conjugates the elements themselves.
A lifted quotient conjugator gives the version for conjugate images.

This is the coprime fusion argument used to transfer the point-residual
Sylow action in Aschbacher--Smith, 12.9, printed pp.862--864.
-/

public section
open Subgroup
open scoped Pointwise
namespace MonoidHom

/-- A coprime kernel reflects conjugacy of prime-order elements with equal images. -/
theorem isConj_of_map_eq_of_prime_order_of_coprime_ker
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H)
    (hker : Nat.Coprime p (Nat.card f.ker))
    {x y : G} (hx : orderOf x = p) (hy : orderOf y = p)
    (hxy : f x = f y) : IsConj x y := by
  let R := (zpowers (f x)).comap f
  let fr := f.comp R.subtype
  have hkr : Nat.Coprime p (Nat.card fr.ker) := by
    apply Nat.Coprime.of_dvd_right _ hker
    have hd := card_dvd_of_le (show fr.ker.map R.subtype ≤ f.ker from by
      rintro _ ⟨z,hz,rfl⟩
      exact hz)
    rwa [card_map_of_injective R.subtype_injective] at hd
  let xr : R := ⟨x, mem_zpowers (f x)⟩
  let yr : R := ⟨y, by change f y ∈ zpowers (f x); rw [← hxy]; exact mem_zpowers _⟩
  have make (z : R) (hz : orderOf z = p) (hfz : f z = f x) :
      ∃ P : Sylow p R, (P : Subgroup R) = zpowers z := by
    have hp : IsPGroup p (zpowers z) := IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, hz, pow_one])
    refine ⟨⟨zpowers z, hp, ?_⟩, rfl⟩
    intro Q hQ hAQ
    apply le_antisymm ?_ hAQ
    intro a ha
    obtain ⟨k,hk⟩ := a.property
    have hzk : z ^ k ∈ Q := hAQ (zpow_mem_zpowers z k)
    have he : (⟨z ^ k, hzk⟩ : Q) = ⟨a,ha⟩ :=
      injective_comp_subtype_of_coprime_ker fr hkr Q hQ (by
        change f ((z : G) ^ k) = f (a : G)
        rw [map_zpow, hfz]
        exact hk)
    have hza : z ^ k = a := congrArg Subtype.val he
    rw [← hza]
    exact zpow_mem_zpowers z k
  obtain ⟨P,hP⟩ := make xr ((orderOf_injective R.subtype R.subtype_injective xr).symm.trans hx) rfl
  obtain ⟨Q,hQ⟩ := make yr ((orderOf_injective R.subtype R.subtype_injective yr).symm.trans hy) hxy.symm
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq R P Q
  have hmem : g * xr * g⁻¹ ∈ (Q : Subgroup R) := by
    rw [← hg]
    exact Subgroup.mem_map.mpr ⟨xr, hP ▸ mem_zpowers xr, rfl⟩
  have hyQ : yr ∈ (Q : Subgroup R) := hQ ▸ mem_zpowers yr
  have hcomm : Commute (f (g : G)) (f x) := by
    obtain ⟨k,hk⟩ := g.property
    rw [← hk]
    exact (Commute.refl (f x)).zpow_left k
  have he : (⟨g * xr * g⁻¹,hmem⟩ : Q) = ⟨yr,hyQ⟩ :=
    injective_comp_subtype_of_coprime_ker fr hkr Q Q.isPGroup' (by
      change f ((g : G) * x * (g : G)⁻¹) = f y
      rw [map_mul, map_mul, map_inv, hcomm.eq, mul_inv_cancel_right, hxy])
  exact isConj_iff.mpr ⟨(g : G), congrArg (fun z : Q => ((z : R) : G)) he⟩

/-- Conjugacy of prime-order images lifts through a surjection with coprime kernel. -/
theorem isConj_of_map_isConj_of_prime_order_of_coprime_ker
    {G H : Type*} [Group G] [Finite G] [Group H]
    {p : ℕ} [Fact p.Prime] (f : G →* H) (hf : Function.Surjective f)
    (hker : Nat.Coprime p (Nat.card f.ker))
    {x y : G} (hx : orderOf x = p) (hy : orderOf y = p)
    (hxy : IsConj (f x) (f y)) : IsConj x y := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hxy
  obtain ⟨g, rfl⟩ := hf a
  have hm : f (MulAut.conj g x) = f y := by
    simpa only [MulAut.conj_apply, map_mul, map_inv] using ha
  exact (isConj_iff.mpr ⟨g, rfl⟩).trans
    (f.isConj_of_map_eq_of_prime_order_of_coprime_ker hker ((MulAut.conj g).orderOf_eq x |>.trans hx) hy hm)

end MonoidHom
