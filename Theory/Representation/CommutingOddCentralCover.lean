module
public import Theory.Representation.CommutingCubicCentralCover
public import Mathlib.Algebra.Ring.GeomSum
/-!
# Commuting odd-order actors split central binary covers

The norm over an odd cyclic subgroup has image in the fixed kernel of a
central cover whenever that cyclic actor is fixed-free on the quotient.
If a commuting subgroup generates the cover, the norm kills every generator
commutator. On the fixed kernel it is multiplication by an odd integer,
hence the identity in characteristic two; the cover kernel is therefore zero.

The product-factor consumer permits the fixed-free fifth-order actor on the
deleted A₅ tensor square, alongside the existing cubic natural-module case.
Source: Aschbacher–Smith,D.3.7 and Remark I.1.5, printed pp.197–199 and408.
-/

public section
namespace Representation.OneCohomology
variable {G U V : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]
/-- The odd cyclic norm annihilates a central kernel under full commuting generation. -/
theorem injective_of_commuting_odd
    {τ : Representation (ZMod 2) G U} {σ : Representation (ZMod 2) G V}
    (p : τ.IntertwiningMap σ) (H : Subgroup G)
    (hk : ∀ u, p u = 0 → ∀ g, τ g u = u)
    (hgen : Coinvariants.ker (τ.comp H.subtype) = ⊤)
    (a : G) (n : ℕ) (hn : Odd n) (ha : a ^ n = 1)
    (hcomm : ∀ h : H, Commute a (h : G))
    (hfree : ∀ v, σ a v = v → v = 0) : Function.Injective p := by
  let N : U →ₗ[ZMod 2] U := ∑ i ∈ Finset.range n, (τ a)^i
  have hfix (u : U) : τ a (N u) = N u := by
    have he : (τ a - 1) * N = 0 := by
      change (τ a - 1) * (∑ i ∈ Finset.range n, (τ a)^i) = 0
      rw [mul_geom_sum,← map_pow,ha,map_one,sub_self]
    have hev := LinearMap.congr_fun he u
    exact sub_eq_zero.mp hev
  have hpN (u : U) : p (N u) = 0 := by
    apply hfree
    rw [← p.isIntertwining,hfix]
  have hNH (h : H) (u : U) : N (τ h u) = τ h (N u) := by
    simp only [N,LinearMap.sum_apply,map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have he := congrArg τ ((hcomm h).pow_left i).eq
    have he' := congrArg (fun f : Module.End (ZMod 2) U => f u) he
    simpa only [map_mul,map_pow,Module.End.mul_apply] using he'
  have hle : Coinvariants.ker (τ.comp H.subtype) ≤ N.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨h,u⟩,rfl⟩
    change N (τ h u - u) = 0
    rw [map_sub,hNH,hk _ (hpN u),sub_self]
  apply (injective_iff_map_eq_zero p.toLinearMap).mpr
  intro u hu
  have he : N u = 0 := hle (hgen ▸ Submodule.mem_top)
  have hNu : N u = u := by
    have ht (i : ℕ) : ((τ a)^i) u = u := by rw [← map_pow]; exact hk u hu _
    simp only [N,LinearMap.sum_apply,ht,Finset.sum_const,Finset.card_range]
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2)]
    have hn' : (n : ZMod 2) = 1 := by
      obtain ⟨m,rfl⟩ := hn
      rw [Nat.cast_add,Nat.cast_mul,Nat.cast_one,ZMod.natCast_self,zero_mul,zero_add]
    rw [hn',one_smul]
  exact hNu.symm.trans he

/-- Full generation lifts from the quotient for a normal commuting actor. -/
theorem injective_of_cover_commuting_odd
    {τ : Representation (ZMod 2) G U} {σ : Representation (ZMod 2) G V}
    (p : τ.IntertwiningMap σ) (hp : IsCover p) (H : Subgroup G) [H.Normal]
    (hgen : Coinvariants.ker (σ.comp H.subtype) = ⊤)
    (a : G) (n : ℕ) (hn : Odd n) (ha : a ^ n = 1)
    (hcomm : ∀ h : H, Commute a (h : G))
    (hfree : ∀ v, σ a v = v → v = 0) : Function.Injective p :=
  injective_of_commuting_odd p H (fun _ hu g => hp.2.1 hu g)
    (CentralCoverOriginalAction.restrict_full H p hp hgen) a n hn ha hcomm hfree
end Representation.OneCohomology

namespace Representation.OneCohomology
variable {G H U V : Type*} [Group G] [Group H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
/-- Fixed-free product factors split a central cover when the first actor has odd order. -/
theorem injective_of_cover_product_odd
    {τ : Representation (ZMod 2) (G × H) U} {σ : Representation (ZMod 2) (G × H) V}
    (p : τ.IntertwiningMap σ) (hp : IsCover p)
    (a : G) (n : ℕ) (hn : Odd n) (ha : a ^ n = 1) (b : H)
    (hleft : ∀ v, σ (a,1) v = v → v = 0)
    (hright : ∀ v, σ (1,b) v = v → v = 0) : Function.Injective p := by
  let K : Subgroup (G × H) := (MonoidHom.fst G H).ker
  have hgen : Coinvariants.ker (σ.comp K.subtype) = ⊤ :=
    coinvariants_eq_top_of_fixedPointFree (σ.comp K.subtype)
      (⟨(1,b),rfl⟩ : K) hright
  apply injective_of_cover_commuting_odd p hp K hgen (a,1) n hn
  · exact Prod.ext ha (by simp)
  · intro h
    change (a,1) * h.val = h.val * (a,1)
    apply Prod.ext
    · have hh : h.val.1 = 1 := h.property
      simp only [Prod.fst_mul,hh,mul_one,one_mul]
    · simp only [Prod.snd_mul,mul_one,one_mul]
  · exact hleft
end Representation.OneCohomology
