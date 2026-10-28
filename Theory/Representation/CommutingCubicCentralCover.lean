module
public import Theory.Representation.CentralCoverOriginalAction
public import Mathlib.Algebra.Field.ZMod

/-!
# Commuting cubic actors split central binary covers

Let a binary module cover have fixed kernel. If a cubic element centralizes
an actor that generates the cover, and acts without fixed vectors on the
quotient, the cover map is injective. The cubic trace has image in the fixed
kernel, commutes with the generating actor, and hence vanishes; its
restriction to the kernel is the identity.

For a direct product, fixed-point-free elements in the second factor make
that factor generate the quotient, and the standard normal-restriction
argument makes it generate the cover. A fixed-point-free cubic in the first
factor therefore eliminates the central kernel. This supplies the actual
cover-splitting step in the A₅ tensor reduction without a cohomology or
projectivity assumption.
Source: Aschbacher–Smith D.3.7 and Remark I.1.5, printed pp.197–199 and408.
-/

public section
namespace Representation.OneCohomology
variable {G U V : Type*} [Group G] [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Cubic trace kills a fixed kernel when a commuting actor generates the source. -/
theorem injective_of_commuting_cubic
    {τ : Representation (ZMod 2) G U} {σ : Representation (ZMod 2) G V}
    (p : τ.IntertwiningMap σ) (H : Subgroup G)
    (hk : ∀ u, p u = 0 → ∀ g, τ g u = u)
    (hgen : Coinvariants.ker (τ.comp H.subtype) = ⊤)
    (a : G) (ha : a ^ 3 = 1) (hcomm : ∀ h : H, Commute a (h : G))
    (hfree : ∀ v, σ a v = v → v = 0) : Function.Injective p := by
  let N : U →ₗ[ZMod 2] U := 1 + τ a + τ (a * a)
  have hN (u : U) : N u = u + τ a u + τ (a * a) u := rfl
  have hc : a * (a * a) = 1 := by simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ha
  have hfix (u : U) : τ a (N u) = N u := by
    rw [hN, map_add, map_add]
    simp only [← Module.End.mul_apply, ← map_mul, hc, map_one, Module.End.one_apply]
    abel
  have hpN (u : U) : p (N u) = 0 := by
    apply hfree
    rw [← p.isIntertwining, hfix]
  have hNH (h : H) (u : U) : N (τ h u) = τ h (N u) := by
    have h1 := (hcomm h).eq
    have h2 := ((hcomm h).mul_left (hcomm h)).eq
    simp only [hN, map_add, ← Module.End.mul_apply, ← map_mul, h1, h2]
  have hle : Coinvariants.ker (τ.comp H.subtype) ≤ N.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨h,u⟩,rfl⟩
    change N (τ h u - u) = 0
    rw [map_sub,hNH,hk _ (hpN u),sub_self]
  have hzero : N = 0 := by
    ext u
    exact hle (hgen ▸ Submodule.mem_top)
  apply (injective_iff_map_eq_zero p.toLinearMap).mpr
  intro u hu
  have he : N u = 0 := LinearMap.congr_fun hzero u
  rw [hN, hk u hu a, hk u hu (a*a)] at he
  have htwo : u + u = 0 := by
    calc
      u + u = (1 + 1 : ZMod 2) • u := by rw [add_smul, one_smul]
      _ = 0 := by rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_smul]
  simpa only [htwo, zero_add] using he

/-- Generation in a normal subgroup lifts from the quotient of a central cover. -/
theorem injective_of_cover_commuting_cubic
    {τ : Representation (ZMod 2) G U} {σ : Representation (ZMod 2) G V}
    (p : τ.IntertwiningMap σ) (hp : IsCover p) (H : Subgroup G) [H.Normal]
    (hgen : Coinvariants.ker (σ.comp H.subtype) = ⊤)
    (a : G) (ha : a ^ 3 = 1) (hcomm : ∀ h : H, Commute a (h : G))
    (hfree : ∀ v, σ a v = v → v = 0) : Function.Injective p :=
  injective_of_commuting_cubic p H (fun _ hu g => hp.2.1 hu g)
    (CentralCoverOriginalAction.restrict_full H p hp hgen) a ha hcomm hfree

end Representation.OneCohomology

namespace Representation
variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V]

/-- One fixed-point-free actor generates a finite-dimensional module by displacements. -/
theorem coinvariants_eq_top_of_fixedPointFree (σ : Representation k G V)
    (a : G) (hfree : ∀ v, σ a v = v → v = 0) : Coinvariants.ker σ = ⊤ := by
  have hi : Function.Injective (σ a - 1 : V →ₗ[k] V) := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    exact hfree v (sub_eq_zero.mp hv)
  have hs := LinearMap.surjective_of_injective hi
  apply top_unique
  intro v _
  obtain ⟨w,hw⟩ := hs v
  rw [← hw]
  exact Coinvariants.sub_mem_ker a w

end Representation

namespace Representation.OneCohomology
variable {G H U V : Type*} [Group G] [Group H]
  [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Fixed-point-free actors in both product factors eliminate a central cover kernel.
Only the first actor needs to have order dividing three. -/
theorem injective_of_cover_product_cubics
    {τ : Representation (ZMod 2) (G × H) U} {σ : Representation (ZMod 2) (G × H) V}
    (p : τ.IntertwiningMap σ) (hp : IsCover p)
    (a : G) (ha : a ^ 3 = 1) (b : H)
    (hleft : ∀ v, σ (a,1) v = v → v = 0)
    (hright : ∀ v, σ (1,b) v = v → v = 0) : Function.Injective p := by
  let K : Subgroup (G × H) := (MonoidHom.fst G H).ker
  have hgen : Coinvariants.ker (σ.comp K.subtype) = ⊤ :=
    coinvariants_eq_top_of_fixedPointFree (σ.comp K.subtype)
      (⟨(1,b),rfl⟩ : K) hright
  apply injective_of_cover_commuting_cubic p hp K hgen (a,1)
  · exact Prod.ext ha (by simp)
  · intro h
    change (a,1) * h.val = h.val * (a,1)
    apply Prod.ext
    · have hh : h.val.1 = 1 := h.property
      simp only [Prod.fst_mul,hh,mul_one,one_mul]
    · simp only [Prod.snd_mul,mul_one,one_mul]
  · exact hleft

end Representation.OneCohomology
