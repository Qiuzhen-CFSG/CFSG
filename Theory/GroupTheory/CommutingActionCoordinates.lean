module

public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.PCoreSurjective

/-!
# Coordinates from a commuting factor and an action kernel

Suppose a subgroup induces the full action and commutes with the action
kernel. If their intersection is a p-group and the ambient p-core is
trivial, the intersection vanishes: both factors are normal and generate
the whole group. Multiplication then supplies product coordinates whose
second factor is the actual kernel, with both embedding formulas retained.

This is the elementary internal-product argument used in Aschbacher–Smith,
proof of 15.3.67, printed p.1153, after quotienting by the two-core.
-/

public section

open Subgroup

namespace Subgroup
variable {G S : Type*} [Group G] [Group S]

/-- Full action, commutation, and a p-group intersection construct compatible
coordinates in a group with trivial p-core. -/
theorem exists_product_coordinates_of_pCore_eq_bot (p : ℕ) (A B : Subgroup G) (f : G →* S)
    (hk : f.ker = B) (hf : Function.Surjective (f.comp A.subtype))
    (hc : A ≤ centralizer (B : Set G)) (hp : IsPGroup p (A ⊓ B : Subgroup G))
    (hcore : pCore p G = ⊥) :
    ∃ e : G ≃* S × B,
      (∀ a : A, e a = (f a, 1)) ∧
      (∀ b : B, e b = (1, b)) ∧
      A.map e.toMonoidHom = (⊤ : Subgroup S).prod ⊥ := by
  have hgen : A ⊔ B = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨a, ha⟩ := hf (f g)
    have hb : (a : G)⁻¹ * g ∈ B := by
      rw [← hk]
      change f ((a : G)⁻¹ * g) = 1
      rw [map_mul, map_inv, show f a = f g from ha, inv_mul_cancel]
    simpa only [mul_inv_cancel_left] using
      (A ⊔ B).mul_mem (mem_sup_left a.property) (mem_sup_right hb)
  have hbc : B ≤ centralizer (A : Set G) := le_centralizer_iff.mp hc
  let : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    rw [← hgen]
    exact sup_le A.le_normalizer (hbc.trans (centralizer_le_normalizer _))))
  let : B.Normal := hk ▸ f.normal_ker
  have hd : Disjoint A B := disjoint_iff.mpr (le_bot_iff.mp (by
    have hle : A ⊓ B ≤ pCore p G := le_sSup ⟨inferInstance, hp⟩
    rwa [hcore] at hle))
  have hfi : Function.Injective (f.comp A.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro a ha
    apply Subtype.ext
    exact disjoint_def.mp hd a.property (hk ▸ ha)
  let ea : A ≃* S := MulEquiv.ofBijective (f.comp A.subtype) ⟨hfi, hf⟩
  obtain ⟨m, hm⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let m' : A × B ≃* G :=
    m.trans ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv)
  have hm' (a : A) (b : B) : m' (a,b) = (a : G) * b := hm a b
  let e : G ≃* S × B := m'.symm.trans (ea.prodCongr (MulEquiv.refl B))
  have hleft (a : A) : e a = (f a, 1) := by
    have he : m' (a,1) = a := by simpa using hm' a 1
    conv_lhs => rw [← he]
    change (ea.prodCongr (MulEquiv.refl B)) (m'.symm (m' (a,1))) = _
    rw [m'.symm_apply_apply]
    rfl
  have hright (b : B) : e b = (1,b) := by
    have he : m' (1,b) = b := by simpa using hm' 1 b
    conv_lhs => rw [← he]
    change (ea.prodCongr (MulEquiv.refl B)) (m'.symm (m' (1,b))) = _
    rw [m'.symm_apply_apply]
    exact Prod.ext (map_one ea) rfl
  refine ⟨e, hleft, hright, ?_⟩
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    change e a ∈ (⊤ : Subgroup S).prod ⊥
    rw [hleft ⟨a,ha⟩]
    exact ⟨mem_top _, rfl⟩
  · rintro ⟨_,hx⟩
    obtain ⟨a,ha⟩ := hf x.1
    exact ⟨a,a.property,(hleft a).trans (Prod.ext ha hx.symm)⟩
end Subgroup
