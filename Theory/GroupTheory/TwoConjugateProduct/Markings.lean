module
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Exact Sylow and Borel preimages under paired multiplication

For commuting factors, a subgroup whose factor intersection is a
self-normalizing Borel pulls back to the product of its factor intersections.
The prescribed Sylow pulls back to the product of its actual factor Sylows,
by maximality of the two coordinate projections. The multiplication map
is kept literal throughout, so the original V is transported without any
choice of abstract coordinates.

Source: Aschbacher–Smith E.2.7, printed p.219, paired Bender construction.
-/

public section
open Subgroup
namespace Subgroup
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem product_borel_comap (K D M : Subgroup H)
    (f : K × D →* H) (hf : ∀ k d, f (k,d) = (k:H)*(d:H))
    (hc : K ≤ centralizer (D : Set H))
    (hself : normalizer (M.subgroupOf K : Set K) = M.subgroupOf K) :
    M.comap f = (M.subgroupOf K).prod (M.subgroupOf D) := by
  ext x
  rcases x with ⟨k,d⟩
  change f (k,d) ∈ M ↔ (k:H)∈M ∧ (d:H)∈M
  rw [hf]
  constructor
  · intro hx
    have hk : k ∈ normalizer (M.subgroupOf K : Set K) := by
      apply mem_normalizer_iff.mpr
      intro y
      constructor
      · intro hy
        change (k:H)*(y:H)*(k:H)⁻¹ ∈ M
        have hh := M.mul_mem (M.mul_mem hx hy) (M.inv_mem hx)
        have hcdy : (d:H)*(y:H)=(y:H)*(d:H) := hc y.property d d.property
        have he : ((k:H)*(d:H))*(y:H)*((k:H)*(d:H))⁻¹ = (k:H)*(y:H)*(k:H)⁻¹ := by
          rw [mul_inv_rev,mul_assoc (k:H) (d:H) (y:H),hcdy]
          group
        change ((k:H)*(d:H))*(y:H)*((k:H)*(d:H))⁻¹ ∈ M at hh
        rwa [he] at hh
      · intro hy
        change (k:H)*(y:H)*(k:H)⁻¹ ∈ M at hy
        have hh := M.mul_mem (M.mul_mem (M.inv_mem hx) hy) hx
        have hcdy : (d:H)*(y:H)=(y:H)*(d:H) := hc y.property d d.property
        have he : ((k:H)*(d:H))⁻¹*((k:H)*(y:H)*(k:H)⁻¹)*((k:H)*(d:H)) = (y:H) := by
          calc
            _ = (d:H)⁻¹*(y:H)*(d:H) := by group
            _ = (y:H) := by rw [mul_assoc,← hcdy]; group
        rwa [he] at hh
    rw [hself] at hk
    refine ⟨hk,?_⟩
    have hh := M.mul_mem (M.inv_mem hk) hx
    change (k:H)⁻¹*((k:H)*(d:H)) ∈ M at hh
    simpa only [inv_mul_cancel_left] using hh
  · rintro ⟨hk,hd⟩
    exact M.mul_mem hk hd

omit [Finite H] in
theorem product_sylow_comap (K D : Subgroup H) (T : Sylow 2 H)
    (f : K × D →* H) (hf : Function.Injective f)
    (hm : ∀k d, f (k,d) = (k:H)*(d:H))
    (S : Sylow 2 K) (R : Sylow 2 D)
    (hS : (S : Subgroup K) = (T : Subgroup H).subgroupOf K)
    (hR : (R : Subgroup D) = (T : Subgroup H).subgroupOf D) :
    (T : Subgroup H).comap f = (S : Subgroup K).prod (R : Subgroup D) := by
  let U := (T : Subgroup H).comap f
  have hp : IsPGroup 2 U := T.isPGroup'.comap_of_injective f hf
  have hSU : (S : Subgroup K).prod (R : Subgroup D) ≤ U := by
    rintro ⟨k,d⟩ ⟨hk,hd⟩
    change f (k,d) ∈ T
    rw [hm]
    rw [hS] at hk
    rw [hR] at hd
    exact (T : Subgroup H).mul_mem hk hd
  have hfst : U.map (MonoidHom.fst K D) = (S : Subgroup K) := by
    apply S.is_maximal' (hp.map _)
    intro k hk
    exact ⟨(k,1),hSU ⟨hk,R.one_mem⟩,rfl⟩
  have hsnd : U.map (MonoidHom.snd K D) = (R : Subgroup D) := by
    apply R.is_maximal' (hp.map _)
    intro d hd
    exact ⟨(1,d),hSU ⟨S.one_mem,hd⟩,rfl⟩
  apply le_antisymm ?_ hSU
  exact le_prod_iff.mpr ⟨hfst.le,hsnd.le⟩
end Subgroup
