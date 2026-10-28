module
public import Theory.Representation.BinaryAlternatingFiveFlag.Coordinates
/-!
# A plane stabilizer in the deleted five-point module fixes the Sylow point

The regular four-group on the first four letters has fixed line generated
by the weight-four vector. The orbit of every vector outside the standard
hyperplane spans the entire augmentation core. Thus every proper invariant
plane lies in that hyperplane. A permutation carrying the fixed vector
back into it fixes the fifth letter, hence fixes the vector itself.
Sylow conjugacy transports this calculation to any subgroup containing A₅,
and the last theorem retains arbitrary equivariant action coordinates.

Source application: Aschbacher--Smith 14.3.23(2), printed p.1000.
-/

public section
open Subgroup Module Representation
open BinaryPermutation BinaryPermutation.AlternatingFiveFlag BinaryPermutation.FiveCentralizerGeometry
namespace BinaryPermutation.AlternatingFiveFlag.PlaneFixer

private theorem orbit_basis : ∀ x y : Space, x.val 4 ≠ 0 →
    ∃ a b c d : Bool, y = (if a then x else 0) + (if b then rho k₀ x else 0) +
      (if c then rho k₁ x else 0) + (if d then rho (k₀*k₁) x else 0) := by decide +kernel
private theorem fixed_points : ∀ x : Space, rho k₀ x=x → rho k₁ x=x → x=0 ∨ x=z := by
  decide +kernel
private theorem invariant_proper (W : Submodule (ZMod 2) Space) (hp : W ≠ ⊤)
    (hi : ∀ g∈four, ∀ w∈W, rho g w ∈ W) : ∀ w∈W, w.val 4=0 := by
  intro w hw
  by_contra hn
  apply hp
  apply top_unique
  intro y _
  obtain ⟨a,b,c,d,he⟩ := orbit_basis w y hn
  rw [he]
  have hz : ∀ (a : Bool) (w : Space), w ∈ W → (if a then w else 0) ∈ W := by
    intro a w hw
    cases a <;> simp [hw]
  exact W.add_mem (W.add_mem (W.add_mem (hz a w hw)
    (hz b _ (hi k₀ (Or.inr (Or.inl rfl)) w hw)))
    (hz c _ (hi k₁ (Or.inr (Or.inr (Or.inl rfl))) w hw)))
    (hz d _ (hi (k₀*k₁) (Or.inr (Or.inr (Or.inr rfl))) w hw))

private theorem standard_plane_fixes_point
    (W : Submodule (ZMod 2) Space) (hd : finrank (ZMod 2) W=2)
    (hi : ∀ g∈four, ∀ w∈W, rho g w ∈ W)
    (v : Space) (hv : v∈W) (hf : ∀ g∈four, rho g v=v)
    (a : Perm) (ha : ∀ w∈W, rho a w∈W) : rho a v=v := by
  rcases fixed_points v (hf k₀ (Or.inr (Or.inl rfl)))
    (hf k₁ (Or.inr (Or.inr (Or.inl rfl)))) with rfl | rfl
  · exact map_zero _
  · have hW : W ≠ ⊤ := by
      intro ht
      rw [ht,finrank_top,finrank_core] at hd
      norm_num at hd
    have hz := invariant_proper W hW hi (rho a z) (ha z hv)
    apply (fixes_z_iff a).mpr
    have hh : ∀ a : Perm, (rho a z).val 4=0 → a 4=4 := by decide +kernel
    exact hh a hz

open scoped Pointwise in
theorem plane_fixes_point (H : Subgroup Perm) (hH : alternatingGroup (Fin 5)≤H)
    (P : Sylow 2 H) (W : Submodule (ZMod 2) Space) (hd : finrank (ZMod 2) W=2)
    (hi : ∀ a∈P, ∀ w∈W, rho a.val w∈W)
    (v : Space) (hv : v∈W) (hf : ∀ a∈P, rho a.val v=v)
    (a : Perm) (ha : ∀ w∈W, rho a w∈W) : rho a v=v := by
  let K := four.subgroupOf H
  have hKH : four≤H := four_even.trans hH
  obtain ⟨S,hS⟩ := (four_isPGroup.comap_subtype : IsPGroup 2 K).exists_le_sylow
  obtain ⟨b,hb⟩ := MulAction.exists_smul_eq H P S
  let e := LinearEquiv.ofBijective (rho b.val) ((rho).apply_bijective b.val)
  let W' := W.map e.toLinearMap
  have hconj (x : Perm) (hx : x∈four) :
      (b⁻¹ * ⟨x,hKH hx⟩ * b : H) ∈ P := by
    have hx' : (⟨x,hKH hx⟩ : H) ∈ (b • P : Sylow 2 H) := hb ▸ hS hx
    change (⟨x,hKH hx⟩ : H) ∈ MulAut.conj b • (P : Subgroup H) at hx'
    have hh := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hx'
    change b⁻¹ * ⟨x,hKH hx⟩ * (b⁻¹)⁻¹ ∈ (P : Subgroup H) at hh
    rw [inv_inv] at hh
    exact hh
  have heq (x : Perm) (w : Space) : rho x (e w)=e (rho (b.val⁻¹*x*b.val) w) := by
    change rho x (rho b.val w) = rho b.val (rho (b.val⁻¹*x*b.val) w)
    simp only [← Module.End.mul_apply,← map_mul]
    congr 2
    group
  have hs' : ∀ x∈four, ∀ w∈W', rho x w∈W' := by
    rintro x hx w ⟨u,hu,rfl⟩
    change rho x (e u)∈W'
    rw [heq]
    exact ⟨_,hi _ (hconj x hx) u hu,rfl⟩
  have hf' : ∀ x∈four, rho x (e v)=e v := by
    intro x hx
    rw [heq]
    exact congrArg e (hf _ (hconj x hx))
  let a' := b.val*a*b.val⁻¹
  have haa : b.val⁻¹*a'*b.val=a := by dsimp [a']; group
  have ha' : ∀ w∈W', rho a' w∈W' := by
    rintro w ⟨u,hu,rfl⟩
    change rho a' (e u)∈W'
    rw [heq,haa]
    exact ⟨_,ha u hu,rfl⟩
  have hh := standard_plane_fixes_point W' ((e.finrank_map_eq W).trans hd)
    hs' (e v) ⟨v,hv,rfl⟩ hf' a' ha'
  rw [heq,haa] at hh
  exact e.injective hh

theorem point_fixed_of_coordinates {D U : Type*} [Group D] [Finite D]
    [AddCommGroup U] [Module (ZMod 2) U]
    (r : Representation (ZMod 2) D U)
    (f : D →* Perm) (hA : alternatingGroup (Fin 5)≤f.range)
    (c : U ≃ₗ[ZMod 2] Space) (he : ∀ a u, c (r a u)=rho (f a) (c u))
    (P : Sylow 2 D) (W : Submodule (ZMod 2) U) (hd : finrank (ZMod 2) W=2)
    (hs : ∀ a∈P, ∀ w∈W, r a w∈W)
    (v : U) (hv : v∈W) (hfix : ∀ a∈P, r a v=v)
    (a : D) (ha : ∀ w∈W, r a w∈W) : r a v=v := by
  let P' := P.mapSurjective (f := f.rangeRestrict) f.rangeRestrict_surjective
  let W' := W.map c.toLinearMap
  have hs' : ∀ x∈P', ∀ w∈W', rho x.val w∈W' := by
    rintro x ⟨y,hy,rfl⟩ w ⟨u,hu,rfl⟩
    exact ⟨_,hs y hy u hu,he y u⟩
  have hf' : ∀ x∈P', rho x.val (c v)=c v := by
    rintro x ⟨y,hy,rfl⟩
    exact (he y v).symm.trans (congrArg c (hfix y hy))
  have ha' : ∀ w∈W', rho (f a) w∈W' := by
    rintro w ⟨u,hu,rfl⟩
    exact ⟨_,ha u hu,he a u⟩
  apply c.injective
  rw [he]
  exact plane_fixes_point f.range hA P' W' ((c.finrank_map_eq W).trans hd)
    hs' (c v) ⟨v,hv,rfl⟩ hf' (f a) ha'

end BinaryPermutation.AlternatingFiveFlag.PlaneFixer
