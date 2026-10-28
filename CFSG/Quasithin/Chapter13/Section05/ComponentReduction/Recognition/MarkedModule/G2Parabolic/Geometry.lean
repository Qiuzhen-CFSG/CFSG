module

public import Theory.Representation.G2BinaryPlaneOrbits.Sylow
public import Theory.Representation.G2BinaryPlaneOrbits.Stabilizer
public import Theory.GroupTheory.SylowNormalRestriction
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The marked G₂ plane bound, including outer Sylow actions

A Sylow-invariant binary plane is conjugate to the literal octonion null
plane, so its stabilizer has order 96. The Sylow has order 32. Intersecting
an ambient stabilizer with a normal G₂(2)′ subgroup preserves the relative
index over its Sylow supplement. An equivariant quotient injective on the
marked plane therefore bounds that index by three, even when the ambient
Sylow acts through outer automorphisms and the module has a central kernel.

Source: Aschbacher–Smith, 13.5.21(5), printed p.924 / PDF p.941.
The concrete plane calculations retain the ATLAS attribution in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open scoped Pointwise
open Subgroup Representation Representation.BinaryOffender
open Atlas.G2.Natural.BinaryPlane
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Geometry

/-- Sylow-invariant planes are conjugate to the marked null plane. -/
theorem plane_conjugacy (S : Sylow 2 Actor) (W : Submodule (ZMod 2) Coefficients)
    (hW : Nat.card W = 4) (hS : (S : Subgroup Actor) ≤ subspaceStabilizer action W) :
    ∃ g : Actor, W.map (innerCoordinates g).toLinearMap = standardPlane := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Actor S standardSylow
  have hmap : (standardSylow : Subgroup Actor) ≤
      subspaceStabilizer action (W.map (innerCoordinates g).toLinearMap) := by
    rw [← map_subspaceStabilizer_equivariant action action (MulAut.conj g)
      (innerCoordinates g) (innerCoordinates_equivariant g) W]
    rw [← hg, Sylow.coe_subgroup_smul]
    exact map_mono hS
  have hc : Nat.card (W.map (innerCoordinates g).toLinearMap) = 4 := by
    rw [← Nat.card_congr (Submodule.equivMapOfInjective _
      (innerCoordinates g).injective W).toEquiv, hW]
  exact ⟨g, eq_standardPlane_of_standardSylow _ hc hmap⟩

theorem card_plane_stabilizer (S : Sylow 2 Actor) (W : Submodule (ZMod 2) Coefficients)
    (hW : Nat.card W = 4) (hS : (S : Subgroup Actor) ≤ subspaceStabilizer action W) :
    Nat.card (subspaceStabilizer action W) = 96 := by
  obtain ⟨g,hg⟩ := plane_conjugacy S W hW hS
  have he := map_subspaceStabilizer_equivariant action action (MulAut.conj g)
    (innerCoordinates g) (innerCoordinates_equivariant g) W
  rw [hg] at he
  rw [← card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective, he]
  exact card_standardPlane_stabilizer

section Group
variable {H : Type*} [Group H] [Finite H]

/-- A stabilizer containing the Sylow supplement has the same relative index
as its intersection with the normal subgroup. This allows an outer Sylow action. -/
theorem stabilizer_relIndex (N S B : Subgroup H)
    (hn : S ≤ normalizer (N : Set H)) (hSB : S ≤ B) :
    S.relIndex ((N ⊔ S) ⊓ B) = S.relIndex (N ⊓ B) := by
  have he : (N ⊔ S) ⊓ B = (N ⊓ B) ⊔ S := by
    apply le_antisymm
    · intro x hx
      have hx' : x ∈ Set.image2 (· * ·) (N : Set H) (S : Set H) := by
        change x ∈ (N : Set H) * (S : Set H)
        rw [← coe_mul_of_right_le_normalizer_left N S hn]
        exact hx.1
      obtain ⟨n,hnN,s,hsS,rfl⟩ := hx'
      have hnB : n ∈ B := by
        simpa only [mul_inv_cancel_right] using B.mul_mem hx.2 (B.inv_mem (hSB hsS))
      exact mul_mem_sup ⟨hnN,hnB⟩ hsS
    · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
        (le_inf le_sup_right hSB)
  rw [he]
  apply relIndex_sup_of_normalizes
  exact (le_inf hn (hSB.trans B.le_normalizer)).trans inf_normalizer_le_normalizer_inf

end Group

section Action
variable {H V W : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem card_map_of_disjoint (p : V →ₗ[ZMod 2] W)
    (X : Submodule (ZMod 2) V) (hX : Disjoint X p.ker) : Nat.card (X.map p) = Nat.card X := by
  let f : X →ₗ[ZMod 2] X.map p :=
    (p.comp X.subtype).codRestrict (X.map p) (fun x => ⟨x.val,x.property,rfl⟩)
  have hi : Function.Injective f := by
    intro x y he
    apply sub_eq_zero.mp
    apply Subtype.ext
    exact Submodule.disjoint_def.mp hX _ (X.sub_mem x.property y.property)
      (by change p (x.val-y.val) = 0; rw [map_sub]; exact sub_eq_zero.mpr (congrArg Subtype.val he))
  have hs : Function.Surjective f := by
    rintro ⟨y,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  exact (Nat.card_congr (LinearEquiv.ofBijective f ⟨hi,hs⟩).toEquiv).symm

omit [Finite H] in
/-- Equivariance maps invariant subspaces to invariant subspaces. -/
theorem image_stable (ρ : Representation (ZMod 2) H V)
    (τ : Representation (ZMod 2) H W) (p : V →ₗ[ZMod 2] W)
    (hp : ∀ g v, p (ρ g v) = τ g (p v)) (X : Submodule (ZMod 2) V)
    (g : H) (hg : g ∈ subspaceStabilizer ρ X) :
    g ∈ subspaceStabilizer τ (X.map p) := by
  have h (a : H) (ha : a ∈ subspaceStabilizer ρ X) :
      ∀ v ∈ X.map p, τ a v ∈ X.map p := by
    rintro v ⟨x,hx,rfl⟩
    exact ⟨ρ a x, (ha x).mpr hx, hp a x⟩
  intro v
  constructor
  · intro hv
    have hw := h g⁻¹ ((subspaceStabilizer ρ X).inv_mem hg) _ hv
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply] using hw
  · exact h g hg v

/-- The concrete bound for the original plane, allowing any outer Sylow action.
The kernel may be central and nonzero; only the marked plane avoids it. -/
theorem index_bound (N : Subgroup H) [N.Normal] (S : Sylow 2 H)
    (ρ : Representation (ZMod 2) H V) (τ : Representation (ZMod 2) H W)
    (p : V →ₗ[ZMod 2] W) (hp : ∀ g v, p (ρ g v) = τ g (p v))
    (f : N ≃* Actor) (e : W ≃ₗ[ZMod 2] Coefficients)
    (he : ∀ g : N, ∀ w, e (τ g.val w) = action (f g) (e w))
    (X : Submodule (ZMod 2) V) (hX : Nat.card X = 4)
    (hd : Disjoint X p.ker) (hS : (S : Subgroup H) ≤ subspaceStabilizer ρ X) :
    (S : Subgroup H).relIndex ((N ⊔ (S : Subgroup H)) ⊓ subspaceStabilizer ρ X) ≤ 3 := by
  let B := subspaceStabilizer ρ X
  let Xq := X.map p
  let Xn := Xq.map e.toLinearMap
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal N
  let Rn := R.mapSurjective (f := f.toMonoidHom) f.surjective
  have hRst : (Rn : Subgroup Actor) ≤ subspaceStabilizer action Xn := by
    rintro _ ⟨r,hr,rfl⟩
    apply (mem_subspaceStabilizer_equivariant (τ.comp N.subtype) action f e he Xq r).mp
    exact image_stable ρ τ p hp X r.val (hS (show r ∈ (S : Subgroup H).subgroupOf N by rwa [← hR]))
  have hXn : Nat.card Xn = 4 := by
    rw [← Nat.card_congr (Submodule.equivMapOfInjective e.toLinearMap e.injective Xq).toEquiv]
    exact (card_map_of_disjoint p X hd).trans hX
  have h96 := card_plane_stabilizer Rn Xn hXn hRst
  have h32 : Nat.card (((S : Subgroup H) ⊓ N) : Subgroup H) = 32 := by
    rw [← subgroupOf_map_subtype, ← hR, card_map_of_injective N.subtype_injective]
    have hRn : Nat.card Rn = Nat.card R := card_map_of_injective f.injective
    have heR : Nat.card Rn = Nat.card standardSylow := Nat.card_congr (Rn.equiv standardSylow)
    exact hRn.symm.trans (heR.trans card_standardSylow)
  have hbound : Nat.card ((N ⊓ B) : Subgroup H) ≤ 96 := by
    let F : (N ⊓ B : Subgroup H) →* Actor :=
      f.toMonoidHom.comp (inclusion (show N ⊓ B ≤ N from inf_le_left))
    have hi : Function.Injective F := f.injective.comp (inclusion_injective _)
    have hFB : F.range ≤ subspaceStabilizer action Xn := by
      rintro _ ⟨x,rfl⟩
      apply (mem_subspaceStabilizer_equivariant (τ.comp N.subtype) action f e he Xq
        (inclusion inf_le_left x)).mp
      exact image_stable ρ τ p hp X x.val x.property.2
    have hc : Nat.card F.range = Nat.card ((N ⊓ B) : Subgroup H) :=
      Nat.card_congr (MonoidHom.ofInjective hi).symm.toEquiv
    rw [← hc, ← h96]
    exact Nat.card_le_card_of_injective (inclusion hFB) (inclusion_injective hFB)
  rw [stabilizer_relIndex N S B le_normalizer_of_normal hS]
  have hle : (S : Subgroup H) ⊓ N ≤ N ⊓ B :=
    le_inf inf_le_right (inf_le_left.trans hS)
  have hc := relIndex_mul_relIndex (⊥ : Subgroup H) ((S : Subgroup H) ⊓ N) (N ⊓ B) bot_le hle
  rw [relIndex_bot_left, relIndex_bot_left] at hc
  have hi : ((S : Subgroup H) ⊓ N).relIndex (N ⊓ B) = (S : Subgroup H).relIndex (N ⊓ B) := by
    conv_lhs => rw [← inf_relIndex_right]
    conv_rhs => rw [← inf_relIndex_right]
    congr 1
    ext x
    simp only [mem_inf]
    tauto
  rw [h32,hi] at hc
  omega
end Action
end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.MarkedModule.G2Parabolic.Geometry
