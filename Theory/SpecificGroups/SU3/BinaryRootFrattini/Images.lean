module

public import Theory.SpecificGroups.SU3.BinaryRootFrattini
public import Theory.SpecificGroups.SU3.BorelTorus.Basic

/-!
# Full-torus irreducibility in the actual special and projective root images

The coordinate calculation is applied to the injective root matrices in both
SU₃ and PSU₃. Conjugation is the actual matrix action of the complete diagonal
torus. The transport lemmas preserve ambient Frattini images under genuine
isomorphisms. Source: GLS4, Chapter 4, Lemma 3.5(a,c).
-/

public section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryRootFrattini
open EvenInner BorelTorus
variable {E : Type*} [Field E] [Finite E] [CharP E 2] (J : HermitianForm 3 E)
  (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  {q : ℕ} (hcard : Nat.card E = q ^ 2)
  (hfixed : Nat.card {x : E // J.conj x = x} = q)

include hcard hfixed in
theorem projective_invariant_subgroup (hq : 2 < q)
    (W : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hW : W ≤ projectiveRoot J hJ)
    (hN : projectiveTorus J hJ ≤ normalizer (W : Set _)) :
    W ≤ (frattini (projectiveRoot J hJ)).map (projectiveRoot J hJ).subtype ∨
      W = projectiveRoot J hJ :=
  image_invariant_subgroup J hcard hfixed hq _ (OddPrimeSylow.NormalizedOuter.Coverage.root_injective J hJ)
    _ (projective_torus_action J hJ) W hW hN

omit [Finite E] [CharP E 2] in
private theorem special_root_injective : Function.Injective (hermitianUnipotentSU J hJ) := by
  intro z w h
  apply Subtype.ext
  exact Prod.ext (congrArg (fun x : J.specialSubgroup => x.val.val 0 1) h)
    (congrArg (fun x : J.specialSubgroup => x.val.val 0 2) h)

omit [Finite E] [CharP E 2] in
private theorem special_torus_action (k : Eˣ) (z : hermitianUnipotentCoord J) :
    hermitianTorusSU J hJ k * hermitianUnipotentSU J hJ z * (hermitianTorusSU J hJ k)⁻¹ =
      hermitianUnipotentSU J hJ (hermitianTorusAction J k z) := by
  apply Subtype.ext
  change hermitianTorusGL J k * hermitianUnipotentGL J z * (hermitianTorusGL J k)⁻¹ = _
  rw [hermitianTorusGL_mul_unipotent, mul_inv_cancel_right]
  rfl

include hcard hfixed in
theorem special_invariant_subgroup (hq : 2 < q) (W : Subgroup J.specialSubgroup)
    (hW : W ≤ specialRoot J hJ)
    (hN : specialTorus J hJ ≤ normalizer (W : Set _)) :
    W ≤ (frattini (specialRoot J hJ)).map (specialRoot J hJ).subtype ∨
      W = specialRoot J hJ :=
  image_invariant_subgroup J hcard hfixed hq _ (special_root_injective J hJ)
    _ (special_torus_action J hJ) W hW hN

end BenderSuzuki.MatrixGroups.HermitianForm.BinaryRootFrattini

namespace BenderSuzuki.MatrixGroups.HermitianForm.BinaryRootFrattini
section Transport
variable {G H : Type*} [Group G] [Group H]

theorem frattini_structure_transport (e : G ≃* H)
    (h : (∀ x : G, x ∈ frattini G ↔ x ^ 2 = 1) ∧ frattini G ≤ center G) :
    (∀ x : H, x ∈ frattini H ↔ x ^ 2 = 1) ∧ frattini H ≤ center H := by
  have hm (x : H) : x ∈ frattini H ↔ e.symm x ∈ frattini G := by
    rw [← frattini_map_equiv e, mem_map_equiv]
  constructor
  · intro x
    rw [hm, h.1, ← map_pow, ← e.symm.map_one, e.symm.injective.eq_iff]
  · intro x hx
    have hc := h.2 ((hm x).mp hx)
    apply mem_center_iff.mpr
    intro y
    apply e.symm.injective
    simpa only [map_mul] using mem_center_iff.mp hc (e.symm y)

theorem frattini_image_map (e : G ≃* H) (P : Subgroup G) :
    ((frattini P).map P.subtype).map e.toMonoidHom =
      (frattini (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype := by
  let f := P.equivMapOfInjective e.toMonoidHom e.injective
  rw [← frattini_map_equiv f, map_map, map_map]
  rfl

theorem invariant_transport (e : G ≃* H) (P D : Subgroup G)
    (hmodel : ∀ W : Subgroup H, W ≤ P.map e.toMonoidHom →
      D.map e.toMonoidHom ≤ normalizer (W : Set H) →
      W ≤ (frattini (P.map e.toMonoidHom)).map (P.map e.toMonoidHom).subtype ∨
        W = P.map e.toMonoidHom)
    (W : Subgroup G) (hW : W ≤ P) (hN : D ≤ normalizer (W : Set G)) :
    W ≤ (frattini P).map P.subtype ∨ W = P := by
  have hn : D.map e.toMonoidHom ≤ normalizer (W.map e.toMonoidHom : Set H) := by
    rw [← map_equiv_normalizer_eq]
    exact map_mono hN
  obtain hs | ht := hmodel (W.map e.toMonoidHom) (map_mono hW) hn
  · left
    rw [← frattini_image_map] at hs
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hs (mem_map_of_mem e.toMonoidHom hx)
    exact e.injective hyx ▸ hy
  · exact Or.inr (Subgroup.map_injective e.injective ht)
end Transport
end BenderSuzuki.MatrixGroups.HermitianForm.BinaryRootFrattini
