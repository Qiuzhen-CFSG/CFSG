module
public import Theory.GroupAction.InnerSylow
/-!
# Sylow normalizers under an inner prime-group action

A prime subgroup S normalizing L and containing an intrinsic Sylow P of L
has no additional inner actors beyond the inner image of P. If every
S-action is inner, S is the product of the embedded P and C_S(L).
Consequently the intrinsic normalizer of P in L normalizes all of S.

The proof uses Sylow maximality in Inn(L), with no assumption that L is
centerless or normal in the full ambient group. This supplies the Borel
normalization step for Aschbacher--Smith 15.1.22(4), printed p.1099.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- An intrinsic Sylow normalizer normalizes any containing prime group whose action is inner. -/
theorem embedded_sylow_normalizer_le_of_inner
    (L S : Subgroup G) (hn : S ≤ normalizer (L : Set G)) (hS : IsPGroup p S)
    (P : Sylow p L) (hPS : (P : Subgroup L).map L.subtype ≤ S)
    (hi : ∀ s : S, L.normalizerMonoidHom (inclusion hn s) ∈ MulAut.innerSubgroup L) :
    (normalizer (P : Set L)).map L.subtype ≤ normalizer (S : Set G) := by
  let a := L.normalizerMonoidHom.comp (inclusion hn)
  let A := a.range
  let R := (P : Subgroup L).map L.subtype
  let C := S ⊓ centralizer (L : Set G)
  have hA : IsPGroup p A := hS.of_surjective a.rangeRestrict a.rangeRestrict_surjective
  have hPA : (P : Subgroup L).map MulAut.conj ≤ A := by
    rintro _ ⟨u,hu,rfl⟩
    refine ⟨⟨u,hPS (mem_map_of_mem L.subtype hu)⟩,?_⟩
    ext x
    rfl
  have hsplit : S = R ⊔ C := by
    apply le_antisymm _ (sup_le hPS inf_le_left)
    intro s hs
    obtain ⟨u,hu,heu⟩ := MulAut.mem_innerSylow_of_mem_inner P A hA hPA
      (show a ⟨s,hs⟩ ∈ A from ⟨⟨s,hs⟩,rfl⟩) (hi ⟨s,hs⟩)
    have huR : (u : G) ∈ R := mem_map_of_mem L.subtype hu
    have hcS : (u : G)⁻¹*s ∈ S := S.mul_mem (S.inv_mem (hPS huR)) hs
    have hc : (u : G)⁻¹*s ∈ centralizer (L : Set G) := by
      intro x hx
      have he := congrArg Subtype.val (DFunLike.congr_fun heu (⟨x,hx⟩ : L))
      change (u : G)*x*(u : G)⁻¹ = s*x*s⁻¹ at he
      have he' : ((u : G)⁻¹*s)*x*((u : G)⁻¹*s)⁻¹ = x := by
        calc
          _ = (u : G)⁻¹ * (s*x*s⁻¹) * (u : G) := by group
          _ = (u : G)⁻¹ * ((u : G)*x*(u : G)⁻¹) * (u : G) := by rw [← he]
          _ = x := by group
      exact (mul_inv_eq_iff_eq_mul.mp he').symm
    have hh := (R ⊔ C).mul_mem (mem_sup_left huR) (mem_sup_right ⟨hcS,hc⟩)
    simpa only [mul_inv_cancel_left] using hh
  have hB : (normalizer (P : Set L)).map L.subtype ≤ L := map_subtype_le _
  have hBR : (normalizer (P : Set L)).map L.subtype ≤ normalizer (R : Set G) :=
    le_normalizer_map L.subtype
  have hBC : (normalizer (P : Set L)).map L.subtype ≤ normalizer (C : Set G) :=
    (hB.trans (le_centralizer_iff.mp (show C ≤ centralizer (L : Set G) from inf_le_right))).trans
      (centralizer_le_normalizer _)
  rw [hsplit]
  exact (le_inf hBR hBC).trans (normalizer_inf_normalizer_le_normalizer_sup R C)
end Subgroup
