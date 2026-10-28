module
public import Theory.GroupTheory.ElementaryThompsonFrattini
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Thompson subgroups through a residual image

If ker(q) lies in S and q(J(S)) lies in q(R), correcting a lift by the
kernel places J(S) in (S ∩ R)ker(q). This subgroup lies between J(S) and S,
so Thompson heredity identifies its Thompson subgroup with J(S). Every
normalizer of S ∩ R also normalizes the kernel and hence normalizes J(S).

Source application: Aschbacher–Smith 5.1.13, printed p.637, the natural
rank-one comparison J(T) ≤ (T ∩ L)O₂(LT). No Sylow or residual hypothesis
is needed for this transport lemma.
-/

public section
open Subgroup
namespace Stellmacher
variable {G H : Type*} [Group G] [Finite G] [Group H]

omit [Finite G] in
theorem elementaryAbelianMaxJ_le_intersection_sup_ker_of_image
    (S R : Subgroup G) (q : G →* H) (hk : q.ker ≤ S)
    (hj : (elementaryAbelianMaxJ S).map q ≤ R.map q) :
    elementaryAbelianMaxJ S ≤ (S ⊓ R) ⊔ q.ker := by
  let P := (S ⊓ R) ⊔ q.ker
  have hJS : elementaryAbelianMaxJ S ≤ S := sSup_le fun _ hA => hA.1
  have hJP : elementaryAbelianMaxJ S ≤ P := by
    intro x hx
    obtain ⟨r,hr,he⟩ := hj (mem_map_of_mem q hx)
    have hker : r⁻¹ * x ∈ q.ker := by
      change q (r⁻¹ * x) = 1
      rw [map_mul,map_inv,he,inv_mul_cancel]
    have hrS : r ∈ S := by
      have hh := S.mul_mem (hJS hx) (S.inv_mem (hk hker))
      simpa only [mul_inv_rev,inv_inv,mul_inv_cancel_left] using hh
    have hh : r * (r⁻¹ * x) ∈ P :=
      P.mul_mem (Subgroup.mem_sup_left ⟨hrS,hr⟩) (Subgroup.mem_sup_right hker)
    simpa only [mul_inv_cancel_left] using hh
  exact hJP

theorem normalizer_intersection_le_normalizer_maxJ_of_image
    (S R : Subgroup G) (q : G →* H) (hk : q.ker ≤ S)
    (hj : (elementaryAbelianMaxJ S).map q ≤ R.map q) :
    normalizer ((S ⊓ R : Subgroup G) : Set G) ≤ normalizer (elementaryAbelianMaxJ S : Set G) := by
  let P := (S ⊓ R) ⊔ q.ker
  have hJP : elementaryAbelianMaxJ S ≤ P :=
    elementaryAbelianMaxJ_le_intersection_sup_ker_of_image S R q hk hj
  have he : elementaryAbelianMaxJ P = elementaryAbelianMaxJ S :=
    elementaryAbelianMaxJ_eq_of_intermediate S P hJP (sup_le inf_le_left hk)
  have hn : normalizer ((S ⊓ R : Subgroup G) : Set G) ≤ normalizer (P : Set G) := by
    apply (le_inf le_rfl (show normalizer ((S ⊓ R : Subgroup G) : Set G) ≤ normalizer (q.ker : Set G) from
      le_normalizer_of_normal)).trans
    exact normalizer_inf_normalizer_le_normalizer_sup (S ⊓ R) q.ker
  exact hn.trans (he ▸ normalizer_le_normalizer_elementaryAbelianMaxJ P)
end Stellmacher
