module

public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Solvability of automorphisms preserving a subgroup

If N_G(A) and Out(G) are solvable, every group of automorphisms preserving
A is solvable. Its intersection with the inner automorphisms lies in the
image of N_G(A), and its quotient by that intersection embeds in Out(G).

Applied to ambient conjugation on a normal subgroup L, this makes the
induced action on V solvable whenever N_L(V) is solvable. The quotient is
by the actual centralizer of V in the original actor subgroup.

Source: the normalizer-action argument in Aschbacher--Smith I.8.5(2),
printed p.430; elementary solvable extension theory.
-/

noncomputable section
namespace MulAut
open Subgroup

/-- A subgroup-preserving group of automorphisms is solvable when its
inner part and outer quotient are solvable. -/
public theorem isSolvable_of_preserves_subgroup
    {G : Type*} [Group G] (A : Subgroup G)
    [Group.IsSolvable (normalizer (A : Set G))] [Group.IsSolvable (Outer G)]
    (H : Subgroup (MulAut G))
    (hH : ∀ a : H, ∀ x : G, x ∈ A ↔ (a : MulAut G) x ∈ A) :
    Group.IsSolvable H := by
  let c : normalizer (A : Set G) →* MulAut G :=
    (MulAut.conj : G →* MulAut G).comp (normalizer (A : Set G)).subtype
  let q : H →* Outer G := (QuotientGroup.mk' (innerSubgroup G)).comp H.subtype
  have hker : q.ker.map H.subtype ≤ c.range := by
    rintro a ⟨b, hb, rfl⟩
    have hb' : (b : MulAut G) ∈ innerSubgroup G := (QuotientGroup.eq_one_iff _).mp hb
    obtain ⟨g, hg⟩ := hb'
    have hgA : g ∈ normalizer (A : Set G) := by
      apply mem_normalizer_iff.mpr
      intro x
      simpa only [← hg, MulAut.conj_apply] using hH b x
    exact ⟨⟨g, hgA⟩, hg⟩
  let k : q.ker →* c.range := (H.subtype.comp q.ker.subtype).codRestrict c.range
    (fun b => hker (mem_map_of_mem H.subtype b.property))
  have hk : Function.Injective k := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : c.range => (a : MulAut G)) he
  let : Group.IsSolvable c.range := Group.isSolvable_of_surjective c.rangeRestrict_surjective
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective hk
  exact Group.isSolvable_of_ker_le_range q.ker.subtype q (by rw [range_subtype])

/-- The original actor modulo C_M(V) is solvable if L is normal, M
normalizes V≤L, and N_L(V) and Out(L) are solvable. -/
public theorem isSolvable_quotient_centralizer_of_normalizer
    {G : Type*} [Group G] (L M V : Subgroup G) [L.Normal]
    [(V.subgroupOf M).Normal] (hVL : V ≤ L)
    (hMV : M ≤ normalizer (V : Set G))
    [Group.IsSolvable (normalizer (V.subgroupOf L : Set L))]
    [Group.IsSolvable (Outer L)] :
    Group.IsSolvable (M ⧸ centralizer (V.subgroupOf M : Set M)) := by
  let f : M →* MulAut L := (MulAut.conjNormal : G →* MulAut L).comp M.subtype
  have hpres : ∀ a : f.range, ∀ x : L,
      x ∈ V.subgroupOf L ↔ (a : MulAut L) x ∈ V.subgroupOf L := by
    rintro ⟨a, m, rfl⟩ x
    exact mem_normalizer_iff.mp (hMV m.property) (x : G)
  let : Group.IsSolvable f.range :=
    isSolvable_of_preserves_subgroup (V.subgroupOf L) f.range hpres
  let C := centralizer (V.subgroupOf M : Set M)
  have hker : f.ker ≤ C := by
    intro m hm v hv
    have he := congrArg (fun a : MulAut L => (a ⟨v, hVL hv⟩ : G)) hm
    change (m : G) * (v : G) * (m : G)⁻¹ = v at he
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  let : Group.IsSolvable (M ⧸ f.ker) :=
    Group.isSolvable_of_isSolvable_injective (QuotientGroup.quotientKerEquivRange f).injective
  let q : M →* M ⧸ C := QuotientGroup.mk' C
  have hkerq : f.ker ≤ q.ker := by rwa [QuotientGroup.ker_mk']
  exact Group.isSolvable_of_surjective
    (QuotientGroup.lift_surjective_of_surjective f.ker q (QuotientGroup.mk'_surjective C) hkerq)

end MulAut
