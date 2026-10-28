module
public import Theory.GroupTheory.PrimeRankNormalIntersection
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.QuasithinBasic

/-!
# Prime-to-p kernels detected on a subgroup of full rank

In a finite group of p-rank at most two, a homomorphism whose restriction
to a subgroup of p-rank two has prime-to-p kernel has prime-to-p kernel
on the whole group. An elementary plane in the subgroup is disjoint from
the kernel; the normal-intersection theorem excludes p-divisibility.

This is the rank argument used in Aschbacher--Smith A.3.19, pp.54--55,
and in the original-module centralizer in 13.3.12, pp.889--890.
-/

public section
open Subgroup Theory.GroupTheory
namespace MonoidHom
variable {G A : Type*} [Group G] [Finite G] [Group A]
    {p : ℕ} [Fact p.Prime]

/-- A prime-to-p restriction kernel on a rank-two subgroup detects the
prime-to-p kernel on the whole rank-at-most-two group. -/
theorem ker_coprime_of_restriction_rank_two (f : G →* A) (L : Subgroup G)
    (hker : Nat.Coprime p (Nat.card (f.comp L.subtype).ker))
    (hrL : 2 ≤ primeRank p L) (hr : primeRank p G ≤ 2) :
    Nat.Coprime p (Nat.card f.ker) := by
  classical
  have heq : primeRank p L = 2 := le_antisymm
    ((primeRank_le_of_injective p L.subtype L.subtype_injective).trans hr) hrL
  obtain ⟨B,hB,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := L) (p := p)
  let := hB
  let E := B.map L.subtype
  let : IsElementaryAbelian p E := IsElementaryAbelian.map L.subtype
  have hc : Nat.card E = p ^ 2 := by
    rw [card_map_of_injective L.subtype_injective,hcard,heq]
  have hi := injective_comp_subtype_of_coprime_ker (f.comp L.subtype) hker B
    (IsElementaryAbelian.isPGroup p B)
  have hinf : E ⊓ f.ker = ⊥ := by
    apply eq_bot_iff.mpr
    rintro y ⟨⟨b,hb,rfl⟩,hy⟩
    have he : (⟨b,hb⟩ : B) = 1 := hi (by
      change f b = f 1
      rw [map_one]
      exact hy)
    exact congrArg (fun z : B => (z.val : G)) he
  apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
  intro hd
  exact E.inf_ne_bot_of_elementary_plane f.ker
    (by rw [normalizer_eq_top]; exact le_top) hd hc hr hinf

end MonoidHom
