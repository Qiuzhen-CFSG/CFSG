module

public import Theory.GroupTheory.SylowOuterSolvability
public import CFSG.Quasithin.ChapterI.Section03.SylowAutomorphisms
public import Theory.GroupTheory.Covering
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# The A.3.9 outer-solvability step from an actual Sylow restriction

The proved finite-simple S₂ theorem supplies solvability of the pointwise
Sylow fixer. Solvability of the actual Sylow automorphism group then gives
full outer solvability by Sylow conjugacy and restriction. Perfect central
descent passes this result to a quasisimple group.

For Q=L/O(L), the perfect ambient actor therefore has trivial outer image.
Lifting the inner implementer through the literal odd-core quotient proves
G=L C_G(Q). The local Aut(P) solvability premise remains explicit; no model
realization, full Schreier conclusion, or trivial outer image is assumed.
In particular this conditional route does not complete the Held or Rudvalis
model cases of the full Theorem C companion.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Proposition A.3.9,
pp.45–46; the S₂ input is the genuine finite-simple fixer theorem exported
by Chapter I, Section 3.
-/

namespace CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
open Subgroup Theory.GroupTheory

/-- S₂ supplies the pointwise-fixer half of the literal Sylow restriction
argument. Only the automorphism group of this actual Sylow remains local. -/
public theorem simple_outer_isSolvable_of_sylowAut
    {S : Type*} [Group S] [Finite S] [IsSimpleGroup S]
    (P : Sylow 2 S) [Group.IsSolvable (MulAut P)] :
    Group.IsSolvable (MulAut.Outer S) := by
  let : Group.IsSolvable (fixingSubgroup (MulAut S) (P : Set S)) :=
    ChapterI.SylowAutomorphisms.simple_fixingSubgroup_solvable P
  exact MulAut.outer_isSolvable_of_sylow_aut P

/-- The actual central quotient is the simple group to which S₂ applies. -/
public theorem quasisimple_outer_isSolvable_of_sylowAut
    {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (P : Sylow 2 (Q ⧸ center Q)) [Group.IsSolvable (MulAut P)] :
    Group.IsSolvable (MulAut.Outer Q) := by
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  let := simple_outer_isSolvable_of_sylowAut P
  exact Group.isSolvable_of_isSolvable_injective
    (MulAut.centralQuotientOuter_injective (MulEquiv.refl (Q ⧸ center Q)))

/-- The A.3.9 perfect-actor equality follows from the actual simple
central quotient's Sylow automorphism group; the outer image is derived
trivial rather than supplied as an assumption. -/
public theorem perfect_actor_sup_oddCore_quotient_centralizer_of_sylowAut
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (L : Subgroup G) [L.Normal]
    (hQ : IsQuasisimple (L ⧸ pPrimeCore 2 L))
    (P : Sylow 2 ((L ⧸ pPrimeCore 2 L) ⧸ center (L ⧸ pPrimeCore 2 L)))
    [Group.IsSolvable (MulAut P)] :
    L ⊔ (normalQuotientAction L (pPrimeCore 2 L)).ker = ⊤ := by
  let Q := L ⧸ pPrimeCore 2 L
  let : IsQuasisimple Q := hQ
  let : Group.IsSolvable (MulAut.Outer Q) :=
    quasisimple_outer_isSolvable_of_sylowAut P
  let a := normalQuotientAction L (pPrimeCore 2 L)
  let f : G →* MulAut.Outer Q :=
    (QuotientGroup.mk' (MulAut.innerSubgroup Q)).comp a
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hs : Subsingleton f.range := by
    by_contra! hn
    exact Group.IsPerfect.not_isSolvable f.range inferInstance
  have hf (g : G) : f g = 1 := congrArg f.range.subtype
    (hs.elim (⟨f g, ⟨g, rfl⟩⟩ : f.range) 1)
  apply top_unique
  intro g _
  have hi : a g ∈ MulAut.innerSubgroup Q := (QuotientGroup.eq_one_iff _).mp (hf g)
  obtain ⟨q, hq⟩ := hi
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) q
  have hl : a (l : G) = a g :=
    (normalQuotientAction_inner L (pPrimeCore 2 L) l).trans hq
  have hk : (l : G)⁻¹ * g ∈ a.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hl, inv_mul_cancel]
  have hm := (L ⊔ a.ker).mul_mem (mem_sup_left l.property) (mem_sup_right hk)
  simpa only [mul_inv_cancel_left] using hm

end CFSG.Quasithin.Chapter1.XiEmbedding.OuterModels
