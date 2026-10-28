module

public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.Contracts
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.PermutationProducts
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.Transpositions
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.Symmetric.FourPairs

/-!
# The two six-dimensional symmetric natural-module calculations

In a subgroup of S₇ containing A₇, an involution with small conjugate
products must be a transposition and consequently cannot have displacement
rank two. In a subgroup of index at most two in S₈, the same bound and
rank two force cycle type `2⁴`; its moved-plane stabilizer is transitive.

Both statements use the literal binary natural permutation section and
its restricted action. No class table or normalizer-transitivity premise
is assumed. `Symmetric.SymplecticBound` proves the explicit conjugate-product
bound, and `Symmetric.Source` assembles the source-model applications.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
G.11.2(4–5), printed p.364 (PDF p.375), and the proof of 6.2.19,
printed p.691 (PDF p.708).
-/

@[expose] public section

namespace Representation.RankTwo.Symmetric
open _root_.Equiv BinaryPermutation

theorem alternating_products_of_small {n : ℕ} (H : Subgroup (Perm (Fin n)))
    (hH : alternatingGroup (Fin n) ≤ H) (v : H) (hb : SmallConjugateProducts v) :
    ∀ g ∈ alternatingGroup (Fin n), orderOf (v.val * (g * v.val * g⁻¹)) ≤ 4 := by
  intro g hg
  have hh := hb ⟨g⁻¹, H.inv_mem (hH hg)⟩
  rw [← Subgroup.orderOf_coe] at hh
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk, inv_inv] using hh

theorem seven_rank_ne_two (H : Subgroup (Perm (Fin 7)))
    (hH : alternatingGroup (Fin 7) ≤ H) (v : H) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hb : SmallConjugateProducts v) :
    Module.finrank (ZMod 2)
      (movedSpace ((naturalRepresentation (Fin 7)).comp H.subtype) v) ≠ 2 := by
  have hne : v.val ≠ 1 := fun h => hv (Subtype.ext h)
  have hp : v.val ^ 2 = 1 := congrArg Subtype.val hv2
  have hs := seven_isSwap v.val hne hp (alternating_products_of_small H hH v hb)
  have hr := natural_isSwap_rank (by decide : 5 ≤ Fintype.card (Fin 7)) v.val hs
  change Module.finrank (ZMod 2) (movedSpace (naturalRepresentation (Fin 7)) v.val) ≠ 2
  omega

theorem eight_stabilizerTransitive (H : Subgroup (Perm (Fin 8)))
    (hH : H.index ≤ 2) (v : H) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hb : SmallConjugateProducts v)
    (hr : Module.finrank (ZMod 2)
      (movedSpace ((naturalRepresentation (Fin 8)).comp H.subtype) v) = 2) :
    StabilizerTransitive ((naturalRepresentation (Fin 8)).comp H.subtype)
      (movedSpace ((naturalRepresentation (Fin 8)).comp H.subtype) v) := by
  have hA := Perm.alternatingGroup_le_of_index_le_two hH
  have hne : v.val ≠ 1 := fun h => hv (Subtype.ext h)
  have hp : v.val ^ 2 = 1 := congrArg Subtype.val hv2
  rcases eight_isSwap_or_four v.val hne hp
    (alternating_products_of_small H hA v hb) with hs | hs
  · have hr1 := natural_isSwap_rank (by decide : 5 ≤ Fintype.card (Fin 8)) v.val hs
    change Module.finrank (ZMod 2) (movedSpace (naturalRepresentation (Fin 8)) v.val) = 2 at hr
    omega
  · exact subgroup_fourPairs_transitive H hA v hs hr

end Representation.RankTwo.Symmetric
