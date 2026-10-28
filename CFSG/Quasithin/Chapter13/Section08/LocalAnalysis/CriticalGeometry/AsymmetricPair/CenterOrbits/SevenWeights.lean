module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.AsymmetricPair.CenterOrbits.Basic
public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
import Mathlib.Tactic

/-!
# Weight-two centers in the natural seven-point module

An order-two center in the actual quotient action has only two possible
model displacements: zero and its nonidentity vector. For a moved coordinate
`i`, the core vector `eᵢ - 𝟙` has displacement `e_{g i} + eᵢ`, which is
nonzero and has weight two. This proves the center weight directly from the
commutator-image condition, without assuming a transposition or fixed-space
codimension.

Double transitivity moves that pair to coordinates 4 and 5. The literal
marking of a vector in V₂ by `e₄ + e₅`, together with Z ≤ V₂, then lifts
through `CenterQuotientAction.place_of_model` to ambient conjugate containment.
These zero-based coordinates are the source's `e₅,₆` marking in 13.7.6(3b).

The argument does not require ambient finiteness or a separate disjointness
hypothesis: the nontrivial center condition and order two already force the
center image to be nonzero. The actual model and marking remain explicit inputs
for the source-theorem assembly.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.7.6(3b), printed pp.938–939, and the S₇ case of (*) in 13.8.7, printed p.949.
-/

public section

open Subgroup BinaryPermutation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair

private theorem coordinate_core (i : Fin 7) :
    Pi.single i (1 : ZMod 2) - allOne (Fin 7) ∈ core (Fin 7) := by
  change augmentation (Fin 7) _ = 0
  have hs : augmentation (Fin 7) (Pi.single i (1 : ZMod 2)) = 1 := by
    simp [augmentation]
  rw [map_sub, hs, augmentation_allOne]
  decide

private theorem coordinate_displacement (g : Equiv.Perm (Fin 7)) (i : Fin 7) :
    representation _ g (Pi.single i 1 - allOne (Fin 7)) -
      (Pi.single i 1 - allOne (Fin 7)) = Pi.single (g i) 1 + Pi.single i 1 := by
  rw [map_sub, permute_allOne, sub_sub_sub_cancel_right]
  have hs : representation (Fin 7) g (Pi.single i 1) = Pi.single (g i) 1 := by
    ext j
    simp [Pi.single_apply, Equiv.symm_apply_eq]
  rw [hs]
  ext k
  exact CharTwo.sub_eq_add _ _

private theorem weight_two_of_displacement
    (g : Equiv.Perm (Fin 7)) (hg : g ≠ 1) (x : core (Fin 7))
    (hd : ∀ v : core (Fin 7), coreRepresentation _ g v - v = 0 ∨
      coreRepresentation _ g v - v = x) :
    ∃ i j : Fin 7, i ≠ j ∧ x.val = Pi.single i 1 + Pi.single j 1 := by
  obtain ⟨i, hi⟩ : ∃ i, g i ≠ i := by
    by_contra! h
    exact hg (Equiv.ext h)
  let v : core (Fin 7) := ⟨_, coordinate_core i⟩
  have he : (coreRepresentation _ g v - v).val =
      Pi.single (g i) 1 + Pi.single i 1 := coordinate_displacement g i
  rcases hd v with hz | hx
  · have hn := congrFun (he.symm.trans (congrArg Subtype.val hz)) (g i)
    simp [hi] at hn
  · exact ⟨g i, i, hi, (congrArg Subtype.val hx).symm.trans he⟩

variable {G : Type*} [Group G] {H U Z : Subgroup G}
  [(Z.subgroupOf U).Normal] [IsElementaryAbelian 2 U]

private theorem model_displacement_cases
    (Q : CenterQuotientAction H U Z)
    {K E : Type*} [Group K] [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : Representation (ZMod 2) K E} (M : Q.Model ρ)
    (A : Subgroup G) (hA : A ≤ U) (hcard : Nat.card A = 2)
    (hc : Q.IsNontrivialCenter A) (a : A) (ha : (a : G) ≠ 1) :
    ∃ g : K, g ≠ 1 ∧ ∀ v : E, ρ g v - v = 0 ∨
      ρ g v - v = M.moduleEquiv (CenterQuotientAction.vector (Z := Z) ⟨a, hA a.property⟩) := by
  obtain ⟨t, ht, hd⟩ := hc
  let t' : Q.action.range := ⟨Q.action t, ⟨t, rfl⟩⟩
  refine ⟨M.groupEquiv t', ?_, ?_⟩
  · intro h
    exact ht (congrArg Subtype.val (M.groupEquiv.injective (h.trans M.groupEquiv.map_one.symm)))
  · intro v
    let w : U ⧸ Z.subgroupOf U := Additive.toMul (M.moduleEquiv.symm v)
    have hv : M.moduleEquiv (Additive.ofMul w) = v := M.moduleEquiv.apply_symm_apply v
    have he : M.moduleEquiv (Additive.ofMul (w⁻¹ * Q.action t w)) =
        ρ (M.groupEquiv t') v - v := by
      change M.moduleEquiv (-Additive.ofMul w + Additive.ofMul (Q.action t w)) = _
      rw [map_add, map_neg, M.intertwines t', hv]
      exact neg_add_eq_sub _ _
    obtain ⟨u, hu, huq⟩ := hd w
    have huA : (u : G) ∈ A := hu
    have hu_cases : (u : G) = 1 ∨ (u : G) = a := by
      obtain ⟨c, _, hlast⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
      by_cases h1 : (u : G) = 1
      · exact Or.inl h1
      · exact Or.inr (congrArg Subtype.val
          ((hlast ⟨u, huA⟩ (fun hh => h1 (congrArg Subtype.val hh))).trans
            (hlast a (fun hh => ha (congrArg Subtype.val hh))).symm))
    rw [← huq] at he
    rcases hu_cases with hu1 | hua
    · left
      have hu1' : u = 1 := Subtype.ext hu1
      simpa only [hu1', map_one, show Additive.ofMul (1 : U ⧸ Z.subgroupOf U) = 0 from rfl,
        map_zero] using he.symm
    · right
      have hua' : u = ⟨a, hA a.property⟩ := Subtype.ext hua
      exact he.symm.trans (congrArg (fun u => M.moduleEquiv
        (CenterQuotientAction.vector (Z := Z) u)) hua')

/-- Every nonidentity element of an order-two nontrivial center has weight two
in the underlying full seven-point permutation module. -/
theorem seven_center_weight_two
    (Q : CenterQuotientAction H U Z)
    (M : Q.Model (coreRepresentation (Fin 7)))
    (A : Subgroup G) (hA : A ≤ U) (hcard : Nat.card A = 2)
    (hc : Q.IsNontrivialCenter A) (a : A) (ha : (a : G) ≠ 1) :
    ∃ i j : Fin 7, i ≠ j ∧
      (M.moduleEquiv (CenterQuotientAction.vector (Z := Z) ⟨a, hA a.property⟩)).val =
        Pi.single i 1 + Pi.single j 1 := by
  obtain ⟨g, hg, hd⟩ := model_displacement_cases Q M A hA hcard hc a ha
  exact weight_two_of_displacement g hg _ hd

/-- The genuine `e₅,₆` marking of 13.7.6(3b) places an order-two transvection
center inside V₂ by an element of the ambient acting subgroup H. -/
theorem place_seven_center
    (Q : CenterQuotientAction H U Z)
    (M : Q.Model (coreRepresentation (Fin 7)))
    (A V₂ : Subgroup G) (hA : A ≤ U) (hcard : Nat.card A = 2)
    (hc : Q.IsNontrivialCenter A) (hZ : Z ≤ V₂)
    (b : U) (hb : (b : G) ∈ V₂)
    (hmarked : (M.moduleEquiv (CenterQuotientAction.vector (Z := Z) b)).val =
      Pi.single (4 : Fin 7) 1 + Pi.single 5 1) :
    ∃ h ∈ H, A.conjBy h ≤ V₂ := by
  obtain ⟨a, ha, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hcard
  have ha1 : (a : G) ≠ 1 := fun he => ha (Subtype.ext he)
  obtain ⟨i, j, hij, hv⟩ := seven_center_weight_two Q M A hA hcard hc a ha1
  obtain ⟨m, hi, hj⟩ := (MulAction.is_two_pretransitive_iff.mp
    (Equiv.Perm.isMultiplyPretransitive (Fin 7) 2)) hij
      (show (4 : Fin 7) ≠ 5 by decide)
  apply Q.place_of_model M A V₂ hA hcard hZ a ha1 b hb m
  apply Subtype.ext
  change representation (Fin 7) m
    (M.moduleEquiv (CenterQuotientAction.vector (Z := Z) ⟨a, hA a.property⟩)).val = _
  rw [hv, hmarked]
  change m i = 4 at hi
  change m j = 5 at hj
  ext k
  simp [Pi.single_apply, Equiv.symm_apply_eq, hi, hj]

end CFSG.Quasithin.Chapter13.Section08.CriticalGeometry.AsymmetricPair

end
