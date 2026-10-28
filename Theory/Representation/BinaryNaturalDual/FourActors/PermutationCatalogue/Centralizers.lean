module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.PermutationCatalogue.Comparison
public import Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals
public import Mathlib.GroupTheory.Perm.Centralizer

/-!
# The two outer-involution centralizers in the eight-point model

The relative centralizers in A₈ of `(01)` and `(01)(23)(45)` are respectively
S₆ and C₂ × S₄. We construct faithful homomorphisms onto these groups:

* On the six fixed points of `(01)`, an arbitrary permutation determines
  the permutation of its two-point support by parity.
* The existing tetrahedral edge action embeds S₄ into the permutations of
  the first six points. Edge complementation is the odd central involution
  `(01)(23)(45)`; adjoining it gives a faithful C₂ × S₄ action. The final
  two-point action is again determined by parity.

For surjectivity, the cycle-type formula gives full symmetric centralizer
orders 1440 and 96. Sign is surjective on each full centralizer because the
marked involution itself is odd. Thus their intersections with A₈ have orders
720 and 48, exactly the orders of the constructed faithful models.

The specified automorphism/permutation comparison then transports these
actual multiplicative equivalences to the inner centralizers and to the
fixed subgroups of the original natural linear group.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(1),
printed p.391, PDF p.402. The tetrahedral action is reused from
`SymmetricSix.ResidualPairRecognition.ComponentLocals.edgeHom`.
-/

public section

open Equiv Subgroup
open Theory.SpecificGroups.SymmetricEight.Involutions
namespace BinaryNaturalDual.FourActors.PermutationCatalogue

private theorem evenCentralizer_card_mul_two (q : S) (hq : Perm.sign q = -1) :
    Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({q} : Set S) : Subgroup S) * 2 =
      Nat.card (centralizer ({q} : Set S)) := by
  let C := centralizer ({q} : Set S)
  let f : C →* ℤˣ := Perm.sign.comp C.subtype
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, f.map_one⟩
    · exact ⟨⟨q, mem_centralizer_singleton_iff.mpr rfl⟩, hq⟩
  have hk : f.ker = (alternatingGroup (Fin 8) ⊓ C).subgroupOf C := by
    ext x
    change Perm.sign x.val = 1 ↔ x.val ∈ alternatingGroup (Fin 8) ∧ x.val ∈ C
    simp only [Perm.mem_alternatingGroup, x.property, and_true]
  have hc : Nat.card f.ker = Nat.card (alternatingGroup (Fin 8) ⊓ C : Subgroup S) :=
    Nat.card_congr ((MulEquiv.subgroupCongr hk).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)).toEquiv
  have hi : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units_int] using
      Nat.card_congr (Subgroup.topEquiv (G := ℤˣ)).toEquiv
  rw [← hc, ← hi]
  exact f.ker.card_mul_index

private theorem transpositionCentralizer_card :
    Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({onePair} : Set S) : Subgroup S) = 720 := by
  have hc := evenCentralizer_card_mul_two onePair (by decide +kernel)
  rw [Perm.nat_card_centralizer, onePair_cycleType] at hc
  norm_num at hc
  change Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({onePair} : Set S) : Subgroup S) * 2 =
    1440 at hc
  omega

private theorem tripleTranspositionCentralizer_card :
    Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({threePairs} : Set S) : Subgroup S) = 48 := by
  have hc := evenCentralizer_card_mul_two threePairs (by decide +kernel)
  rw [Perm.nat_card_centralizer, threePairs_cycleType] at hc
  norm_num at hc
  change Nat.card (alternatingGroup (Fin 8) ⊓ centralizer ({threePairs} : Set S) : Subgroup S) * 2 =
    96 at hc
  omega

private def parityPerm : ℤˣ →* Perm (Fin 2) where
  toFun u := if u = 1 then 1 else swap 0 1
  map_one' := by decide
  map_mul' := by decide +kernel

private theorem parityPerm_sign : ∀ u, Perm.sign (parityPerm u) = u := by decide +kernel

private def blockHom (m n : ℕ) : Perm (Fin m) × Perm (Fin n) →* Perm (Fin (m + n)) :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n))).toMonoidHom.comp
    (Perm.sumCongrHom _ _)

private theorem blockHom_injective (m n : ℕ) : Function.Injective (blockHom m n) :=
  (Equiv.permCongrHom _).injective.comp Perm.sumCongrHom_injective

private theorem blockHom_sign (m n : ℕ) (p : Perm (Fin m) × Perm (Fin n)) :
    Perm.sign (blockHom m n p) = Perm.sign p.1 * Perm.sign p.2 :=
  (Perm.sign_permCongr _ _).trans (Perm.sign_sumCongr _ _)

private def sixOnRight : Perm (Fin 6) →* S :=
  (blockHom 2 6).comp ((parityPerm.comp Perm.sign).prod (MonoidHom.id _))

private theorem sixOnRight_injective : Function.Injective sixOnRight := by
  intro a b h
  exact congrArg Prod.snd (blockHom_injective 2 6 h)

private theorem sixOnRight_even (a : Perm (Fin 6)) : sixOnRight a ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup]
  change Perm.sign (blockHom 2 6 (parityPerm (Perm.sign a), a)) = 1
  rw [blockHom_sign, parityPerm_sign]
  exact Int.units_mul_self _

private theorem two_commute : ∀ p : Perm (Fin 2), Commute p (swap 0 1) := by
  change ∀ p : Perm (Fin 2), p * swap 0 1 = swap 0 1 * p
  decide +kernel

private theorem sixOnRight_commute (a : Perm (Fin 6)) : Commute (sixOnRight a) onePair := by
  have hp : Commute (parityPerm (Perm.sign a), a) (swap (0 : Fin 2) 1, (1 : Perm (Fin 6))) := by
    apply Prod.ext
    · exact (two_commute _).eq
    · simp
  exact (show blockHom 2 6 (swap 0 1, 1) = onePair by decide +kernel) ▸ hp.map (blockHom 2 6)

private def sixOnRightCentralizer : Perm (Fin 6) →*
    (alternatingGroup (Fin 8) ⊓ centralizer ({onePair} : Set S) : Subgroup S) :=
  sixOnRight.codRestrict _ fun a =>
    ⟨sixOnRight_even a, mem_centralizer_singleton_iff.mpr (sixOnRight_commute a).eq⟩

/-- The full relative centralizer of `(01)` in A₈, parametrized by its six fixed points. -/
noncomputable def onePairCentralizerEquiv :
    (alternatingGroup (Fin 8) ⊓ centralizer ({onePair} : Set S) : Subgroup S) ≃*
      Perm (Fin 6) :=
  (MulEquiv.ofBijective sixOnRightCentralizer
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h =>
      sixOnRight_injective (congrArg Subtype.val h), by
        rw [transpositionCentralizer_card, Nat.card_eq_fintype_card, Fintype.card_perm]
        decide⟩)).symm

open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition.ComponentLocals

private def complementHom : Multiplicative (ZMod 2) →* Perm (Fin 6) where
  toFun c := if c = 1 then 1 else synthemeFlip
  map_one' := by decide
  map_mul' := by decide +kernel

private theorem complementHom_sign (c : Multiplicative (ZMod 2)) :
    Perm.sign (complementHom c) = 1 ↔ c = 1 := by
  revert c
  decide +kernel

private theorem edgeHom_commute : ∀ a, Commute synthemeFlip (edgeHom a) := by
  change ∀ a, synthemeFlip * edgeHom a = edgeHom a * synthemeFlip
  decide +kernel

private theorem complementHom_commute : ∀ c a, Commute (complementHom c) (edgeHom a) := by
  intro c a
  dsimp only [complementHom, MonoidHom.coe_mk, OneHom.coe_mk]
  split_ifs
  · exact Commute.one_left _
  · exact edgeHom_commute a

private def edgeProduct : Multiplicative (ZMod 2) × Perm (Fin 4) →* Perm (Fin 6) :=
  complementHom.noncommCoprod edgeHom complementHom_commute

private theorem edgeProduct_injective : Function.Injective edgeProduct := by
  apply (injective_iff_map_eq_one edgeProduct).mpr
  intro x hx
  have hc : x.1 = 1 := by
    apply (complementHom_sign x.1).mp
    have hs := congrArg Perm.sign hx
    change Perm.sign (complementHom x.1 * edgeHom x.2) = Perm.sign 1 at hs
    rw [map_mul, Perm.mem_alternatingGroup.mp (edgeHom_even x.2), mul_one, map_one] at hs
    exact hs
  apply Prod.ext hc
  apply edgeHom_injective
  simpa [edgeProduct, MonoidHom.noncommCoprod_apply, hc] using hx

private theorem edgeProduct_commute (x : Multiplicative (ZMod 2) × Perm (Fin 4)) :
    Commute (edgeProduct x) synthemeFlip := by
  have hc : Commute (complementHom x.1) synthemeFlip := by
    dsimp only [complementHom, MonoidHom.coe_mk, OneHom.coe_mk]
    split_ifs
    · exact Commute.one_left _
    · exact Commute.refl _
  exact hc.mul_left (edgeHom_commute x.2).symm

private def sixOnLeft : Perm (Fin 6) →* S :=
  (blockHom 6 2).comp ((MonoidHom.id _).prod (parityPerm.comp Perm.sign))

private theorem sixOnLeft_injective : Function.Injective sixOnLeft := by
  intro a b h
  exact congrArg Prod.fst (blockHom_injective 6 2 h)

private theorem sixOnLeft_even (a : Perm (Fin 6)) : sixOnLeft a ∈ alternatingGroup (Fin 8) := by
  rw [Perm.mem_alternatingGroup]
  change Perm.sign (blockHom 6 2 (a, parityPerm (Perm.sign a))) = 1
  rw [blockHom_sign, parityPerm_sign]
  exact Int.units_mul_self _

private theorem edgeProduct_eight_commute (x : Multiplicative (ZMod 2) × Perm (Fin 4)) :
    Commute (sixOnLeft (edgeProduct x)) threePairs := by
  have hp : Commute (edgeProduct x, parityPerm (Perm.sign (edgeProduct x)))
      (synthemeFlip, (1 : Perm (Fin 2))) := by
    apply Prod.ext
    · exact (edgeProduct_commute x).eq
    · simp
  exact (show blockHom 6 2 (synthemeFlip, 1) = threePairs by decide +kernel) ▸ hp.map (blockHom 6 2)

private def edgeCentralizer : Multiplicative (ZMod 2) × Perm (Fin 4) →*
    (alternatingGroup (Fin 8) ⊓ centralizer ({threePairs} : Set S) : Subgroup S) :=
  (sixOnLeft.comp edgeProduct).codRestrict _ fun x =>
    ⟨sixOnLeft_even _, mem_centralizer_singleton_iff.mpr (edgeProduct_eight_commute x).eq⟩

/-- The full relative centralizer of `(01)(23)(45)` in A₈, including the central C₂. -/
noncomputable def threePairsCentralizerEquiv :
    (alternatingGroup (Fin 8) ⊓ centralizer ({threePairs} : Set S) : Subgroup S) ≃*
      (Multiplicative (ZMod 2) × Perm (Fin 4)) :=
  (MulEquiv.ofBijective edgeCentralizer
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨fun _ _ h =>
      edgeProduct_injective (sixOnLeft_injective (congrArg Subtype.val h)), by
        rw [tripleTranspositionCentralizer_card, Nat.card_prod, Nat.card_eq_fintype_card,
          Nat.card_eq_fintype_card, Fintype.card_perm]
        decide⟩)).symm

/-- The transposition actor has inner centralizer S₆ in the marked automorphism group. -/
noncomputable def transpositionCentralizerEquiv :
    innerCentralizer transposition ≃* Perm (Fin 6) :=
  (innerCentralizerPermutationEquiv transposition).trans
    ((MulEquiv.subgroupCongr (by rw [permutationEquiv_transposition])).trans
      onePairCentralizerEquiv)

/-- The triple-transposition actor has inner centralizer C₂ × S₄. -/
noncomputable def tripleTranspositionCentralizerEquiv :
    innerCentralizer tripleTransposition ≃* (Multiplicative (ZMod 2) × Perm (Fin 4)) :=
  (innerCentralizerPermutationEquiv tripleTransposition).trans
    ((MulEquiv.subgroupCongr (by rw [permutationEquiv_tripleTransposition])).trans
      threePairsCentralizerEquiv)

/-- The actual natural linear group fixed by the transposition actor is S₆. -/
noncomputable def transpositionFixedEquiv : transposition.fixedSubgroup ≃* Perm (Fin 6) :=
  (fixedInnerEquiv transposition).trans transpositionCentralizerEquiv

/-- The actual natural linear group fixed by the triple-transposition actor is C₂ × S₄. -/
noncomputable def tripleTranspositionFixedEquiv :
    tripleTransposition.fixedSubgroup ≃* (Multiplicative (ZMod 2) × Perm (Fin 4)) :=
  (fixedInnerEquiv tripleTransposition).trans tripleTranspositionCentralizerEquiv

end BinaryNaturalDual.FourActors.PermutationCatalogue
