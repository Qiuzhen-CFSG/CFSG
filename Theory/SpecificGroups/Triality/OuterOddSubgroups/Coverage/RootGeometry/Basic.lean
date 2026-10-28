module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootFrame
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.Normalization
public import Theory.SpecificGroups.Triality.TwoLocalCover.ApartmentStabilizer.Opposition

/-!
# Opposite unipotents and recognition of the two triality nodes

Opposition uses the published longest relative Weyl word in the original
central quotient. The proved opposite-Borel intersection and the disjointness
of the unipotent subgroup and torus show that the two unipotents are disjoint.

The pinned rank-one embeddings prove injectivity of the literal simple-root
parameter maps; Weyl conjugation supplies the negative signs. Thus the signed
root groups have orders q³ and q, distinguishing their nodes even at q = 2.
This removes the node permutation once an automorphism is proved to send each
signed simple-root group to some simple-root group of the same sign.

Source: Steinberg, Theorem 30(1) and Theorem 36,
`refs/KGroup/GLS3/Chapter2St1.tex`; GLS3 §§2.3–2.5,
`refs/KGroup/GLS3/chapter2.tex`. Opposite alignment and geometric recognition
are not assumed to follow merely from these cardinality calculations.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.OuterOdd.Coverage.RootGeometry
open Parabolics ConcreteBruhat
open Matrix
open scoped MatrixGroups

/-- The opposite of the actual positive subgroup, using the published longest word. -/
def oppositeUnipotent (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (unipotent P).map (MulAut.conj (weylRepresentative P hp (.r 3))).toMonoidHom

def oppositeBorel (P : Parameters) (hp : P.prime = 2) : Subgroup (Carrier P) :=
  (borel P).map (MulAut.conj (weylRepresentative P hp (.r 3))).toMonoidHom

theorem normalizer_oppositeUnipotent (P : Parameters) (hp : P.prime = 2) :
    Subgroup.normalizer (oppositeUnipotent P hp) = oppositeBorel P hp := by
  rw [oppositeUnipotent, ← Subgroup.map_equiv_normalizer_eq,
    normalizer_unipotent_eq_borel P hp]
  rfl

/-- Opposition is taken inside the original central quotient. -/
theorem disjoint_unipotent_opposite (f : ℕ) (hf : 0 < f) :
    Disjoint (unipotent (binaryParameters f hf))
      (oppositeUnipotent (binaryParameters f hf) rfl) := by
  let P := binaryParameters f hf
  apply Subgroup.disjoint_def.mpr
  intro x hx hy
  obtain ⟨y, hy, he⟩ := hy
  change weylRepresentative P rfl (.r 3) * y *
    (weylRepresentative P rfl (.r 3))⁻¹ = x at he
  have hb : (weylRepresentative P rfl (.r 3))⁻¹ * x *
      weylRepresentative P rfl (.r 3) ∈ borel P := by
    rw [← he]
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using
      unipotent_le_borel P hy
  have ht := TwoLocalGeometry.ApartmentStabilizer.borel_opposition_intersection f hf
    (unipotent_le_borel P hx) hb
  exact Subgroup.disjoint_def.mp (disjoint_unipotent_torus P rfl) hx ht

private abbrev upper (F : Type*) [Field F] (t : F) : SL(2, F) :=
  SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) (by decide) t

private theorem upper_injective (F : Type*) [Field F] : Function.Injective (upper F) := by
  intro s t h
  have he := congrArg (fun A : SL(2, F) => A.val 0 1) h
  simpa [upper, SpecialLinearGroup.transvection_coe, Matrix.transvection] using he

private theorem positiveRoot_injective (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    Function.Injective (positiveRoot P i) := by
  intro s t h
  exact upper_injective (ExtensionField P) ((pinnedRankOneMaps P hp).injective i
    (((pinnedRankOneMaps P hp).positive i s).trans
      (h.trans ((pinnedRankOneMaps P hp).positive i t).symm)))

private theorem foldedRoot_positive_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (ElementaryCentralKernel.foldedRoot P true) := by
  let := rankOneExtensionCharTwo P hp
  let D := pinnedRankOneMaps P hp
  let C := armRootCommutation P hp
  let tuple (t : ExtensionField P) :=
    ((upper (ExtensionField P) t, upper (ExtensionField P) (fieldFrobenius P t)),
      upper (ExtensionField P) (fieldFrobenius P (fieldFrobenius P t)))
  have htuple (t : ExtensionField P) :
      D.armsProduct C (tuple t) = ElementaryCentralKernel.foldedRoot P true t := by
    simp only [PinnedRankOneMaps.armsProduct_apply, tuple, upper, D.positive]
    rfl
  intro s t h
  have he := D.armsProduct_injective C ((htuple s).trans (h.trans (htuple t).symm))
  exact upper_injective (ExtensionField P) (congrArg (fun v => v.1.1) he)

private theorem positive_rootElement_injective (P : Parameters) (hp : P.prime = 2)
    (i : Node) : Function.Injective (rootElement P hp true i) := by
  intro s t h
  have he := congrArg (elementaryInclusion P) (ElementaryCentralKernel.toCarrier_injective P hp h)
  cases i with
  | arms => exact foldedRoot_positive_injective P hp he
  | central => exact Subtype.ext (positiveRoot_injective P hp 1 he)

/-- No parameter is identified by the actual elementary central quotient. -/
theorem rootElement_injective (P : Parameters) (hp : P.prime = 2)
    (s : Bool) (i : Node) : Function.Injective (rootElement P hp s i) := by
  cases s
  · intro t u h
    apply positive_rootElement_injective P hp i
    have he := (simpleRepresentative_positive P hp i t).trans
      (h.trans (simpleRepresentative_positive P hp i u).symm)
    exact mul_left_cancel (mul_right_cancel he)
  · exact positive_rootElement_injective P hp i

/-- The two node sizes stay distinct at q = 2. -/
theorem card_root_range (P : Parameters) (hp : P.prime = 2) (s : Bool) (i : Node) :
    Nat.card (Set.range (rootElement P hp s i)) =
      (match i with | .arms => P.q ^ 3 | .central => P.q) := by
  rw [Nat.card_range_of_injective (rootElement_injective P hp s i)]
  cases i
  · exact card_extensionField P
  · exact card_fixedField P

/-- An automorphism sending one signed simple-root group to another preserves its node. -/
theorem node_eq_of_root_image (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) (s t : Bool) (i j : Node)
    (h : a '' Set.range (rootElement P hp s i) = Set.range (rootElement P hp t j)) :
    i = j := by
  have hc := (Nat.card_image_of_injective a.injective
    (Set.range (rootElement P hp s i))).symm.trans
      (congrArg (fun S : Set (Carrier P) => Nat.card S) h)
  rw [card_root_range, card_root_range] at hc
  have hlt : P.q < P.q ^ 3 := by
    simpa only [pow_one] using Nat.pow_lt_pow_right
      (show 1 < P.q by have := P.q_ge_two; omega) (show 1 < 3 by decide)
  cases i <;> cases j
  · rfl
  · exact (hlt.ne' hc).elim
  · exact (hlt.ne hc).elim
  · rfl

/-- Once the signed simple-root groups are recognized, their unequal orders
discharge the possible permutation without any small-field exception. -/
theorem preservesRootFrame_of_root_images (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P))
    (h : ∀ s i, ∃ j,
      a '' Set.range (rootElement P hp s i) = Set.range (rootElement P hp s j)) :
    PreservesRootFrame P hp a := by
  intro s i
  obtain ⟨j, hj⟩ := h s i
  exact node_eq_of_root_image P hp a s s i j hj ▸ hj

/-- A further conjugation from U preserves the first Sylow normalization. -/
theorem unipotent_invariant_after_conj (P : Parameters) (a : MulAut (Carrier P))
    (ha : (unipotent P).map a.toMonoidHom = unipotent P)
    (u : Carrier P) (hu : u ∈ unipotent P) :
    (unipotent P).map (MulAut.conj u * a).toMonoidHom = unipotent P := by
  change (unipotent P).map ((MulAut.conj u).toMonoidHom.comp a.toMonoidHom) = _
  rw [← Subgroup.map_map, ha]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp ((unipotent P).le_normalizer hu)

end Triality.Standard.OuterOdd.Coverage.RootGeometry
