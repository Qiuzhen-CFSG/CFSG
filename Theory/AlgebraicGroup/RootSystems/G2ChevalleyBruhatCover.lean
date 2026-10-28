module

public import Theory.AlgebraicGroup.RootSystems.G2ChevalleyMixedWordTermination
public import Theory.AlgebraicGroup.Variety.AffineSpace
import all Theory.AlgebraicGroup.RootSystems.G2ChevalleyMixedWordTermination

/-!
# Explicit G2 Chevalley Bruhat cover

This module packages the characteristic-free explicit Bruhat cover of the
closed `G2` Chevalley carrier.  It first records the finite rank-two Weyl
combinatorics: the twelve roots are split into the chosen positive and negative
halves, and the two simple-reflection tables from
`G2ChevalleyRepresentation` are collected into twelve normal forms for the
Weyl action.

The geometric part builds regular maps from a fixed affine cell
`A^6 × dVariety k 2 × A^6` into the carrier.  The coordinates are multiplied
as six negative root curves, one canonical Weyl lift, one split-torus point,
and six positive root curves.  The root-collection and Borel-Weyl exchange
normal form from the lower G2 matrix modules converts every generator word in
the carrier into one of these finitely many cells, including words containing
torus generators by moving the final torus factor across the positive root
coordinates.

All ingredients are the axiom-clean integral `G2` Chevalley matrices, closed
carrier, root curves, root-collection identities, Weyl-lift identities, and
finite mixed-word termination package.  The local `import all` edge is only to
reuse the implementation equations of that concrete mixed-word package while
keeping this module's public interface theorem-based.  No root exhaustiveness,
semisimplicity, center calculation, or general classification result is used.
-/

namespace Theory.AlgebraicGroup.G2Chevalley

@[expose] public section

/-- The six positive roots in the fixed Chevalley order. -/
def positiveRoots : List Root :=
  [Root.short, Root.long, Root.shortLong, Root.twoShortLong,
    Root.threeShortLong, Root.threeShortTwoLong]

/-- The six negative roots in the fixed Chevalley order. -/
def negativeRoots : List Root :=
  [Root.negShort, Root.negLong, Root.negShortLong, Root.negTwoShortLong,
    Root.negThreeShortLong, Root.negThreeShortTwoLong]

theorem mem_positiveRoots_iff (r : Root) :
    r ∈ positiveRoots ↔ r.val < 6 := by
  fin_cases r <;> simp [positiveRoots, Root.short, Root.long, Root.shortLong,
    Root.twoShortLong, Root.threeShortLong, Root.threeShortTwoLong]

theorem mem_negativeRoots_iff (r : Root) :
    r ∈ negativeRoots ↔ 6 ≤ r.val := by
  fin_cases r <;> simp [negativeRoots, Root.negShort, Root.negLong,
    Root.negShortLong, Root.negTwoShortLong, Root.negThreeShortLong,
    Root.negThreeShortTwoLong]

/-- Apply a word in the two simple reflections to the explicit root set. -/
def weylWordAction : List (Fin 2) → Root → Root
  | [], r => r
  | i :: w, r => weylWordAction w (simpleReflection i r)

/-- Twelve normal-form words for the `G2` Weyl action. -/
def allWeylWords : List (List (Fin 2)) :=
  [[],
    [0], [1],
    [0, 1], [1, 0],
    [0, 1, 0], [1, 0, 1],
    [0, 1, 0, 1], [1, 0, 1, 0],
    [0, 1, 0, 1, 0], [1, 0, 1, 0, 1],
    [0, 1, 0, 1, 0, 1]]

/-- Two words are equivalent if they induce the same permutation of the root set. -/
def weylWordEquivalent (u v : List (Fin 2)) : Prop :=
  ∀ r : Root, weylWordAction u r = weylWordAction v r

/-- The listed Weyl normal forms are syntactically distinct. -/
theorem allWeylWords_nodup : allWeylWords.Nodup := by
  decide

/-- The root permutation attached to a Weyl word. -/
def weylWordSignature (w : List (Fin 2)) : Root → Root :=
  fun r => weylWordAction w r

/-- The listed words induce twelve distinct root permutations. -/
theorem allWeylWordSignatures_nodup :
    (allWeylWords.map weylWordSignature).Nodup := by
  decide

/-- Each simple reflection is an involution on the explicit root set. -/
theorem simpleReflection_involutive (i : Fin 2) (r : Root) :
    simpleReflection i (simpleReflection i r) = r := by
  fin_cases i <;> fin_cases r <;> rfl

/-- The longest listed Weyl word acts by negating every root. -/
theorem longestWeylWord_neg (r : Root) :
    weylWordAction [0, 1, 0, 1, 0, 1] r = -r := by
  fin_cases r <;> rfl

/-- The rank-two `G2` braid relation for the explicit root action. -/
theorem braid_six :
    weylWordEquivalent [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] [] := by
  intro r
  fin_cases r <;> rfl

private theorem simple_cons_reduces (i : Fin 2) {v : List (Fin 2)}
    (hv : v ∈ allWeylWords) :
    ∃ u ∈ allWeylWords, weylWordEquivalent (i :: v) u := by
  fin_cases i <;>
    simp [allWeylWords, weylWordEquivalent] at hv ⊢ <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

/-- Every word in the two simple reflections is represented by one of the
twelve listed normal forms as a root permutation. -/
theorem exists_allWeylWords_equivalent :
    ∀ w : List (Fin 2), ∃ v ∈ allWeylWords, weylWordEquivalent w v
  | [] => by
      refine ⟨[], ?_, ?_⟩
      · simp [allWeylWords]
      · intro r
        rfl
  | i :: w => by
      obtain ⟨v, hv, hveq⟩ := exists_allWeylWords_equivalent w
      obtain ⟨u, hu, hueq⟩ := simple_cons_reduces i hv
      refine ⟨u, hu, ?_⟩
      intro r
      calc
        weylWordAction (i :: w) r = weylWordAction w (simpleReflection i r) := rfl
        _ = weylWordAction v (simpleReflection i r) := hveq (simpleReflection i r)
        _ = weylWordAction (i :: v) r := rfl
        _ = weylWordAction u r := hueq r

end

public section

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A universe-aligned six-coordinate index for the affine root factors in a
Bruhat cell. -/
abbrev BruhatSix := ULift.{u} (Fin 6)

/-- The common domain of the explicit G2 Bruhat cells:
six negative-root coordinates, a rank-two split torus point, and six
positive-root coordinates. -/
noncomputable abbrev BruhatCellDomain (k : Type u) [Field k] [IsAlgClosed k] :
    Variety k :=
  Variety.prod (affineSpaceVariety k BruhatSix)
    (Variety.prod (dVariety k 2) (affineSpaceVariety k BruhatSix))

private noncomputable def affineSixCoordinateMorphism (i : Fin 6) :
    Variety.Morphism (affineSpaceVariety k BruhatSix) (KPlus k) where
  toFun := fun x => kPlusPoint (x.val (ULift.up i))
  regular := by
    intro c
    refine ⟨MvPolynomial.X (ULift.up i), ?_⟩
    intro x
    rw [show c = PUnit.unit by rfl]
    change x.val (ULift.up i) = evalPolynomial x.val (MvPolynomial.X (ULift.up i))
    rw [evalPolynomial_X]

private noncomputable def pointwiseProductMorphism {X : Variety k}
    (fs : List (Variety.Morphism X (Carrier (k := k)))) :
    Variety.Morphism X (Carrier (k := k)) :=
  match fs with
  | [] => Variety.Morphism.const X (Carrier (k := k)) 1
  | f :: fs =>
      (mulMorphism (Carrier (k := k))).comp
        (f.pair (pointwiseProductMorphism fs))

private theorem pointwiseProductMorphism_apply {X : Variety k}
    (fs : List (Variety.Morphism X (Carrier (k := k)))) (x : Variety.Point X) :
    (pointwiseProductMorphism (k := k) fs).toFun x =
      (fs.map fun f => f.toFun x).prod := by
  induction fs with
  | nil =>
      rfl
  | cons f fs ih =>
      simp [pointwiseProductMorphism, Variety.Morphism.comp, Variety.Morphism.pair,
        Variety.prodPointEquiv, mulMorphism, ih]

private noncomputable def bruhatNegativeProjection :
    Variety.Morphism (BruhatCellDomain k) (affineSpaceVariety k BruhatSix) :=
  Variety.Morphism.fst _ _

private noncomputable def bruhatMiddleProjection :
    Variety.Morphism (BruhatCellDomain k)
      (Variety.prod (dVariety k 2) (affineSpaceVariety k BruhatSix)) :=
  Variety.Morphism.snd _ _

private noncomputable def bruhatTorusProjection :
    Variety.Morphism (BruhatCellDomain k) (dVariety k 2) :=
  (Variety.Morphism.fst _ _).comp (bruhatMiddleProjection (k := k))

private noncomputable def bruhatPositiveProjection :
    Variety.Morphism (BruhatCellDomain k) (affineSpaceVariety k BruhatSix) :=
  (Variety.Morphism.snd _ _).comp (bruhatMiddleProjection (k := k))

private noncomputable def carrierRootCoordinateMorphism {X : Variety k}
    (projection : Variety.Morphism X (affineSpaceVariety k BruhatSix))
    (r : Fin 6 → Root) (i : Fin 6) :
    Variety.Morphism X (Carrier (k := k)) :=
  (rootMorphism (k := k) (r i)).toVariety.comp
    ((affineSixCoordinateMorphism (k := k) i).comp projection)

private noncomputable def carrierNegativeRootProductMorphism :
    Variety.Morphism (BruhatCellDomain k) (Carrier (k := k)) :=
  pointwiseProductMorphism (k := k)
    (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i =>
      carrierRootCoordinateMorphism (k := k) (bruhatNegativeProjection (k := k))
        (fun i => -positiveConvexRoot i) i)

private noncomputable def carrierPositiveRootProductMorphism :
    Variety.Morphism (BruhatCellDomain k) (Carrier (k := k)) :=
  pointwiseProductMorphism (k := k)
    (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i =>
      carrierRootCoordinateMorphism (k := k) (bruhatPositiveProjection (k := k))
        positiveConvexRoot i)

private theorem carrierNegativeRootProductMorphism_apply
    (z : Variety.Point (BruhatCellDomain k)) :
    (carrierNegativeRootProductMorphism (k := k)).toFun z =
      carrierNegativeRootProduct (k := k)
        (fun i => ((bruhatNegativeProjection (k := k)).toFun z).val (ULift.up i)) := by
  simp [carrierNegativeRootProductMorphism, carrierNegativeRootProduct,
    carrierRootCoordinateMorphism, carrierRootFactor, pointwiseProductMorphism_apply,
    affineSixCoordinateMorphism, bruhatNegativeProjection,
    Variety.Morphism.comp, Theory.AlgebraicGroup.Morphism.onPoints]

private theorem carrierPositiveRootProductMorphism_apply
    (z : Variety.Point (BruhatCellDomain k)) :
    (carrierPositiveRootProductMorphism (k := k)).toFun z =
      carrierPositiveRootProduct (k := k)
        (fun i => ((bruhatPositiveProjection (k := k)).toFun z).val (ULift.up i)) := by
  simp [carrierPositiveRootProductMorphism, carrierPositiveRootProduct,
    carrierRootCoordinateMorphism, pointwiseProductMorphism_apply,
    affineSixCoordinateMorphism, bruhatPositiveProjection,
    Variety.Morphism.comp, Theory.AlgebraicGroup.Morphism.onPoints]

private noncomputable def carrierTorusMorphism :
    Variety.Morphism (BruhatCellDomain k) (Carrier (k := k)) :=
  (splitTorusMorphism (k := k)).toVariety.comp (bruhatTorusProjection (k := k))

private noncomputable def carrierWeylConstantMorphism (j : Fin 12) :
    Variety.Morphism (BruhatCellDomain k) (Carrier (k := k)) :=
  Variety.Morphism.const _ _ (carrierWeylWord (k := k) (canonicalWeylWord j))

/-- The regular morphism parametrizing the `j`th explicit G2 Bruhat cell. -/
noncomputable def bruhatCellMorphism (j : Fin 12) :
    Variety.Morphism (BruhatCellDomain k) (Carrier (k := k)) :=
  pointwiseProductMorphism (k := k)
    [carrierNegativeRootProductMorphism (k := k),
      carrierWeylConstantMorphism (k := k) j,
      carrierTorusMorphism (k := k),
      carrierPositiveRootProductMorphism (k := k)]

/-- Extract the six negative-root coordinates from a Bruhat-cell parameter. -/
noncomputable def bruhatCellNegativeParameters
    (z : Variety.Point (BruhatCellDomain k)) : Fin 6 → k :=
  fun i => ((bruhatNegativeProjection (k := k)).toFun z).val (ULift.up i)

/-- Extract the split-torus coordinate from a Bruhat-cell parameter. -/
noncomputable def bruhatCellTorusParameter
    (z : Variety.Point (BruhatCellDomain k)) : Variety.Point (dVariety k 2) :=
  (bruhatTorusProjection (k := k)).toFun z

/-- Extract the six positive-root coordinates from a Bruhat-cell parameter. -/
noncomputable def bruhatCellPositiveParameters
    (z : Variety.Point (BruhatCellDomain k)) : Fin 6 → k :=
  fun i => ((bruhatPositiveProjection (k := k)).toFun z).val (ULift.up i)

/-- The pointwise formula for the `j`th explicit G2 Bruhat cell. -/
noncomputable def bruhatCellPoint (j : Fin 12)
    (z : Variety.Point (BruhatCellDomain k)) : CarrierPoint (k := k) :=
  carrierNegativeRootProduct (k := k) (bruhatCellNegativeParameters (k := k) z) *
    carrierWeylWord (k := k) (canonicalWeylWord j) *
      (splitTorusMorphism (k := k)).onPoints (bruhatCellTorusParameter (k := k) z) *
        carrierPositiveRootProduct (k := k) (bruhatCellPositiveParameters (k := k) z)

/-- The regular Bruhat-cell morphism evaluates to the stated negative,
Weyl, torus, positive product. -/
theorem bruhatCellMorphism_apply (j : Fin 12)
    (z : Variety.Point (BruhatCellDomain k)) :
    (bruhatCellMorphism (k := k) j).toFun z = bruhatCellPoint (k := k) j z := by
  simp [bruhatCellMorphism, bruhatCellPoint, bruhatCellTorusParameter,
    carrierNegativeRootProductMorphism_apply, carrierPositiveRootProductMorphism_apply,
    carrierTorusMorphism, carrierWeylConstantMorphism,
    pointwiseProductMorphism_apply, Variety.Morphism.comp,
    Variety.Morphism.const, Theory.AlgebraicGroup.Morphism.onPoints]
  rw [show (fun i : Fin 6 =>
        ((bruhatNegativeProjection (k := k)).toFun z).val (ULift.up i)) =
        bruhatCellNegativeParameters (k := k) z by rfl,
      show (fun i : Fin 6 =>
        ((bruhatPositiveProjection (k := k)).toFun z).val (ULift.up i)) =
        bruhatCellPositiveParameters (k := k) z by rfl]
  group

private noncomputable def bruhatCellDomainPoint (aNeg : Fin 6 → k)
    (t : Variety.Point (dVariety k 2)) (aPos : Fin 6 → k) :
    Variety.Point (BruhatCellDomain k) :=
  (Variety.prodPointEquiv _ _).symm
    (affineSpacePoint (fun i : BruhatSix => aNeg i.down),
      (Variety.prodPointEquiv _ _).symm
        (t, affineSpacePoint (fun i : BruhatSix => aPos i.down)))

private theorem bruhatCellDomainPoint_negative (aNeg : Fin 6 → k)
    (t : Variety.Point (dVariety k 2)) (aPos : Fin 6 → k) :
    bruhatCellNegativeParameters (k := k)
      (bruhatCellDomainPoint (k := k) aNeg t aPos) = aNeg := by
  funext i
  simp [bruhatCellNegativeParameters, bruhatNegativeProjection,
    bruhatCellDomainPoint, affineSpacePoint, Variety.Morphism.fst, Variety.prodPointEquiv]

private theorem bruhatCellDomainPoint_torus (aNeg : Fin 6 → k)
    (t : Variety.Point (dVariety k 2)) (aPos : Fin 6 → k) :
    bruhatCellTorusParameter (k := k)
      (bruhatCellDomainPoint (k := k) aNeg t aPos) = t := by
  simp [bruhatCellTorusParameter, bruhatTorusProjection, bruhatMiddleProjection,
    bruhatCellDomainPoint, Variety.Morphism.comp, Variety.Morphism.fst,
    Variety.Morphism.snd, Variety.prodPointEquiv]

private theorem bruhatCellDomainPoint_positive (aNeg : Fin 6 → k)
    (t : Variety.Point (dVariety k 2)) (aPos : Fin 6 → k) :
    bruhatCellPositiveParameters (k := k)
      (bruhatCellDomainPoint (k := k) aNeg t aPos) = aPos := by
  funext i
  simp [bruhatCellPositiveParameters, bruhatPositiveProjection, bruhatMiddleProjection,
    bruhatCellDomainPoint, affineSpacePoint, Variety.Morphism.comp, Variety.Morphism.snd,
    Variety.prodPointEquiv]

/-- Every finite word in the twelve root curves lands in one of the explicit
regular G2 Bruhat cells. -/
theorem exists_bruhatCell_of_carrierRootWord (word : List (Root × k)) :
    ∃ j : Fin 12, ∃ z : Variety.Point (BruhatCellDomain k),
      carrierRootWordProduct (k := k) word =
        (bruhatCellMorphism (k := k) j).toFun z := by
  obtain ⟨aNeg, j, t, aPos, h⟩ :=
    exists_carrierRootWord_mixed_normalForm (k := k) word
  refine ⟨j, bruhatCellDomainPoint (k := k) aNeg t aPos, ?_⟩
  rw [bruhatCellMorphism_apply]
  rw [h]
  simp [bruhatCellPoint, bruhatCellDomainPoint_negative,
    bruhatCellDomainPoint_torus, bruhatCellDomainPoint_positive]

private noncomputable abbrev H (t : Variety.Point (dVariety k 2)) :
    CarrierPoint (k := k) :=
  (splitTorusMorphism (k := k)).onPoints t

private lemma H_mul (t s : Variety.Point (dVariety k 2)) :
    H (k := k) t * H s = H (t * s) := by
  exact ((splitTorusMorphism (k := k)).onPoints.map_mul t s).symm

private lemma H_one : H (k := k) 1 = 1 := by
  exact (splitTorusMorphism (k := k)).onPoints.map_one

private lemma H_inv (t : Variety.Point (dVariety k 2)) :
    (H (k := k) t)⁻¹ = H t⁻¹ := by
  exact ((splitTorusMorphism (k := k)).onPoints.map_inv t).symm

private noncomputable def torusScale (r : Root)
    (t : Variety.Point (dVariety k 2)) : k := by
  letI := (splitTorus (k := k)).carrierAlgebraicGroup
  exact (rootWeight (k := k) r).pointCharacter
    ((splitTorusIso (k := k)).hom.onPoints t)

private lemma carrierRootFactor_move_torus_right (r : Root) (a : k)
    (t : Variety.Point (dVariety k 2)) :
    carrierRootFactor (k := k) r a * H t =
      H t * carrierRootFactor r (torusScale r t * a) := by
  let _ : AlgebraicGroup (splitTorus (k := k)).carrierVariety :=
    (splitTorus (k := k)).carrierAlgebraicGroup
  have h := rootMorphism_splitTorus_conjugation (k := k) r a
    ((splitTorusIso (k := k)).hom.onPoints t)
  change ((splitTorus (k := k)).inclusion.onPoints
      ((splitTorusIso (k := k)).hom.onPoints t))⁻¹ * carrierRootFactor r a *
      (splitTorus (k := k)).inclusion.onPoints
        ((splitTorusIso (k := k)).hom.onPoints t) =
    carrierRootFactor r (torusScale r t * a) at h
  have h' : (H (k := k) t)⁻¹ * carrierRootFactor r a * H t =
      carrierRootFactor r (torusScale r t * a) := by
    simpa only [H, splitTorusIso_inclusion_apply] using h
  calc
    carrierRootFactor (k := k) r a * H t =
        H t * ((H t)⁻¹ * carrierRootFactor r a * H t) := by group
    _ = H t * carrierRootFactor r (torusScale r t * a) := by rw [h']

private lemma carrierRootFactor_move_torus_left (r : Root) (a : k)
    (t : Variety.Point (dVariety k 2)) :
    H t * carrierRootFactor (k := k) r a =
      carrierRootFactor r (torusScale r t⁻¹ * a) * H t := by
  have h := carrierRootFactor_move_torus_right (k := k) r a t⁻¹
  rw [← H_inv] at h
  calc
    H t * carrierRootFactor (k := k) r a =
        H t * (carrierRootFactor r a * (H t)⁻¹) * H t := by group
    _ = H t * ((H t)⁻¹ * carrierRootFactor r (torusScale r t⁻¹ * a)) * H t := by
      rw [h]
    _ = carrierRootFactor r (torusScale r t⁻¹ * a) * H t := by group

private noncomputable def torusMovedRootWord
    (t : Variety.Point (dVariety k 2)) (word : List (Root × k)) :
    List (Root × k) :=
  word.map fun z => (z.1, torusScale (k := k) z.1 t⁻¹ * z.2)

private lemma H_mul_carrierRootWordProduct
    (t : Variety.Point (dVariety k 2)) (word : List (Root × k)) :
    H (k := k) t * carrierRootWordProduct (k := k) word =
      carrierRootWordProduct (k := k) (torusMovedRootWord (k := k) t word) * H t := by
  induction word with
  | nil =>
      simp [carrierRootWordProduct, torusMovedRootWord]
  | cons z word ih =>
      rcases z with ⟨r, a⟩
      change H (k := k) t * (carrierRootFactor r a *
          carrierRootWordProduct (k := k) word) =
        carrierRootFactor r (torusScale r t⁻¹ * a) *
          carrierRootWordProduct (torusMovedRootWord t word) * H t
      calc
        H (k := k) t * (carrierRootFactor r a *
            carrierRootWordProduct (k := k) word) =
            (H t * carrierRootFactor r a) *
              carrierRootWordProduct (k := k) word := by group
        _ = (carrierRootFactor r (torusScale r t⁻¹ * a) * H t) *
              carrierRootWordProduct (k := k) word := by
            rw [carrierRootFactor_move_torus_left]
        _ = carrierRootFactor r (torusScale r t⁻¹ * a) *
              (H t * carrierRootWordProduct (k := k) word) := by group
        _ = carrierRootFactor r (torusScale r t⁻¹ * a) *
              (carrierRootWordProduct (torusMovedRootWord t word) * H t) := by
            rw [ih]
        _ = (carrierRootFactor r (torusScale r t⁻¹ * a) *
              carrierRootWordProduct (torusMovedRootWord t word)) * H t := by group

private noncomputable def torusMovedRootWordRight
    (t : Variety.Point (dVariety k 2)) (word : List (Root × k)) :
    List (Root × k) :=
  word.map fun z => (z.1, torusScale (k := k) z.1 t * z.2)

private lemma carrierRootWordProduct_mul_H
    (word : List (Root × k)) (t : Variety.Point (dVariety k 2)) :
    carrierRootWordProduct (k := k) word * H (k := k) t =
      H t * carrierRootWordProduct (k := k) (torusMovedRootWordRight (k := k) t word) := by
  induction word with
  | nil =>
      simp [carrierRootWordProduct, torusMovedRootWordRight]
  | cons z word ih =>
      rcases z with ⟨r, a⟩
      change (carrierRootFactor r a * carrierRootWordProduct (k := k) word) * H (k := k) t =
        H t * (carrierRootFactor r (torusScale r t * a) *
          carrierRootWordProduct (torusMovedRootWordRight t word))
      calc
        (carrierRootFactor r a * carrierRootWordProduct (k := k) word) * H (k := k) t =
            carrierRootFactor r a *
              (carrierRootWordProduct (k := k) word * H t) := by group
        _ = carrierRootFactor r a *
              (H t * carrierRootWordProduct (torusMovedRootWordRight t word)) := by
            rw [ih]
        _ = (carrierRootFactor r a * H t) *
              carrierRootWordProduct (torusMovedRootWordRight t word) := by group
        _ = (H t * carrierRootFactor r (torusScale r t * a)) *
              carrierRootWordProduct (torusMovedRootWordRight t word) := by
            rw [carrierRootFactor_move_torus_right]
        _ = H t * (carrierRootFactor r (torusScale r t * a) *
              carrierRootWordProduct (torusMovedRootWordRight t word)) := by group

private noncomputable def positiveParametersMovedByTorus
    (t : Variety.Point (dVariety k 2)) (a : Fin 6 → k) : Fin 6 → k :=
  fun i => torusScale (k := k) (positiveConvexRoot i) t * a i

private lemma carrierPositiveRootProduct_move_torus_right
    (a : Fin 6 → k) (t : Variety.Point (dVariety k 2)) :
    carrierPositiveRootProduct (k := k) a * H t =
      H t * carrierPositiveRootProduct
        (k := k) (positiveParametersMovedByTorus (k := k) t a) := by
  simpa [carrierPositiveRootProduct, positiveParametersMovedByTorus,
    carrierRootWordProduct, carrierRootFactor, torusMovedRootWordRight] using
    carrierRootWordProduct_mul_H (k := k)
      (([0, 1, 2, 3, 4, 5] : List (Fin 6)).map fun i => (positiveConvexRoot i, a i)) t

private inductive CarrierGeneratorAtom where
  | root (r : Root) (a : k)
  | torus (t : Variety.Point (dVariety k 2))

private noncomputable def carrierGeneratorAtomPoint :
    CarrierGeneratorAtom (k := k) → CarrierPoint (k := k)
  | .root r a => carrierRootFactor (k := k) r a
  | .torus t => H (k := k) t

private noncomputable def carrierGeneratorWordProduct
    (word : List (CarrierGeneratorAtom (k := k))) : CarrierPoint (k := k) :=
  (word.map carrierGeneratorAtomPoint).prod

private noncomputable def carrierGeneratorRootWordAndTorus :
    List (CarrierGeneratorAtom (k := k)) →
      List (Root × k) × Variety.Point (dVariety k 2)
  | [] => ([], 1)
  | .root r a :: word =>
      let q := carrierGeneratorRootWordAndTorus word
      ((r, a) :: q.1, q.2)
  | .torus t :: word =>
      let q := carrierGeneratorRootWordAndTorus word
      (torusMovedRootWord (k := k) t q.1, t * q.2)

private lemma carrierGeneratorWordProduct_eq_rootWord_torus
    (word : List (CarrierGeneratorAtom (k := k))) :
    carrierGeneratorWordProduct (k := k) word =
      carrierRootWordProduct (k := k) (carrierGeneratorRootWordAndTorus (k := k) word).1 *
        H (k := k) (carrierGeneratorRootWordAndTorus (k := k) word).2 := by
  induction word with
  | nil =>
      simp [carrierGeneratorWordProduct, carrierRootWordProduct,
        carrierGeneratorRootWordAndTorus, H_one]
  | cons atom word ih =>
      cases atom with
      | root r a =>
          change carrierRootFactor r a * carrierGeneratorWordProduct (k := k) word =
            carrierRootFactor r a *
              carrierRootWordProduct (carrierGeneratorRootWordAndTorus (k := k) word).1 *
                H (carrierGeneratorRootWordAndTorus (k := k) word).2
          rw [ih]
          group
      | torus t =>
          change H (k := k) t * carrierGeneratorWordProduct (k := k) word =
            carrierRootWordProduct
                (torusMovedRootWord t (carrierGeneratorRootWordAndTorus (k := k) word).1) *
              H (t * (carrierGeneratorRootWordAndTorus (k := k) word).2)
          rw [ih]
          calc
            H (k := k) t *
                (carrierRootWordProduct (carrierGeneratorRootWordAndTorus (k := k) word).1 *
                  H (carrierGeneratorRootWordAndTorus (k := k) word).2) =
                (H t *
                  carrierRootWordProduct (carrierGeneratorRootWordAndTorus (k := k) word).1) *
                    H (carrierGeneratorRootWordAndTorus (k := k) word).2 := by group
            _ = (carrierRootWordProduct
                    (torusMovedRootWord t (carrierGeneratorRootWordAndTorus (k := k) word).1) *
                  H t) *
                    H (carrierGeneratorRootWordAndTorus (k := k) word).2 := by
                rw [H_mul_carrierRootWordProduct]
            _ = carrierRootWordProduct
                    (torusMovedRootWord t (carrierGeneratorRootWordAndTorus (k := k) word).1) *
                  H (t * (carrierGeneratorRootWordAndTorus (k := k) word).2) := by
                calc
                  (carrierRootWordProduct
                        (torusMovedRootWord t (carrierGeneratorRootWordAndTorus (k := k) word).1) *
                      H t) *
                        H (carrierGeneratorRootWordAndTorus (k := k) word).2 =
                      carrierRootWordProduct
                          (torusMovedRootWord t (carrierGeneratorRootWordAndTorus (k := k) word).1) *
                        (H t * H (carrierGeneratorRootWordAndTorus (k := k) word).2) := by
                          group
                  _ = carrierRootWordProduct
                          (torusMovedRootWord t (carrierGeneratorRootWordAndTorus (k := k) word).1) *
                        H (t * (carrierGeneratorRootWordAndTorus (k := k) word).2) := by
                          rw [H_mul]

private lemma normalForm_mul_torus_eq_bruhatCellMorphism
    (aNeg : Fin 6 → k) (j : Fin 12)
    (t s : Variety.Point (dVariety k 2)) (aPos : Fin 6 → k) :
    (carrierNegativeRootProduct (k := k) aNeg *
          carrierWeylWord (k := k) (canonicalWeylWord j) *
            H (k := k) t * carrierPositiveRootProduct (k := k) aPos) *
        H s =
      (bruhatCellMorphism (k := k) j).toFun
        (bruhatCellDomainPoint (k := k) aNeg (t * s)
          (positiveParametersMovedByTorus (k := k) s aPos)) := by
  rw [bruhatCellMorphism_apply]
  unfold bruhatCellPoint
  rw [bruhatCellDomainPoint_negative, bruhatCellDomainPoint_torus,
    bruhatCellDomainPoint_positive]
  let n := carrierNegativeRootProduct (k := k) aNeg
  let w := carrierWeylWord (k := k) (canonicalWeylWord j)
  let p := carrierPositiveRootProduct (k := k) aPos
  let p' := carrierPositiveRootProduct (k := k) (positiveParametersMovedByTorus (k := k) s aPos)
  have hp : p * H (k := k) s = H s * p' := by
    simpa [p, p'] using
      carrierPositiveRootProduct_move_torus_right (k := k) aPos s
  have ht : H (k := k) t * p * H s = H (t * s) * p' := by
    calc
      H (k := k) t * p * H s = H t * (p * H s) := by group
      _ = H t * (H s * p') := by rw [hp]
      _ = (H t * H s) * p' := by group
      _ = H (t * s) * p' := by rw [H_mul]
  change (n * w * H (k := k) t * p) * H s = n * w * H (t * s) * p'
  calc
    (n * w * H (k := k) t * p) * H s =
        n * w * (H t * p * H s) := by group
    _ = n * w * (H (t * s) * p') := by rw [ht]
    _ = n * w * H (t * s) * p' := by group

private theorem exists_bruhatCell_of_carrierGeneratorWord
    (word : List (CarrierGeneratorAtom (k := k))) :
    ∃ j : Fin 12, ∃ z : Variety.Point (BruhatCellDomain k),
      carrierGeneratorWordProduct (k := k) word =
        (bruhatCellMorphism (k := k) j).toFun z := by
  let q := carrierGeneratorRootWordAndTorus (k := k) word
  obtain ⟨aNeg, j, t, aPos, h⟩ :=
    exists_carrierRootWord_mixed_normalForm (k := k) q.1
  refine ⟨j, bruhatCellDomainPoint (k := k) aNeg
    (t * q.2) (positiveParametersMovedByTorus (k := k) q.2 aPos), ?_⟩
  rw [carrierGeneratorWordProduct_eq_rootWord_torus]
  change carrierRootWordProduct (k := k) q.1 * H (k := k) q.2 = _
  rw [h]
  exact normalForm_mul_torus_eq_bruhatCellMorphism (k := k) aNeg j t q.2 aPos

private theorem exists_carrierGeneratorAtom_of_mem_generatorFamily
    (i : Option Root) {g : Variety.Point (Ambient k)}
    (hg : g ∈ (generatorFamily (k := k) i : Set (Variety.Point (Ambient k)))) :
    ∃ atom : CarrierGeneratorAtom (k := k),
      (ambientClosedCarrier (k := k)).inclusion.onPoints
        (carrierGeneratorAtomPoint (k := k) atom) = g := by
  cases i with
  | none =>
      change g ∈ (torusAmbientMorphism (k := k)).image at hg
      rcases hg with ⟨t, rfl⟩
      refine ⟨.torus t, ?_⟩
      simp [carrierGeneratorAtomPoint, H, splitTorusMorphism_inclusion_apply]
  | some r =>
      change g ∈ (rootAmbientMorphism (k := k) r).image at hg
      rcases hg with ⟨q, rfl⟩
      refine ⟨.root r (q.val PUnit.unit), ?_⟩
      have hq : kPlusPoint (q.val PUnit.unit) = q := by
        apply (additiveGroupPointEquiv k).injective
        rfl
      simp [carrierGeneratorAtomPoint, carrierRootFactor,
        rootMorphism_inclusion_apply, hq]

private theorem exists_carrierGeneratorWord_of_closedSubgroupWordProduct :
    ∀ (w : List (Option Root)) {g : Variety.Point (Ambient k)},
      g ∈ closedSubgroupWordProduct (generatorFamily (k := k)) w →
        ∃ atoms : List (CarrierGeneratorAtom (k := k)),
          (ambientClosedCarrier (k := k)).inclusion.onPoints
              (carrierGeneratorWordProduct (k := k) atoms) = g
  | [], g, hg => by
      have hg' : g = 1 := by simpa [closedSubgroupWordProduct] using hg
      subst g
      refine ⟨[], ?_⟩
      simp [carrierGeneratorWordProduct]
  | i :: w, g, hg => by
      rcases Set.mem_mul.mp (by simpa [closedSubgroupWordProduct] using hg) with
        ⟨a, ha, b, hb, hab⟩
      obtain ⟨atom, hatom⟩ :=
        exists_carrierGeneratorAtom_of_mem_generatorFamily (k := k) i ha
      obtain ⟨atoms, hatoms⟩ :=
        exists_carrierGeneratorWord_of_closedSubgroupWordProduct w hb
      refine ⟨atom :: atoms, ?_⟩
      change (ambientClosedCarrier (k := k)).inclusion.onPoints
          (carrierGeneratorAtomPoint (k := k) atom *
            carrierGeneratorWordProduct (k := k) atoms) = g
      rw [map_mul, hatom, hatoms, hab]

/-- The finitely many explicit G2 Bruhat cells cover the closed Chevalley
carrier. -/
theorem carrier_bruhatCell_cover (x : CarrierPoint (k := k)) :
    ∃ j : Fin 12, ∃ z : Variety.Point (BruhatCellDomain k),
      x = (bruhatCellMorphism (k := k) j).toFun z := by
  obtain ⟨w, hw⟩ :=
    exists_closedSubgroupWordProduct_eq_closure_iUnion
      (generatorFamily (k := k)) (generatorFamily_connected (k := k))
  have hx :
      (ambientClosedCarrier (k := k)).inclusion.onPoints x ∈
        closedSubgroupWordProduct (generatorFamily (k := k)) w := by
    rw [hw]
    change ((ambientClosedCarrier (k := k)).pointEquiv x).val ∈
      ambientCarrierSubgroup (k := k)
    exact ((ambientClosedCarrier (k := k)).pointEquiv x).property
  obtain ⟨atoms, hatoms⟩ :=
    exists_carrierGeneratorWord_of_closedSubgroupWordProduct (k := k) w hx
  obtain ⟨j, z, hcell⟩ :=
    exists_bruhatCell_of_carrierGeneratorWord (k := k) atoms
  refine ⟨j, z, ?_⟩
  apply (ambientClosedCarrier (k := k)).inclusion_injective
  rw [← hcell]
  exact hatoms.symm

end

end Theory.AlgebraicGroup.G2Chevalley
