module

public import Theory.Representation.Mathieu.M22James.DegreeTwentyFour.ExclusionsTwelve.Induction

/-!
# Transversal coordinates on the induced Mathieu point modules

The actual induction of each natural or dual point constituent is equivalent
to 22 copies of its three-dimensional F₄ carrier. Slot `i` corresponds to
`IndV.mk pointEmbedding (constituent a) (transversal i)⁻¹ v`; the inverse is
the sum of these vectors. The proof uses Frobenius reciprocity and the literal
coinvariant relations, so it respects Mathlib's inverse/right-translation
convention without any semisimplicity assumption.

The action transports slot `i` to `g i` by the point-stabilizer element
`T(g i)⁻¹ g T(i)`. For the two ambient generators, `generator_apply` identifies
this element with the already certified reference Schreier matrix. Thus finite
calculations can use the existing ATLAS-derived data, with field encoding
0, 1, omega, 1 + omega and column vectors. Original attribution remains in
`Uniqueness/PointRestriction/PointModel/source/README.md` and its linked sources;
no external code or unverified matrix data is used in this module.

These coordinates support the degree exclusion used in Guralnick–Malle,
Classification of 2F-modules I, Proposition 5.1, pp.15–16 and Theorem 6.6/Table
6.7. The simple-factor filtrations are separate obligations.
-/

open Representation
open Representation.SL3FourLocalCatalogue
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

@[expose] public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates
open Uniqueness Uniqueness.PointRestriction.PointModel

/-- Twenty-two slots with three F₄ coordinates in each slot. -/
abbrev Space := Fin 22 → Representation.SL3FourLocalCatalogue.W

/-- The literal point-stabilizer correction for the chosen transversal. -/
def cocycle (g : M22TripleCover) (i : Fin 22) : pointStabilizer :=
  ⟨(transversal (corePermutationAction g i))⁻¹ * g * transversal i, by
    rw [mem_pointStabilizer, map_mul, map_mul, map_inv, transversal_action,
      transversal_action]
    change (transversalPermutation (corePermutationAction g i)).symm
      (corePermutationAction g (transversalPermutation i 1)) = 1
    rw [transversal_base]
    apply (transversalPermutation (corePermutationAction g i)).injective
    rw [Equiv.apply_symm_apply, transversal_base]⟩

lemma cocycle_one (i : Fin 22) : cocycle 1 i = 1 := by
  apply Subtype.ext
  simp [cocycle]

lemma cocycle_mul (g h : M22TripleCover) (i : Fin 22) :
    cocycle (g * h) i = cocycle g (corePermutationAction h i) * cocycle h i := by
  apply Subtype.ext
  simp only [cocycle, map_mul, Equiv.Perm.mul_apply, Subgroup.coe_mul]
  group

def action (a : Constituent) (g : M22TripleCover) : Space →ₗ[ZMod 2] Space where
  toFun v j := constituent a
    (pointStabilizerEquiv (cocycle g (corePermutationAction g⁻¹ j)))
    (v (corePermutationAction g⁻¹ j))
  map_add' v w := by
    funext j
    exact map_add _ _ _
  map_smul' c v := by
    funext j
    exact (constituent a _).map_smul c (v _)

/-- The binary action on transversal coordinates. -/
def representation (a : Constituent) : Representation (ZMod 2) M22TripleCover Space where
  toFun := action a
  map_one' := by
    apply LinearMap.ext
    intro v
    funext j
    change constituent a (pointStabilizerEquiv (cocycle 1 (corePermutationAction (1 : M22TripleCover)⁻¹ j))) (v (corePermutationAction (1 : M22TripleCover)⁻¹ j)) = v j
    simp only [inv_one, map_one, Equiv.Perm.one_apply, cocycle_one, Module.End.one_apply]
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    funext j
    change action a (g * h) v j = action a g (action a h v) j
    simp only [action, LinearMap.coe_mk, AddHom.coe_mk,
      mul_inv_rev, map_mul, Equiv.Perm.mul_apply]
    rw [cocycle_mul]
    simp only [map_mul, Module.End.mul_apply]
    simp only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply]

lemma action_apply (a : Constituent) (g : M22TripleCover) (v : Space) (i : Fin 22) :
    representation a g v (corePermutationAction g i) =
      constituent a (pointStabilizerEquiv (cocycle g i)) (v i) := by
  simp [representation, action]

lemma action_single (a : Constituent) (g : M22TripleCover)
    (i : Fin 22) (v : Representation.SL3FourLocalCatalogue.W) :
    representation a g (Pi.single i v) =
      Pi.single (corePermutationAction g i)
        (constituent a (pointStabilizerEquiv (cocycle g i)) v) := by
  funext j
  obtain ⟨j, rfl⟩ := (corePermutationAction g).surjective j
  rw [action_apply]
  by_cases h : j = i
  · subst j
    simp
  · simp [h, (corePermutationAction g).injective.ne h]

lemma cocycle_transversal (i : Fin 22) : cocycle (transversal i) 1 = 1 := by
  apply Subtype.ext
  simp [cocycle, transversal_action, transversal_base, transversal_one]

lemma representation_transversal_single (a : Constituent) (i : Fin 22)
    (v : Representation.SL3FourLocalCatalogue.W) :
    representation a (transversal i) (Pi.single 1 v) = Pi.single i v := by
  rw [action_single, cocycle_transversal]
  simp [transversal_action, transversal_base]

lemma embedding_action (s : Representation.SL3FourLocalCatalogue.SL) :
    corePermutationAction (pointEmbedding s) 1 = 1 :=
  (pointStabilizerEquiv.symm s).property

lemma cocycle_embedding (s : Representation.SL3FourLocalCatalogue.SL) :
    cocycle (pointEmbedding s) 1 = pointStabilizerEquiv.symm s := by
  apply Subtype.ext
  change (transversal (corePermutationAction (pointEmbedding s) 1))⁻¹ *
    pointEmbedding s * transversal 1 = _
  rw [embedding_action, transversal_one]
  simp [pointEmbedding]

def localMap (a : Constituent) :
    IntertwiningMap (constituent a) (pointAction (representation a)) where
  toLinearMap := LinearMap.single (R := ZMod 2)
    (φ := fun _ : Fin 22 => Representation.SL3FourLocalCatalogue.W) 1
  isIntertwining' s := by
    apply LinearMap.ext
    intro v
    change (Pi.single 1 (constituent a s v) : Space) =
      representation a (pointEmbedding s) (Pi.single 1 v)
    rw [action_single, embedding_action, cocycle_embedding]
    simp

def fromInduced (a : Constituent) :
    IntertwiningMap (inducedRepresentation a) (representation a) :=
  inducedMap (representation a) (localMap a)

lemma fromInduced_mk (a : Constituent) (g : M22TripleCover)
    (v : Representation.SL3FourLocalCatalogue.W) :
    fromInduced a (IndV.mk pointEmbedding (constituent a) g v) =
      representation a g⁻¹ (Pi.single 1 v) := by
  simp [fromInduced, inducedMap, localMap]

lemma fromInduced_transversal (a : Constituent) (i : Fin 22)
    (v : Representation.SL3FourLocalCatalogue.W) :
    fromInduced a (IndV.mk pointEmbedding (constituent a) (transversal i)⁻¹ v) =
      Pi.single i v := by
  rw [fromInduced_mk, inv_inv, representation_transversal_single]

def toInduced (a : Constituent) : Space →ₗ[ZMod 2] InducedSpace a :=
  LinearMap.lsum (ZMod 2) (fun _ : Fin 22 => Representation.SL3FourLocalCatalogue.W)
    (ZMod 2) (fun i => IndV.mk pointEmbedding (constituent a) (transversal i)⁻¹)

lemma toInduced_single (a : Constituent) (i : Fin 22)
    (v : Representation.SL3FourLocalCatalogue.W) :
    toInduced a (Pi.single i v) =
      IndV.mk pointEmbedding (constituent a) (transversal i)⁻¹ v :=
  LinearMap.lsum_piSingle _ _ _ _ _ _

lemma mk_relation (a : Constituent) (s : Representation.SL3FourLocalCatalogue.SL)
    (g : M22TripleCover) (v : Representation.SL3FourLocalCatalogue.W) :
    IndV.mk pointEmbedding (constituent a) (pointEmbedding s⁻¹ * g) v =
      IndV.mk pointEmbedding (constituent a) g (constituent a s v) := by
  simpa [IndV.mk, ofMulAction_single] using
    Coinvariants.mk_inv_tmul ((leftRegular (ZMod 2) M22TripleCover).comp pointEmbedding)
      (constituent a) (MonoidAlgebra.single g (1 : ZMod 2)) v s

lemma cocycle_decomposition (g : M22TripleCover) :
    pointEmbedding (pointStabilizerEquiv (cocycle g⁻¹ 1))⁻¹ *
      (transversal (corePermutationAction g⁻¹ 1))⁻¹ = g := by
  rw [map_inv]
  change ((pointStabilizerEquiv.symm
    (pointStabilizerEquiv (cocycle g⁻¹ 1)) : pointStabilizer) : M22TripleCover)⁻¹ * _ = _
  rw [pointStabilizerEquiv.symm_apply_apply]
  simp [cocycle, transversal_one, mul_inv_rev, mul_assoc]

lemma toInduced_fromInduced (a : Constituent) :
    (toInduced a).comp (fromInduced a).toLinearMap = LinearMap.id := by
  apply IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro v
  change toInduced a (fromInduced a (IndV.mk pointEmbedding (constituent a) g v)) =
    IndV.mk pointEmbedding (constituent a) g v
  rw [fromInduced_mk, action_single, toInduced_single, ← mk_relation,
    cocycle_decomposition]

lemma fromInduced_toInduced (a : Constituent) (v : Space) :
    fromInduced a (toInduced a v) = v := by
  change (fromInduced a).toLinearMap (toInduced a v) = v
  simp only [toInduced, LinearMap.lsum_apply, LinearMap.sum_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum]
  change (∑ i, fromInduced a (IndV.mk pointEmbedding (constituent a) (transversal i)⁻¹ (v i))) = v
  simp_rw [fromInduced_transversal]
  exact Finset.univ_sum_single v

/-- An equivalence with Mathlib induction, proved using both explicit inverse identities. -/
def equiv (a : Constituent) : (inducedRepresentation a).Equiv (representation a) :=
  (fromInduced a).ofBijective
    ⟨Function.LeftInverse.injective (g := toInduced a) (fun x => LinearMap.congr_fun (toInduced_fromInduced a) x),
      Function.RightInverse.surjective (fromInduced_toInduced a)⟩

lemma equiv_transversal (a : Constituent) (i : Fin 22)
    (v : Representation.SL3FourLocalCatalogue.W) :
    equiv a (IndV.mk pointEmbedding (constituent a) (transversal i)⁻¹ v) =
      Pi.single i v := fromInduced_transversal a i v

lemma cocycle_generator (i : Fin 22) (j : Fin 2) :
    cocycle (ambientGenerator j) i = schreierGenerator i j := by
  apply Subtype.ext
  simp only [cocycle, schreierGenerator, ambientGenerator_action]

lemma generator_apply (a : Constituent) (j : Fin 2) (v : Space) (i : Fin 22) :
    representation a (ambientGenerator j) v (ambientPermutation j i) =
      constituent a
        (SchreierCertificate.referenceElement (SchreierCertificate.schreierIndex i j)) (v i) := by
  rw [← ambientGenerator_action, action_apply, cocycle_generator]
  have he := schreierGenerator_image_of_natural_action pointStabilizerEquiv.toMonoidHom
    pointStabilizerEquiv_natural_action i j
  change pointStabilizerEquiv (schreierGenerator i j) = _ at he
  rw [he]

lemma space_finrank : Module.finrank (ZMod 2) Space = 132 := by
  rw [Module.finrank_pi_fintype]
  simp only [constituent_finrank, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul]

lemma induced_finrank (a : Constituent) : Module.finrank (ZMod 2) (InducedSpace a) = 132 :=
  (equiv a).toLinearEquiv.finrank_eq.trans space_finrank

lemma constituent_smul (a : Constituent) (s : Representation.SL3FourLocalCatalogue.SL)
    (c : Representation.SL3FourNaturalDual.F) (v : Representation.SL3FourLocalCatalogue.W) :
    constituent a s (c • v) = c • constituent a s v := by
  cases a with
  | natural => exact (specialLinearNatural 3 s).map_smul c v
  | dual => exact (specialLinearNatural 3 (Matrix.SpecialLinearGroup.inverseTranspose s)).map_smul c v

/-- The same action with its actual F₄-linear structure. -/
def fieldRepresentation (a : Constituent) :
    Representation Representation.SL3FourNaturalDual.F M22TripleCover Space where
  toFun g :=
    { toFun := representation a g
      map_add' := (representation a g).map_add
      map_smul' c v := by
        funext j
        exact constituent_smul a _ c (v _) }
  map_one' := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun (representation a).map_one v
  map_mul' g h := by
    apply LinearMap.ext
    intro v
    exact LinearMap.congr_fun ((representation a).map_mul g h) v

lemma fieldRepresentation_restrictScalars (a : Constituent) :
    restrictScalars (k := ZMod 2) (fieldRepresentation a) = representation a := by
  apply MonoidHom.ext
  intro g
  apply LinearMap.ext
  intro v
  rfl

lemma space_field_finrank : Module.finrank Representation.SL3FourNaturalDual.F Space = 66 := by
  change Module.finrank Representation.SL3FourNaturalDual.F
    (Fin 22 → Fin 3 → Representation.SL3FourNaturalDual.F) = 66
  rw [Module.finrank_pi_fintype]
  simp only [Module.finrank_fin_fun, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

end Sporadic.Mathieu.M22TripleCover.DegreeTwentyFour.ExclusionsTwelve.InducedCoordinates

