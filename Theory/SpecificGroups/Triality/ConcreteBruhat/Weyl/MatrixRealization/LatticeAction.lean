module

public import Theory.SpecificGroups.Triality.ConcreteBruhat.Weyl.Basic
public import Theory.SpecificGroups.Triality.PositiveRootCoordinates.Collection.SumExchange.CanonicalCoefficients.SimpleReflection
public import Theory.AlgebraicGroup.RootSystems.IntegralRootCurveSimpleGeneration

/-!
# Weyl words on the complete binary D₄ Geck lattice

A simple matrix word is the scalar extension of the integral Tits lift. Its
root block permutes the 24 literal roots, while its Cartan block transforms the
simple-coroot coordinate vectors by the same reflection. Both identities extend
through products and inverses. The root vectors distinguish permutations, and
together with the coroot vectors they span all 28 coordinates, distinguishing
entire matrices even in characteristic two.

The finite Cartan calculation is checked over `ZMod 2` and then transported by
the scalar homomorphism, so no restriction on the field size is needed.
Source: the D₄ reflection construction and GLS3 §§2.3–2.4
(`refs/KGroup/GLS3/chapter2.tex`), using `IntegralGeckConstruction` and the
checked `CanonicalCoefficients.SimpleReflection` matrices.
-/

@[expose] public section
open Theory.AlgebraicGroup.StandardRootSystem
open Triality.Standard.Parabolics.RankOneMatrices
open Triality.Standard.PositiveCoordinates.SumExchangeData
open RootPairing.IntegralGeckConstruction
open scoped BigOperators
open Matrix
namespace Triality.Standard.ConcreteBruhat.MatrixRealization
open Parabolics
noncomputable section
local instance : DecidableEq LatticeIndex := fun a b => instDecidableEqSum a b

/-- The original matrix, with all Cartan and root coordinates enumerated. -/
def matrix (P : Parameters) : SplitGroup P →* Matrix Index Index (ExtensionField P) :=
  (Matrix.reindexRingEquiv (ExtensionField P) latticeEnumeration.symm).toMonoidHom.comp
    ((Units.coeHom _).comp (RootPairing.SimpleGeckGroup.subgroup
      (typeDRootPairing_base 2) (ExtensionField P)).subtype)

lemma matrix_injective (P : Parameters) : Function.Injective (matrix P) := by
  intro g h he
  apply Subtype.ext
  apply Units.ext
  exact (Matrix.reindexRingEquiv (ExtensionField P) latticeEnumeration.symm).injective he

lemma matrix_simple (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    let := rankOneExtensionCharTwo P hp
    matrix P (weylWord P i 1) = (scalarMap (ExtensionField P)).mapMatrix (binaryTits i) := by
  let := rankOneExtensionCharTwo P hp
  have ht := rootCurveTitsWord_cons
    (S := ExtensionField P) (typeDRootPairing_baseEquiv 2 i) []
  rw [rootCurveTitsWord_nil, mul_one] at ht
  have hv := congrArg Units.val ht
  change specializeMatrix (titsLift (typeDRootPairing_baseEquiv 2 i) * 1) = _ at hv
  rw [mul_one] at hv
  have he : (weylWord P i 1).val.val =
      specializeMatrix (titsLift (typeDRootPairing_baseEquiv 2 i)) := by
    change (RootPairing.SimpleGeckGroup.positiveUnit _ 1 *
      RootPairing.SimpleGeckGroup.negativeUnit _ (-(1 : ExtensionField P)⁻¹) *
      RootPairing.SimpleGeckGroup.positiveUnit _ 1).val = _
    rw [inv_one]
    exact hv.symm
  ext a b
  change (weylWord P i 1).val.val (latticeEnumeration a) (latticeEnumeration b) = _
  rw [he, ← binarySpecialization_titsLift]
  change (_ : ExtensionField P) = scalarMap (ExtensionField P) ((_ : ℤ) : ZMod 2)
  rw [map_intCast]
  rfl

/-- Root basis vectors and coroot coordinate vectors in the full Geck lattice. -/
def rootVector (F : Type*) [Zero F] [One F] (r : Fin 24) : Index → F :=
  Pi.single (.inr r) 1

def corootVector (F : Type*) [Ring F] (r : Fin 24) : Index → F
  | .inl j => (simpleCoefficients r j : F)
  | .inr _ => 0

lemma rootVector_injective (F : Type*) [Ring F] [Nontrivial F] :
    Function.Injective (rootVector F) := by
  intro r s h
  by_contra hn
  have he := congrFun h (.inr r)
  simp [rootVector, hn] at he

lemma corootVector_simple (F : Type*) [Ring F] (i : Fin 4) :
    corootVector F (simpleIndex i) = Pi.single (.inl i) 1 := by
  have h (i j : Fin 4) : simpleCoefficients (simpleIndex i) j = if j = i then 1 else 0 := by
    revert i j
    decide +kernel
  ext a
  cases a with
  | inl j => simp [corootVector, h, Pi.single_apply]
  | inr r => simp [corootVector]

private lemma binaryTits_coroot (i : Fin 4) (r : Fin 24) :
    binaryTits i *ᵥ corootVector (ZMod 2) r =
      corootVector (ZMod 2) (reflectionTable i r) := by
  have h (i k : Fin 4) (r : Fin 24) :
      (∑ j : Fin 4, binaryTits i (.inl k) (.inl j) * (simpleCoefficients r j : ZMod 2)) =
        (simpleCoefficients (reflectionTable i r) k : ZMod 2) := by
    revert i k r
    decide +kernel
  ext a
  cases a with
  | inl k => simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, corootVector] using h i k r
  | inr q => simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, corootVector, binaryTits]

private lemma binaryTits_root (i : Fin 4) (r : Fin 24) :
    binaryTits i *ᵥ rootVector (ZMod 2) r =
      rootVector (ZMod 2) (reflectionTable i r) := by
  ext a
  cases a <;> simp [rootVector, Matrix.col_apply,
    binaryTits, Pi.single_apply]

lemma matrix_simple_root (P : Parameters) (hp : P.prime = 2) (i : Fin 4) (r : Fin 24) :
    matrix P (weylWord P i 1) *ᵥ rootVector (ExtensionField P) r =
      rootVector (ExtensionField P) (reflectionTable i r) := by
  let := rankOneExtensionCharTwo P hp
  rw [matrix_simple P hp]
  ext a
  have h := congrArg (scalarMap (ExtensionField P)) (congrFun (binaryTits_root i r) a)
  simpa [RingHom.map_mulVec, rootVector, Pi.single_apply] using h

lemma matrix_simple_coroot (P : Parameters) (hp : P.prime = 2) (i : Fin 4) (r : Fin 24) :
    matrix P (weylWord P i 1) *ᵥ corootVector (ExtensionField P) r =
      corootVector (ExtensionField P) (reflectionTable i r) := by
  let := rankOneExtensionCharTwo P hp
  rw [matrix_simple P hp]
  have hc (r : Fin 24) :
      scalarMap (ExtensionField P) ∘ corootVector (ZMod 2) r =
        corootVector (ExtensionField P) r := by
    ext a
    cases a <;> simp [corootVector]
  ext a
  have h := congrArg (scalarMap (ExtensionField P)) (congrFun (binaryTits_coroot i r) a)
  rw [RingHom.map_mulVec, hc] at h
  exact h.trans (congrFun (hc _) a)

/-- The literal root action in the enumeration used for the full lattice. -/
def rootAction : rootWeylGroup →* Equiv.Perm (Fin 24) :=
  rootEnumeration.symm.permCongrHom.toMonoidHom.comp rootWeylGroup.subtype

lemma rootAction_injective : Function.Injective rootAction :=
  rootEnumeration.symm.permCongrHom.injective.comp Subtype.val_injective

lemma rootAction_simple (i : Fin 4) (r : Fin 24) :
    rootAction (rootWeylGenerator i) r = reflectionTable i r := by
  change rootEnumeration.symm (rootReflection i (rootEnumeration r)) = _
  rw [rootReflection, ← rootEnumeration_reflectionTable, Equiv.symm_apply_apply]

/-- A matrix realizes a root permutation on both spanning families. -/
def Realizes (P : Parameters) (g : SplitGroup P) (w : rootWeylGroup) : Prop :=
  (∀ r, matrix P g *ᵥ rootVector (ExtensionField P) r =
    rootVector (ExtensionField P) (rootAction w r)) ∧
  (∀ r, matrix P g *ᵥ corootVector (ExtensionField P) r =
    corootVector (ExtensionField P) (rootAction w r))

lemma realizes_simple (P : Parameters) (hp : P.prime = 2) (i : Fin 4) :
    Realizes P (weylWord P i 1) (rootWeylGenerator i) := by
  constructor <;> intro r <;> rw [rootAction_simple]
  · exact matrix_simple_root P hp i r
  · exact matrix_simple_coroot P hp i r

lemma realizes_one (P : Parameters) : Realizes P 1 1 := by
  constructor <;> intro r <;> simp only [map_one, Matrix.one_mulVec, Equiv.Perm.one_apply]

lemma realizes_mul {P : Parameters} {g h : SplitGroup P} {w v : rootWeylGroup}
    (hg : Realizes P g w) (hh : Realizes P h v) : Realizes P (g * h) (w * v) := by
  constructor <;> intro r
  · rw [map_mul, ← Matrix.mulVec_mulVec, hh.1, hg.1, map_mul, Equiv.Perm.mul_apply]
  · rw [map_mul, ← Matrix.mulVec_mulVec, hh.2, hg.2, map_mul, Equiv.Perm.mul_apply]

private lemma inverse_action {G F I : Type*} [Group G] [CommRing F]
    [Fintype I] [DecidableEq I] (f : G →* Matrix I I F) (g : G)
    (v u : I → F) (h : f g *ᵥ v = u) : f g⁻¹ *ᵥ u = v := by
  rw [← h, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

lemma realizes_inv {P : Parameters} {g : SplitGroup P} {w : rootWeylGroup}
    (h : Realizes P g w) : Realizes P g⁻¹ w⁻¹ := by
  constructor <;> intro r
  · have he := inverse_action (matrix P) g _ _ (h.1 (rootAction w⁻¹ r))
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using he
  · have he := inverse_action (matrix P) g _ _ (h.2 (rootAction w⁻¹ r))
    simpa only [map_inv, Equiv.Perm.inv_def, Equiv.apply_symm_apply] using he

/-- The root basis distinguishes the realized permutations. -/
lemma Realizes.permutation_unique {P : Parameters} {g : SplitGroup P}
    {w v : rootWeylGroup} (h : Realizes P g w) (k : Realizes P g v) : w = v := by
  apply rootAction_injective
  apply Equiv.ext
  intro r
  exact rootVector_injective (ExtensionField P) ((h.1 r).symm.trans (k.1 r))

/-- Both families together distinguish the entire matrix, including its Cartan block. -/
lemma Realizes.matrix_unique {P : Parameters} {g h : SplitGroup P}
    {w : rootWeylGroup} (hg : Realizes P g w) (hh : Realizes P h w) : g = h := by
  apply matrix_injective P
  ext a b
  cases b with
  | inl j =>
    have he := (hg.2 (simpleIndex j)).trans (hh.2 (simpleIndex j)).symm
    rw [corootVector_simple, Matrix.mulVec_single_one, Matrix.mulVec_single_one] at he
    exact congrFun he a
  | inr r =>
    have he := (hg.1 r).trans (hh.1 r).symm
    simp only [rootVector, Matrix.mulVec_single_one] at he
    exact congrFun he a

/-- Every entry follows from the two spanning-family identities. -/
lemma Realizes.matrix_column {P : Parameters} {g : SplitGroup P} {w : rootWeylGroup}
    (h : Realizes P g w) (a b : Index) :
    matrix P g a b = match b with
      | .inl j => corootVector (ExtensionField P) (rootAction w (simpleIndex j)) a
      | .inr r => if a = .inr (rootAction w r) then 1 else 0 := by
  cases b with
  | inl j =>
    have he := h.2 (simpleIndex j)
    rw [corootVector_simple, Matrix.mulVec_single_one] at he
    exact congrFun he a
  | inr r =>
    have he := h.1 r
    simpa only [rootVector, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
      using congrFun he a

lemma Realizes.root_column {P : Parameters} {g : SplitGroup P} {w : rootWeylGroup}
    (h : Realizes P g w) (a : LatticeIndex) (r : TypeDRootIndex 4) :
    g.val.val a (.inr r) = if a = .inr (w.val r) then 1 else 0 := by
  have he := h.matrix_column (latticeEnumeration.symm a) (.inr (rootEnumeration.symm r))
  change g.val.val (latticeEnumeration (latticeEnumeration.symm a))
    (.inr (rootEnumeration (rootEnumeration.symm r))) =
      if latticeEnumeration.symm a = .inr (rootAction w (rootEnumeration.symm r))
        then 1 else 0 at he
  have hc : latticeEnumeration (.inr (rootAction w (rootEnumeration.symm r))) =
      .inr (w.val r) := by
    change Sum.inr (rootEnumeration (rootEnumeration.symm
      (w.val (rootEnumeration (rootEnumeration.symm r))))) = _
    simp only [Equiv.apply_symm_apply]
  simpa only [Equiv.apply_symm_apply, Equiv.symm_apply_eq, hc] using he

lemma exists_realizes (P : Parameters) (hp : P.prime = 2)
    (g : splitWeylSubgroup P) : ∃ w, Realizes P g.val w := by
  obtain ⟨g, hg⟩ := g
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact ⟨rootWeylGenerator i, realizes_simple P hp i⟩
  | one => exact ⟨1, realizes_one P⟩
  | mul g h hg hh ihg ihh =>
    obtain ⟨w, hw⟩ := ihg
    obtain ⟨v, hv⟩ := ihh
    exact ⟨w * v, realizes_mul hw hv⟩
  | inv g hg ih =>
    obtain ⟨w, hw⟩ := ih
    exact ⟨w⁻¹, realizes_inv hw⟩

end
end Triality.Standard.ConcreteBruhat.MatrixRealization
