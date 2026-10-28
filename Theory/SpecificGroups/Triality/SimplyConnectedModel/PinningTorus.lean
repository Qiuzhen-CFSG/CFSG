module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Carrier
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RootPoints
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootPoints
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.CorootTorus
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.PointGeneration
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.WeightReflection

/-!
# The concrete Spin D4 pinning and integral coroot torus

The closed maximal torus `CorootTorus.closedSubgroup k` has the actual algebraic
coordinate isomorphism `CorootTorus.coordinateIso k`: inclusion is the ordered
product of the four source simple coroots, and the inverse uses a regular
Clifford coefficient. Its fundamental characters and integral weight embedding
are dual to these coroot coordinates.

`pinnedRootData` discharges the geometric premises of the regular-root
construction with this torus and isomorphism. It exhausts the actual roots,
with the standard D4 base, central vertex 1 and arms 0, 2, 3. Its regular root
parametrizations have the original even-orthogonal matrices under the faithful
natural action; the positive and negative simple groups generate all points.
The root characters and cocharacters agree with the same integral coordinates
and source coroot words.

The same pinned normalizers induce the regular torus automorphisms
`CorootTorus.torusReflection`. Their conjugation and character identities,
`torusReflection_conjugation` and `weightEmbedding_reflection`, provide the
exact inputs to `RestrictedWeights`. The conventions remain
`nα(t) = xα(t) x−α(−t⁻¹) xα(t)` and `hα(t) = nα(1)⁻¹ nα(t)`;
the torus maps are inverse conjugation.

Source: GLS3, §§1.9–1.14, especially 1.12.1, 1.12.5(b), and 1.14.1–2
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

@[expose] public section
noncomputable section
namespace Triality.SimplyConnected.Pinning
open Theory Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- The constructed regular torus isomorphism has exactly the source coroot product. -/
theorem hasCorootCoordinates :
    HasCorootCoordinates k (CorootTorus.closedSubgroup k) (CorootTorus.coordinateIso k) :=
  CorootTorus.coordinateIso_inclusion k

/-- The actual D4 root geometry of the concrete closed maximal Spin torus. -/
abbrev pinnedRootData : RootGroupData (groupVariety k) (CorootTorus.closedSubgroup k) :=
  rootData k (CorootTorus.closedSubgroup k) (CorootTorus.coordinateIso k)

/-- The concrete D4 index regarded as an index of the realized root datum. -/
def pinnedRootIndex (r : RootIndex) : (pinnedRootData k).Root := ULift.up r

/-- Exhaustive root realization, with all geometric torus premises discharged. -/
theorem pinnedRootData_isRealization : (pinnedRootData k).IsRealization :=
  rootData_isRealization k _ (CorootTorus.isMaximal k) _ (hasCorootCoordinates k)

/-- The actual root pairing and base are the standard numbered D4 pairing and base. -/
theorem pinnedRootData_isActualBasedRootPairing :
    IsActualBasedRootPairing (pinnedRootData k) (typeDRootPairing 2)
      (typeDRootPairing_base 2) Equiv.ulift :=
  rootData_isActualBasedRootPairing k _ _

/-- The positive system and heights agree with the same standard D4 base. -/
theorem pinnedRootData_isRootSystemRealization :
    IsRootSystemRealization (pinnedRootData k) (typeDRootPairing 2)
      Equiv.ulift (typeDRootPairing_base 2) :=
  rootData_isRootSystemRealization k _ _

/-- Partial addition is precisely addition of the standard D4 root vectors. -/
theorem pinnedRootData_isRootAdditionRealization :
    IsRootAdditionRealization (pinnedRootData k) (typeDRootPairing 2) Equiv.ulift :=
  rootData_isRootAdditionRealization k _ _

/-- Every sum of actual root characters that is a root occurs in the root datum. -/
theorem pinnedRootData_isRootAdditionComplete :
    (pinnedRootData k).IsRootAdditionComplete :=
  rootData_isRootAdditionComplete k _ _

/-- The chosen positive roots form an actual positive system. -/
theorem pinnedRootData_positive_isPositiveSystem :
    IsPositiveSystem (pinnedRootData k) (pinnedRootData k).positive :=
  rootData_positive_isPositiveSystem k _ (CorootTorus.isMaximal k) _ (hasCorootCoordinates k)

/-- The four pinned simple roots are exactly the simple roots of this realization. -/
theorem pinnedRootData_simple :
    (pinnedRootData k).simple = Set.range (fun i => pinnedRootIndex k (simpleRoot i)) :=
  rootData_simple_eq_range k _ _

/-- The simple pairings have central vertex 1 and arms 0, 2, and 3. -/
theorem pinnedRootData_pairing_simple (i j : Fin 4) :
    (pinnedRootData k).pairing (pinnedRootIndex k (simpleRoot i)) (pinnedRootIndex k (simpleRoot j)) =
      typeDCartanMatrix 2 i j :=
  rootData_pairing_simple k _ _ i j

/-- Negation agrees with the signed root-point convention. -/
theorem pinnedRootData_neg (r : RootIndex) :
    (pinnedRootData k).neg (pinnedRootIndex k r) = pinnedRootIndex k (negativeRoot r) :=
  rootData_neg k _ _ r

/-- The algebraic group structure inherited by each realized closed root subgroup. -/
instance pinnedRootSubgroupAlgebraicGroup (r : (pinnedRootData k).Root) :
    AlgebraicGroup ((pinnedRootData k).rootSubgroup r).carrierVariety :=
  ((pinnedRootData k).rootSubgroup r).carrierAlgebraicGroup

/-- The normalized regular additive parametrization of each realized root subgroup. -/
def pinnedRootParametrization (r : (pinnedRootData k).Root) :
    OneParameterParametrization ((pinnedRootData k).rootSubgroup r).carrierVariety :=
  rootParametrization k r.down

/-- The geometric parametrization includes as the original anchored root point. -/
theorem pinnedRootParametrization_inclusion (r : (pinnedRootData k).Root) (a : k) :
    ((pinnedRootData k).rootSubgroup r).includePoint
      ((pinnedRootParametrization k r).value a) = rootPoint k r.down a :=
  rootParametrization_inclusion k r.down a

/-- Each geometric root curve has the prescribed even-orthogonal root matrix. -/
theorem pinnedRootParametrization_naturalAction (r : (pinnedRootData k).Root) (a : k) :
    naturalAction k (((pinnedRootData k).rootSubgroup r).includePoint
      ((pinnedRootParametrization k r).value a)) =
        evenOrthogonalRootQuadraticPoint 4 r.down a := by
  rw [pinnedRootParametrization_inclusion, naturalAction_rootPoint]

/-- The positive simple parametrizations preserve the original pinning. -/
theorem pinnedRootParametrization_positiveSimple (i : Fin 4) (a : k) :
    ((pinnedRootData k).rootSubgroup (pinnedRootIndex k (simpleRoot i))).includePoint
      ((pinnedRootParametrization k (pinnedRootIndex k (simpleRoot i))).value a) =
        positiveSimplePoint k i a :=
  pinnedRootParametrization_inclusion k _ a

/-- The negative simple parametrizations preserve the original pinning. -/
theorem pinnedRootParametrization_negativeSimple (i : Fin 4) (a : k) :
    ((pinnedRootData k).rootSubgroup (pinnedRootIndex k (negativeSimpleRoot i))).includePoint
      ((pinnedRootParametrization k (pinnedRootIndex k (negativeSimpleRoot i))).value a) =
        negativeSimplePoint k i a :=
  pinnedRootParametrization_inclusion k _ a

/-- The actual root characters are the integral characters in Spin coroot coordinates. -/
theorem pinnedRootData_rootWeight (r : (pinnedRootData k).Root) :
    (pinnedRootData k).rootWeight r =
      CorootTorus.weightEmbedding k (rootCorootExponent r.down) := by
  apply TorusCharacter.pointCharacter_injective
  ext t
  obtain ⟨x, rfl⟩ := (CorootTorus.coordinateIso k).toMulEquiv.surjective t
  change (coordinateRootWeight k _ (CorootTorus.coordinateIso k) r.down).pointCharacter
      ((CorootTorus.coordinateIso k).hom.onPoints x) =
    (CorootTorus.weightEmbedding k (rootCorootExponent r.down)).pointCharacter
      ((CorootTorus.coordinateIso k).hom.onPoints x)
  rw [coordinateRootWeight_apply, CorootTorus.coordinateIso_hom_apply,
    CorootTorus.weightEmbedding_parameter]

/-- The four simple roots have the rows of the D4 Cartan matrix as weight coordinates. -/
theorem pinnedRootData_rootWeight_simple (i : Fin 4) :
    (pinnedRootData k).rootWeight (pinnedRootIndex k (simpleRoot i)) =
      CorootTorus.weightEmbedding k (typeDCartanMatrix 2 i) := by
  rw [pinnedRootData_rootWeight]
  congr 1
  funext j
  exact rootCorootExponent_simple i j

/-- Every actual root cocharacter is the source word hα(t) = nα(1)⁻¹ nα(t). -/
theorem pinnedRootData_rootCocharacter (r : (pinnedRootData k).Root)
    (t : Variety.Point (KMult k)) :
    (CorootTorus.closedSubgroup k).includePoint
      (((pinnedRootData k).rootCocharacter r).onPoints t) =
        corootWord k r.down (dPointEquiv 1 t 0) :=
  coordinateRootCocharacter_inclusion k _ _ (hasCorootCoordinates k) r.down t

/-- The integral weight coordinates are their exponents on the actual simple coroots. -/
theorem pinnedRootData_weight_simpleCoroot (a : Fin 4 → ℤ) (i : Fin 4)
    (t : Variety.Point (KMult k)) :
    (CorootTorus.weightEmbedding k a).pointCharacter
      (((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints t) =
        (dPointEquiv 1 t 0 : k) ^ a i := by
  have h : ((pinnedRootData k).rootCocharacter (pinnedRootIndex k (simpleRoot i))).onPoints t =
      CorootTorus.parameterPoint k (Function.update (fun _ => 1) i (dPointEquiv 1 t 0)) := by
    apply (CorootTorus.closedSubgroup k).inclusion_injective
    exact (pinnedRootData_rootCocharacter k _ t).trans
      (CorootTorus.inclusion_single_parameter k i (dPointEquiv 1 t 0)).symm
  rw [h, CorootTorus.weightEmbedding_parameter]
  classical
  rw [Fintype.prod_eq_single i]
  · simp
  · intro j hj
    simp [Function.update_of_ne hj]

/-- The positive and negative simple algebraic root groups generate all Spin points. -/
theorem pinnedRootParametrization_generate :
    Subgroup.closure
      (Set.range (fun p : Fin 4 × k =>
        ((pinnedRootData k).rootSubgroup (pinnedRootIndex k (simpleRoot p.1))).includePoint
          ((pinnedRootParametrization k (pinnedRootIndex k (simpleRoot p.1))).value p.2)) ∪
       Set.range (fun p : Fin 4 × k =>
        ((pinnedRootData k).rootSubgroup (pinnedRootIndex k (negativeSimpleRoot p.1))).includePoint
          ((pinnedRootParametrization k (pinnedRootIndex k (negativeSimpleRoot p.1))).value p.2))) = ⊤ := by
  simpa only [simplePointSubgroup, pinnedRootParametrization_positiveSimple,
    pinnedRootParametrization_negativeSimple] using simplePointSubgroup_eq_top k

end Triality.SimplyConnected.Pinning
