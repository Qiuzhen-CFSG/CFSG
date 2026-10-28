module
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.Incidence
public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocal.Octagon.WeylGroup
public import Theory.AlgebraicGroup.BNPair.DihedralGeometry.OctagonRootPath
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockGeometry.ParabolicRecognition
public import Theory.SpecificGroups.ReeF4.LargeLocalSeeds.FixedGeometry.FixedBruhat
public import Theory.GroupAction.RankTwoCosetGeometry.Valence

/-!
# Local geometry of the general Ree completion

The concrete octagonal BN-pair gives nine-path transitivity with the original
linear/Suzuki marking. The two root-Borel indices are transported through the
matrix-preserving fixed-group equivalence, giving valences q+1 and q²+1.
These are native model facts for every positive parameter, including q=8.
They do not recognize an arbitrary completion.

Source: Aschbacher–Smith F.4.5–6, printed pp.275–277, and GLS3 §§2.3,2.6.
-/

public noncomputable section
namespace ReeF4.SourceCompletion
open Subgroup LargeLocalSeeds Parabolics SectionGeometry.BNPair
open MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry
open Theory.AlgebraicGroup.TitsSystem
attribute [local instance] borel_inf_normalizerWords_normal

/-- The surviving source orientation: linear first, Suzuki second. -/
@[expose] def family (m : ℕ) : Bool → Subgroup (Model m) :=
  fun b => if b then Parabolics.parabolic m .suzuki else Parabolics.parabolic m .linear

/-- The marked native Weyl quotient and full parabolics give the octagonal datum. -/
theorem exists_datum (m : ℕ) (hm : 0 < m) :
    Nonempty (DihedralGeometry.OctagonalDatum (titsSystem m) (family m)) := by
  obtain ⟨e, he₀, he₁⟩ := hasOctagonalWeylGroup m hm
  let side : Bool → Side := fun b => if b then .suzuki else .linear
  refine ⟨{
    typeEquiv := Equiv.refl Bool
    simple := fun b => simpleReflection m (side b)
    simple_range := ?_
    weylEquiv := e
    map_simple := ?_
    parabolic_eq := ?_ }⟩
  · change Set.range (fun b => simpleReflection m (side b)) = Set.range (simpleReflection m)
    ext w
    constructor
    · rintro ⟨b, rfl⟩; exact ⟨side b, rfl⟩
    · rintro ⟨s, rfl⟩
      cases s with
      | linear => exact ⟨false, rfl⟩
      | suzuki => exact ⟨true, rfl⟩
  · intro b
    cases b with
    | false => exact he₀
    | true => exact he₁
  · intro b
    have hh := standardParabolic_singleton_eq_parabolic m hm (side b)
    rw [parabolic_eq_rootParabolic] at hh
    cases b <;> exact hh.symm

/-- Every native vertex stabilizer is transitive on nonbacktracking nine-paths. -/
theorem nine_transitive (m : ℕ) (hm : 0 < m) (v : CosetGeometry.Vertex (family m)) :
    SimpleGraph.PathTransitivePolygon.RootPathTransitive
      (CosetGeometry.RankTwo.graph (family m)) (Model m) v 9 := by
  obtain ⟨D⟩ := exists_datum m hm
  exact D.rootPathTransitive_nine v

open LocalBlockInput.PairRigidity

/-- The whole Borel has index q+1 or q²+1 in its indicated full parabolic. -/
theorem borel_relIndex (m : ℕ) (hm : 0 < m) (s : Side) :
    (borel m).relIndex (Parabolics.parabolic m s) =
      (if s = .linear then 2^(2*m+1) else (2^(2*m+1))^2) + 1 := by
  let d := canonicalLocalBlockInput m
  have hP : (rootBorel d ⊔ simpleBlock d s false).map d.modelEquiv.toMonoidHom =
      Parabolics.parabolic m s := by
    rw [rootBorel_sup_negativeBlock_eq_sup_relativeWeyl, Subgroup.map_sup,
      rootBorel_map_modelEquiv, MonoidHom.map_zpowers, MulEquiv.coe_toMonoidHom,
      modelEquiv_relativeWeyl]
    cases s with
    | linear => exact (linear_parabolic_eq_borel_sup_weyl m hm).symm
    | suzuki => exact (suzuki_parabolic_eq_borel_sup_weyl m).symm
  rw [←hP, ←rootBorel_map_modelEquiv d, relIndex_map_map_of_injective _ _ d.modelEquiv.injective]
  have hi := FixedBruhat.standardUnipotent_index_odd d
  cases s with
  | linear => exact LocalIndices.linear_relIndex d hi (splitTorus_eq_diagonalTorus m)
  | suzuki => exact LocalIndices.suzuki_relIndex hm d hi (splitTorus_eq_diagonalTorus m)

/-- Local valences in the reversed source orientation. -/
theorem card_neighbors (m : ℕ) (hm : 0 < m)
    (v : CosetGeometry.Vertex (family m)) :
    Nat.card ((CosetGeometry.RankTwo.graph (family m)).neighborSet v) =
      (if v.type then (2^(2*m+1))^2 else 2^(2*m+1)) + 1 := by
  have hbase (i : Bool) :
      Nat.card ((CosetGeometry.RankTwo.graph (family m)).neighborSet
        (CosetGeometry.base (family m) i)) =
      (if i then (2^(2*m+1))^2 else 2^(2*m+1)) + 1 := by
    rw [CosetGeometry.RankTwo.card_neighbor_base]
    have ho : Parabolics.parabolic m .linear ⊓ Parabolics.parabolic m .suzuki = borel m := by
      simpa only [parabolic_eq_rootParabolic] using
        (parabolic_inf_eq_borel m hm)
    cases i
    · change (Parabolics.parabolic m .suzuki).relIndex (Parabolics.parabolic m .linear) = _
      rw [← Subgroup.inf_relIndex_left, ho]
      exact borel_relIndex m hm .linear
    · change (Parabolics.parabolic m .linear).relIndex (Parabolics.parabolic m .suzuki) = _
      rw [← Subgroup.inf_relIndex_left, inf_comm, ho]
      exact borel_relIndex m hm .suzuki
  obtain ⟨g, hg⟩ := CosetGeometry.exists_smul_base (family m) v
  have hh := Nat.card_congr
    ((CosetGeometry.translationGraphIso (family m) g).mapNeighborSet
      (CosetGeometry.base (family m) v.type))
  change Nat.card ((CosetGeometry.RankTwo.graph (family m)).neighborSet
    (CosetGeometry.base (family m) v.type)) =
    Nat.card ((CosetGeometry.RankTwo.graph (family m)).neighborSet
      (g • CosetGeometry.base (family m) v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans (hbase v.type)

end ReeF4.SourceCompletion
