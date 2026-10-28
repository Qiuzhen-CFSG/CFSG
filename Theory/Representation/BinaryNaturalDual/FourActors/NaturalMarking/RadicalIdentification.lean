module

public import Theory.Representation.BinaryNaturalDual.FourActors.Model
public import Theory.Representation.BinaryNaturalDual.FourActors.Radical
public import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The two-block actor is the radical of a coordinate two-space

The four specified generators of A₀ correspond to four block-unipotent
matrices in the original natural space. The correspondence is checked through
`psl4TwoEquivAlt8_orthogonal`: exterior-square and deleted-permutation actions
agree modulo the constant word. Thus this identifies the published A₀ using
the actual exceptional equivalence, without choosing another comparison.

All four matrices fix the plane x₂ = x₃ = 0 pointwise and have displacement in
it. A radical element is determined by the displacements of the two remaining
basis vectors, so this radical has at most 4² elements. The explicit premise
`Nat.card A0 = 16`, supplied by the permutation catalogue, gives equality.
No elementary-abelian premise or radical-identification premise is assumed.

The coordinate comparison uses the attributed ATLAS port in
`Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8`, adapted from Gerald
Höhn and ATLAS contributors, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), H.9.3(4),
printed p.391, PDF p.402.
-/

@[expose] public section

open Equiv Subgroup
open BinaryLinear BinaryLinear.OuterCyclic
open Atlas.Order20160A8
open scoped MatrixGroups
namespace BinaryNaturalDual.FourActors

private def blockMatrix (q : Fin 4 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1,0,q 0,q 1; 0,1,q 2,q 3; 0,0,1,0; 0,0,0,1]

private def blockSL (q : Fin 4 → ZMod 2) : SL(4,ZMod 2) :=
  ⟨blockMatrix q, by
    rw [Matrix.det_of_isUpperTriangular]
    · simp [blockMatrix, Fin.prod_univ_succ]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [blockMatrix]⟩

private def generatorParameters : Fin 4 → (Fin 4 → ZMod 2) :=
  ![![0,1,1,0], ![1,0,1,1], ![1,0,0,1], ![1,1,1,0]]

private def generatorPermutation : Fin 4 → S :=
  ![swap 0 1 * swap 2 3, swap 0 2 * swap 1 3,
    swap 4 5 * swap 6 7, swap 4 6 * swap 5 7]

private theorem comparison_sl (g : SL(4,ZMod 2)) :
    linearAlternatingEquiv (slEquivLinear 4 g) =
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8 (sl4TwoEquivPSL g) := by
  have h : (projectiveEquivLinear (by decide : 0 < 4)).symm (slEquivLinear 4 g) =
      sl4TwoEquivPSL g := by
    apply (projectiveEquivLinear (by decide : 0 < 4)).injective
    rw [MulEquiv.apply_symm_apply]
    exact (projectiveEquivLinear_mk (by decide) g).symm
  change Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8
    ((projectiveEquivLinear (by decide : 0 < 4)).symm (slEquivLinear 4 g)) = _
  rw [h]

private theorem comparison_of_raw (g : SL(4,ZMod 2)) (p : S)
    (h : ∀ v : DeletedEight.D,
      DeletedEight.raw (Exterior.onD g v) - (fun i => DeletedEight.raw v (p.symm i)) =
        (fun _ => DeletedEight.raw v (p.symm 7))) :
    (linearAlternatingEquiv (slEquivLinear 4 g)).val = p := by
  apply DeletedEight.orthogonalHom_injective
  rw [comparison_sl, Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8_orthogonal]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  apply DeletedEight.splitEquiv.injective
  change DeletedEight.splitEquiv (Exterior.onD g v) =
    DeletedEight.splitEquiv (DeletedEight.splitEquiv.symm
      (DeletedEight.quotientPerm p (DeletedEight.splitEquiv v)))
  rw [LinearEquiv.apply_symm_apply]
  change Submodule.Quotient.mk (DeletedEight.intoEven (Exterior.onD g v)) =
    Submodule.Quotient.mk (DeletedEight.evenPerm p (DeletedEight.intoEven v))
  apply (Submodule.Quotient.eq _).mpr
  apply Submodule.mem_span_singleton.mpr
  refine ⟨DeletedEight.raw v (p.symm 7), ?_⟩
  apply Subtype.ext
  funext j
  change DeletedEight.raw v (p.symm 7) * 1 =
    DeletedEight.raw (Exterior.onD g v) j - DeletedEight.raw v (p.symm j)
  simpa only [mul_one, Pi.sub_apply] using congrFun (h v).symm j

private theorem generators_comparison (i : Fin 4) :
    (linearAlternatingEquiv (slEquivLinear 4 (blockSL (generatorParameters i)))).val =
      generatorPermutation i := by
  apply comparison_of_raw
  exact (by decide +kernel : ∀ (i : Fin 4) (v : DeletedEight.D),
    DeletedEight.raw (Exterior.onD (blockSL (generatorParameters i)) v) -
      (fun j => DeletedEight.raw v ((generatorPermutation i).symm j)) =
        (fun _ => DeletedEight.raw v ((generatorPermutation i).symm 7))) i

/-- The actual coordinate plane determined by the two four-point blocks. -/
def A0Plane : Submodule (ZMod 2) X where
  carrier := {v | v 2 = 0 ∧ v 3 = 0}
  zero_mem' := by simp
  add_mem' := by rintro v w ⟨hv2,hv3⟩ ⟨hw2,hw3⟩; simp_all
  smul_mem' := by rintro a v ⟨hv2,hv3⟩; simp_all

private def planeEquiv : (Fin 2 → ZMod 2) ≃ₗ[ZMod 2] A0Plane where
  toFun v := ⟨![v 0,v 1,0,0], by constructor <;> rfl⟩
  invFun v := ![v.val 0,v.val 1]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · rfl
    · exact v.property.1.symm
    · exact v.property.2.symm
  map_add' v w := by apply Subtype.ext; ext i; fin_cases i <;> rfl
  map_smul' a v := by apply Subtype.ext; ext i; fin_cases i <;> simp

theorem A0Plane_finrank : Module.finrank (ZMod 2) A0Plane = 2 := by
  rw [← planeEquiv.finrank_eq]
  simp

private theorem block_mem_radical (q : Fin 4 → ZMod 2) :
    slEquivLinear 4 (blockSL q) ∈ radical A0Plane := by
  constructor
  · intro v hv
    change (blockMatrix q).mulVec v = v
    ext i
    fin_cases i <;>
      simp [blockMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hv.1, hv.2]
  · intro v
    change (blockMatrix q).mulVec v 2 - v 2 = 0 ∧
      (blockMatrix q).mulVec v 3 - v 3 = 0
    constructor <;>
      simp [blockMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem A0_le_radicalImage : A0 ≤ radicalImage A0Plane := by
  have hgen (i : Fin 4) : generatorPermutation i ∈
      (radicalImage A0Plane).map permutationEquiv.toMonoidHom := by
    refine ⟨MulAut.conj (slEquivLinear 4 (blockSL (generatorParameters i))),
      Subgroup.mem_map_of_mem _ (block_mem_radical _), ?_⟩
    exact (permutationEquiv_inner _).trans (generators_comparison i)
  have hle : permutationA0 ≤ (radicalImage A0Plane).map permutationEquiv.toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro p hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl | rfl
    · exact hgen 0
    · exact hgen 1
    · exact hgen 2
    · exact hgen 3
  intro a ha
  obtain ⟨b, hb, he⟩ := hle ha
  exact permutationEquiv.injective he ▸ hb

private theorem card_radical_plane_le : Nat.card (radical A0Plane) ≤ 16 := by
  let f : radical A0Plane → (Fin 2 → A0Plane) := fun g i =>
    ⟨g.val (Pi.single (if i = 0 then 2 else 3) 1) -
      Pi.single (if i = 0 then 2 else 3) 1, g.property.2 _⟩
  have hf : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply LinearEquiv.toLinearMap_injective
    apply (Pi.basisFun (ZMod 2) (Fin 4)).ext
    intro i
    simp only [Pi.basisFun_apply]
    change g.val (Pi.single i 1) = h.val (Pi.single i 1)
    fin_cases i
    · rw [g.property.1 _ (by constructor <;> decide),
        h.property.1 _ (by constructor <;> decide)]
    · rw [g.property.1 _ (by constructor <;> decide),
        h.property.1 _ (by constructor <;> decide)]
    · have hh := congrArg (fun k : Fin 2 → A0Plane => (k 0).val) he
      change g.val (Pi.single 2 1) - Pi.single 2 1 =
        h.val (Pi.single 2 1) - Pi.single 2 1 at hh
      exact sub_left_inj.mp hh
    · have hh := congrArg (fun k : Fin 2 → A0Plane => (k 1).val) he
      change g.val (Pi.single 3 1) - Pi.single 3 1 =
        h.val (Pi.single 3 1) - Pi.single 3 1 at hh
      exact sub_left_inj.mp hh
  have hc : Nat.card A0Plane = 4 := by
    rw [← Nat.card_congr planeEquiv.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hb := Nat.card_le_card_of_injective f hf
  norm_num only [Nat.card_fun, Nat.card_fin, hc] at hb
  exact hb

theorem A0_eq_radicalImage (hcard : Nat.card A0 = 16) : A0 = radicalImage A0Plane := by
  let : Finite G := Finite.of_injective (fun g : G => (g : X → X)) DFunLike.coe_injective
  apply Subgroup.eq_of_le_of_card_ge A0_le_radicalImage
  rw [hcard]
  have hc : Nat.card (radicalImage A0Plane) = Nat.card (radical A0Plane) := by
    exact (Nat.card_congr ((radical A0Plane).equivMapOfInjective _
      (MulAut.conj_injective_of_center_eq_bot center_linear_eq_bot)).toEquiv).symm
  rw [hc]
  exact card_radical_plane_le

/-- The published two-block actor is an actual two-space radical. The order premise
is the remaining permutation-catalogue input to H.9.3(4). -/
theorem exists_A0_radical (hcard : Nat.card A0 = 16) :
    ∃ U : Submodule (ZMod 2) X, Module.finrank (ZMod 2) U = 2 ∧ A0 = radicalImage U :=
  ⟨A0Plane, A0Plane_finrank, A0_eq_radicalImage hcard⟩

end BinaryNaturalDual.FourActors
