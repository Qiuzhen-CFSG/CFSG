module

public import CFSG.Quasithin.ChapterI.Section04To05.Geometry
public import Theory.Representation.PSL3Two.FanoLineSpan
public import Theory.LinearAlgebra.BinaryPointMap
public import Mathlib.RepresentationTheory.Subrepresentation
public import Theory.Representation.SubspaceQuotient
/-!
# The four-dimensional module in A₃ recognition

We form the binary permutation module on the actual point cosets and quotient
by the span of actual three-point line vectors. A Fano identification in each
of the seven planes through the base point shows that each plane contributes
at most one dimension modulo the seven-generator base-point pencil. Thus the
line span has dimension at most fourteen and the quotient is nonzero.

The binary point-map lemmas then identify the fifteen points with precisely
the nonzero quotient vectors, prove dimension four and faithfulness, and
identify the point stabilizer literally with the original vertex group.

The explicit GeometryData fields are earlier I.5.8–9 incidence facts, still
to be constructed from DSystem by the geometry owner. No nonzero quotient,
dimension, linear faithfulness or recognition conclusion is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, I.5.10,
printed p.422, using the local Fano calculation of H.5.3.
-/

@[expose] public section

open Module
attribute [local instance] Classical.propDecidable
namespace Quasithin.I5.A3Recognition
open DSystem
variable {G : Type*} [Group G] (S : DSystem .A3 G)
abbrev U := S.Point → ZMod 2
noncomputable def pointVector (x : S.Point) : U S := Pi.single x 1
noncomputable def lineVector (l : S.Line) : U S := fun x => if S.Inc x l then 1 else 0
noncomputable def K : Submodule (ZMod 2) (U S) :=
  Submodule.span _ (Set.range (lineVector S))
noncomputable def pointSpan (x : S.Point) : Submodule (ZMod 2) (U S) :=
  Submodule.span _ (Set.range fun l : {l : S.Line // S.Inc x l} => lineVector S l.val)
theorem pointSpan_le_K (x : S.Point) : pointSpan S x ≤ K S := by
  apply Submodule.span_le.mpr
  rintro v ⟨l, rfl⟩
  exact Submodule.subset_span ⟨l.val, rfl⟩

/-- The literal point and line incidence of a plane residue. -/
structure FanoPlane (π : S.Plane) where
  points : Matrix.PSL3Two.Fano.Point ≃ {x : S.Point // S.Inc x π}
  lines : Matrix.PSL3Two.Fano.Line ≃ {l : S.Line // S.Inc l π}
  incident : ∀ p l, S.Inc (points p).val (lines l).val ↔ Matrix.PSL3Two.Fano.Incident p l

/-- Earlier I.5.8–9 geometry used in the module construction. -/
structure GeometryData where
  card_points : Nat.card S.Point = 15
  faithful_points : FaithfulSMul G S.Point
  card_lines : Nat.card {l : S.Line // S.Inc S.basePoint l} = 7
  card_planes : Nat.card {π : S.Plane // S.Inc S.basePoint π} = 7
  line_points : ∀ x y : S.Point, x ≠ y → ∃ l : S.Line, ∃ z : S.Point,
    z ≠ x ∧ z ≠ y ∧ ∀ p : S.Point, S.Inc p l ↔ p = x ∨ p = y ∨ p = z
  point_line_plane : ∀ (x : S.Point) (l : S.Line) (π : S.Plane),
    S.Inc x l → S.Inc l π → S.Inc x π
  planes : ∀ π : {π : S.Plane // S.Inc S.basePoint π}, FanoPlane S π.val
  cover : ∀ l : S.Line, ∃ π : {π : S.Plane // S.Inc S.basePoint π}, S.Inc l π.val

variable {S}
theorem GeometryData.finite_points (d : GeometryData S) : Finite S.Point :=
  Nat.finite_of_card_ne_zero (by rw [d.card_points]; decide)
noncomputable def planeLift {π : S.Plane} (e : FanoPlane S π) :
    BinaryLinearThree.FanoLineSpan.Full →ₗ[ZMod 2] U S where
  toFun v x := if hx : S.Inc x π then v (e.points.symm ⟨x, hx⟩) else 0
  map_add' a b := by ext x; dsimp; split_ifs <;> simp
  map_smul' c a := by ext x; dsimp; split_ifs <;> simp
theorem planeLift_line (d : GeometryData S) {π : S.Plane} (e : FanoPlane S π)
    (l : Matrix.PSL3Two.Fano.Line) :
    planeLift e (BinaryLinearThree.FanoLineSpan.lineVector l) =
      lineVector S (e.lines l).val := by
  classical
  ext x
  by_cases hx : S.Inc x π
  · have hi := e.incident (e.points.symm ⟨x, hx⟩) l
    simp only [Equiv.apply_symm_apply] at hi
    simp [planeLift, BinaryLinearThree.FanoLineSpan.lineVector, lineVector, hx, hi]
  · have hn : ¬ S.Inc x (e.lines l).val :=
      fun h => hx (d.point_line_plane _ _ _ h (e.lines l).property)
    simp [planeLift, lineVector, hx, hn]

noncomputable def planeImage (d : GeometryData S)
    (π : {π : S.Plane // S.Inc S.basePoint π}) :
    Submodule (ZMod 2) (U S ⧸ pointSpan S S.basePoint) :=
  BinaryLinearThree.FanoLineSpan.lineSpan.map
    ((pointSpan S S.basePoint).mkQ.comp (planeLift (d.planes π)))

theorem finrank_planeImage (d : GeometryData S)
    (π : {π : S.Plane // S.Inc S.basePoint π}) :
    finrank (ZMod 2) (planeImage d π) ≤ 1 := by
  apply BinaryLinearThree.FanoLineSpan.finrank_map_le_one
    ((d.planes π).points.symm ⟨S.basePoint, π.property⟩)
  intro l hl
  change (pointSpan S S.basePoint).mkQ (planeLift _ _) = 0
  rw [planeLift_line d]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply Submodule.subset_span
  refine ⟨⟨((d.planes π).lines l).val, ?_⟩, rfl⟩
  have hi := ((d.planes π).incident
    ((d.planes π).points.symm ⟨S.basePoint, π.property⟩) l).mpr hl
  simpa only [Equiv.apply_symm_apply] using hi

theorem map_K_le_planes (d : GeometryData S) :
    (K S).map (pointSpan S S.basePoint).mkQ ≤ ⨆ π, planeImage d π := by
  rw [K, Submodule.map_span]
  apply Submodule.span_le.mpr
  rintro _ ⟨v, ⟨l, rfl⟩, rfl⟩
  obtain ⟨π, hl⟩ := d.cover l
  apply (le_iSup (planeImage d) π)
  let r := (d.planes π).lines.symm ⟨l, hl⟩
  refine ⟨BinaryLinearThree.FanoLineSpan.lineVector r,
    Submodule.subset_span ⟨r, rfl⟩, ?_⟩
  change (pointSpan S S.basePoint).mkQ (planeLift _ _) = _
  rw [planeLift_line d]
  simp [r]

private theorem finrank_iSup_le_sum {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] {ι : Type*} [Fintype ι]
    (A : ι → Submodule (ZMod 2) V) :
    finrank (ZMod 2) (⨆ i, A i : Submodule (ZMod 2) V) ≤ ∑ i, finrank (ZMod 2) (A i) := by
  classical
  have aux (s : Finset ι) :
      finrank (ZMod 2) (⨆ i ∈ s, A i : Submodule (ZMod 2) V) ≤ ∑ i ∈ s, finrank (ZMod 2) (A i) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      rw [Finset.iSup_insert]
      have hd := (A i).finrank_sup_add_finrank_inf_eq (⨆ j ∈ s, A j)
      omega
  have he : (⨆ i ∈ (Finset.univ : Finset ι), A i) = ⨆ i, A i := by
    apply le_antisymm
    · exact iSup_le fun i => iSup_le fun _ => le_iSup A i
    · exact iSup_le fun i => le_iSup_of_le i (le_iSup_of_le (Finset.mem_univ i) le_rfl)
  have h := aux Finset.univ
  rw [he] at h
  exact h

theorem finrank_pointSpan (d : GeometryData S) :
    finrank (ZMod 2) (pointSpan S S.basePoint) ≤ 7 := by
  let : Finite {l : S.Line // S.Inc S.basePoint l} :=
    Nat.finite_of_card_ne_zero (by rw [d.card_lines]; decide)
  let := Fintype.ofFinite {l : S.Line // S.Inc S.basePoint l}
  exact (finrank_range_le_card _).trans (by rw [← Nat.card_eq_fintype_card, d.card_lines])

theorem finrank_map_K (d : GeometryData S) :
    finrank (ZMod 2) ((K S).map (pointSpan S S.basePoint).mkQ) ≤ 7 := by
  let : Finite S.Point := d.finite_points
  let : Finite {π : S.Plane // S.Inc S.basePoint π} :=
    Nat.finite_of_card_ne_zero (by rw [d.card_planes]; decide)
  let := Fintype.ofFinite {π : S.Plane // S.Inc S.basePoint π}
  calc
    _ ≤ finrank (ZMod 2) (⨆ π, planeImage d π : Submodule (ZMod 2) (U S ⧸ pointSpan S S.basePoint)) := Submodule.finrank_mono (map_K_le_planes d)
    _ ≤ ∑ π, finrank (ZMod 2) (planeImage d π) := finrank_iSup_le_sum _
    _ ≤ ∑ _π : {π : S.Plane // S.Inc S.basePoint π}, 1 :=
      Finset.sum_le_sum (fun π _ => finrank_planeImage d π)
    _ = 7 := by simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one];
                rw [← Nat.card_eq_fintype_card, d.card_planes]

theorem finrank_K (d : GeometryData S) : finrank (ZMod 2) (K S) ≤ 14 := by
  let : Finite S.Point := d.finite_points
  have hr := ((pointSpan S S.basePoint).mkQ.domRestrict (K S)).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict] at hr
  have hk : ((pointSpan S S.basePoint).mkQ.domRestrict (K S)).ker =
      (pointSpan S S.basePoint).comap (K S).subtype := by
    ext v
    exact Submodule.Quotient.mk_eq_zero _
  rw [hk, (Submodule.comapSubtypeEquivOfLe (pointSpan_le_K S S.basePoint)).finrank_eq] at hr
  have h1 := finrank_map_K d
  have h2 := finrank_pointSpan d
  omega

theorem K_ne_top (d : GeometryData S) : K S ≠ ⊤ := by
  let : Finite S.Point := d.finite_points
  intro h
  have hk := finrank_K d
  rw [h, finrank_top] at hk
  have hu : finrank (ZMod 2) (U S) = 15 := by
    let := Fintype.ofFinite S.Point
    simpa only [Module.finrank_pi, Nat.card_eq_fintype_card] using d.card_points
  omega
variable (S)
def permutationRepresentation : Representation (ZMod 2) G (U S) :=
  (BinaryPermutation.representation S.Point).comp (MulAction.toPermHom G S.Point)

theorem lineVector_action (g : G) (l : S.Line) :
    permutationRepresentation S g (lineVector S l) = lineVector S (g • l) := by
  classical
  ext x
  change (if S.Inc (g⁻¹ • x) l then 1 else 0) = if S.Inc x (g • l) then 1 else 0
  have hi : S.Inc (g⁻¹ • x) l ↔ S.Inc x (g • l) := by
    constructor
    · intro h
      simpa only [smul_inv_smul] using h.smul S g
    · intro h
      simpa only [inv_smul_smul] using h.smul S g⁻¹
  simp only [hi]

theorem pointVector_action (g : G) (x : S.Point) :
    permutationRepresentation S g (pointVector S x) = pointVector S (g • x) := by
  classical
  ext y
  change (Pi.single x (1 : ZMod 2) : U S) (g⁻¹ • y) = (Pi.single (g • x) 1 : U S) y
  simp only [Pi.single_apply]
  have hi : g⁻¹ • y = x ↔ y = g • x := by
    constructor
    · intro h
      simpa only [smul_inv_smul] using congrArg (g • ·) h
    · intro h
      rw [h, inv_smul_smul]
  simp only [hi]

noncomputable def lineSubrepresentation : Subrepresentation (permutationRepresentation S) where
  toSubmodule := K S
  apply_mem_toSubmodule g v hv := by
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨l, rfl⟩ := hv
      rw [lineVector_action]
      exact Submodule.subset_span ⟨g • l, rfl⟩
    | zero => simpa only [map_zero] using (K S).zero_mem
    | add v w _ _ hv hw => simpa only [map_add] using (K S).add_mem hv hw
    | smul a v _ hv => simpa only [map_smul] using (K S).smul_mem a hv

abbrev V := U S ⧸ K S
noncomputable def quotientRepresentation : Representation (ZMod 2) G (V S) :=
  (lineSubrepresentation S).quotientRepresentation

noncomputable instance quotientDistribMulAction : DistribMulAction G (V S) where
  smul g v := quotientRepresentation S g v
  one_smul v := LinearMap.congr_fun (map_one (quotientRepresentation S)) v
  mul_smul g h v := LinearMap.congr_fun (map_mul (quotientRepresentation S) g h) v
  smul_zero g := map_zero (quotientRepresentation S g)
  smul_add g v w := map_add (quotientRepresentation S g) v w

noncomputable instance quotientSMulCommClass : SMulCommClass G (ZMod 2) (V S) where
  smul_comm g a v := map_smul (quotientRepresentation S g) a v

noncomputable def pointMap (x : S.Point) : V S := (K S).mkQ (pointVector S x)

theorem pointMap_equivariant (g : G) (x : S.Point) :
    pointMap S (g • x) = g • pointMap S x := by
  change (K S).mkQ (pointVector S (g • x)) =
    (K S).mkQ (permutationRepresentation S g (pointVector S x))
  rw [pointVector_action]

theorem span_pointMap [Finite S.Point] :
    Submodule.span (ZMod 2) (Set.range (pointMap S)) = ⊤ := by
  classical
  have hp : Submodule.span (ZMod 2) (Set.range (pointVector S)) = ⊤ := by
    have he : pointVector S = (Pi.basisFun (ZMod 2) S.Point) := by
      funext x
      exact (Pi.basisFun_apply _ _ x).symm
    rw [he]
    exact (Pi.basisFun (ZMod 2) S.Point).span_eq
  calc
    _ = (Submodule.span (ZMod 2) (Set.range (pointVector S))).map (K S).mkQ := by
      rw [Submodule.map_span, ← Set.range_comp]
      rfl
    _ = ⊤ := by rw [hp, Submodule.map_top, Submodule.range_mkQ]

variable {S}
theorem pointMap_line (d : GeometryData S) (x y : S.Point) (hxy : x ≠ y) :
    ∃ z, pointMap S x + pointMap S y = pointMap S z := by
  classical
  obtain ⟨l, z, hzx, hzy, hl⟩ := d.line_points x y hxy
  have he : lineVector S l = pointVector S x + pointVector S y + pointVector S z := by
    ext p
    simp only [lineVector, pointVector, Pi.add_apply, Pi.single_apply, hl]
    by_cases hx : p = x <;> by_cases hy : p = y <;> by_cases hz : p = z <;>
      simp_all
  have hk : (K S).mkQ (lineVector S l) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨l, rfl⟩)
  rw [he, map_add, map_add] at hk
  refine ⟨z, ?_⟩
  change pointMap S x + pointMap S y + pointMap S z = 0 at hk
  have hz : -pointMap S z = pointMap S z :=
    neg_eq_of_add_eq_zero_left (by
      have htwo : (1 : ZMod 2) + 1 = 0 := rfl
      simpa only [add_smul, one_smul, zero_smul] using
        congrArg (fun a : ZMod 2 => a • pointMap S z) htwo)
  exact (eq_neg_of_add_eq_zero_left hk).trans hz

theorem quotient_nontrivial (d : GeometryData S) : Nontrivial (V S) :=
  Submodule.Quotient.nontrivial_iff.mpr (K_ne_top d)

theorem pointMap_nonzero (d : GeometryData S) (x : S.Point) : pointMap S x ≠ 0 := by
  let : Finite S.Point := d.finite_points
  let : Nontrivial (V S) := quotient_nontrivial d
  exact Theory.LinearAlgebra.BinaryPointMap.nonzero_of_pretransitive
    (pointMap S) (pointMap_equivariant S) (span_pointMap S) x

theorem pointMap_bijective (d : GeometryData S) :
    Function.Bijective (fun x => (⟨pointMap S x, pointMap_nonzero d x⟩ :
      {v : V S // v ≠ 0})) := by
  let : Finite S.Point := d.finite_points
  exact Theory.LinearAlgebra.BinaryPointMap.bijective_nonzero
    (pointMap S) (pointMap_nonzero d) (pointMap_line d) (span_pointMap S)

theorem quotient_finrank (d : GeometryData S) : finrank (ZMod 2) (V S) = 4 := by
  let : Finite S.Point := d.finite_points
  exact Theory.LinearAlgebra.BinaryPointMap.finrank
    (pointMap S) (pointMap_nonzero d) (pointMap_line d) (span_pointMap S)
    4 (by rw [d.card_points]; decide)

theorem quotient_faithful (d : GeometryData S) : FaithfulSMul G (V S) := by
  let : Finite S.Point := d.finite_points
  let : Nontrivial (V S) := quotient_nontrivial d
  let : FaithfulSMul G S.Point := d.faithful_points
  exact Theory.LinearAlgebra.BinaryPointMap.faithful_of_pretransitive
    (pointMap S) (pointMap_equivariant S) (pointMap_line d) (span_pointMap S)

noncomputable def linearAction : G →* (V S ≃ₗ[ZMod 2] V S) :=
  DistribMulAction.toModuleAut (ZMod 2) (V S)

theorem linearAction_injective (d : GeometryData S) :
    Function.Injective (linearAction (S := S)) := by
  let : FaithfulSMul G (V S) := quotient_faithful d
  intro g h he
  apply FaithfulSMul.eq_of_smul_eq_smul (α := V S)
  intro v
  exact LinearEquiv.congr_fun he v

theorem stabilizer_pointMap (d : GeometryData S) (x : S.Point) :
    MulAction.stabilizer G (pointMap S x) = MulAction.stabilizer G x := by
  ext g
  change g • pointMap S x = pointMap S x ↔ g • x = x
  rw [← pointMap_equivariant]
  exact (Theory.LinearAlgebra.BinaryPointMap.injective (pointMap S)
    (pointMap_nonzero d) (pointMap_line d)).eq_iff

theorem stabilizer_basePointMap (d : GeometryData S) :
    MulAction.stabilizer G (pointMap S S.basePoint) = S.family 0 := by
  rw [stabilizer_pointMap d, S.stabilizer_basePoint]

end Quasithin.I5.A3Recognition
