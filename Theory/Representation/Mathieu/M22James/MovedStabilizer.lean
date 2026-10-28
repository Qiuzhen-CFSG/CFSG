module
public import Theory.Representation.Mathieu.M22James.MovedStabilizer.Certificates
public import Theory.Representation.BinaryNaturalDual.VectorStabilizers.Inner
public import Theory.GroupTheory.PerfectTriangle
/-!
# Nonsolvable stabilizers on the Mathieu involution moved space

The five checked (2,3,5) pairs generate nontrivial perfect subgroups of the
fifteen native point stabilizers. The rank factorization covers every nonzero
vector in the native involution's moved space. Involution fusion and the
literal conjugation homomorphism transport this to every involution of the
actual cubic cover. No full vector-orbit classification is needed.

Source: the consequence of Aschbacher–Smith H.12.1(5),(7) used in the
proof of 12.6.26, printed pp.393–394,832. See Certificates for ATLAS
attribution and the checked coordinate convention.
-/
public section
set_option backward.isDefEq.respectTransparency false
namespace Sporadic.Mathieu.M22TripleCover.MovedStabilizer
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix Subgroup Representation BinaryNaturalDual.VectorStabilizers
open scoped Matrix

 theorem actorX_square (i : Fin 5) : actorX i ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((actorX i : Matrix12ˣ).val) ^ 2 = 1
  rw [coe_actorX, pow_two, x_square]
 theorem actorY_cube (i : Fin 5) : actorY i ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((actorY i : Matrix12ˣ).val) ^ 3 = 1
  rw [coe_actorY, pow_succ, pow_two, y_square, y_cube]
 theorem actorXY_fifth (i : Fin 5) : (actorX i * actorY i) ^ 5 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change (((actorX i : Matrix12ˣ).val) * ((actorY i : Matrix12ˣ).val)) ^ 5 = 1
  rw [coe_actorX, coe_actorY, xy_mul]
  calc
    matrixXY i ^ 5 = (matrixXY i * matrixXY i) *
        (matrixXY i * matrixXY i) * matrixXY i := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = 1 := by rw [xy_square, xy_four, xy_five]

 theorem point_stabilizer_not_solvable (i : Fin 15) :
    ¬ Group.IsSolvable (representationStabilizer binaryRepresentation (point i)) := by
  intro hs
  let j := pairIndex i
  let K := closure ({actorX j, actorY j} : Set M22TripleCover)
  let : Group.IsPerfect K := Group.isPerfect_closure_pair_of_coprime_triangle
    (actorX j) (actorY j) (m := 2) (n := 3) (k := 5) (by decide) (by decide)
    (actorX_square j) (actorY_cube j) (actorXY_fifth j)
  have hx : actorX j ∈ K := subset_closure (Or.inl rfl)
  have hne : actorX j ≠ 1 := by
    intro h
    apply x_nonidentity j
    exact (coe_actorX j).symm.trans (congrArg (fun x : M22TripleCover => (x : Matrix12ˣ).val) h)
  let : Nontrivial K := ⟨⟨⟨actorX j,hx⟩,1,fun h => hne (congrArg Subtype.val h)⟩⟩
  have hle : K ≤ representationStabilizer binaryRepresentation (point i) := by
    apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · change binaryRepresentation (actorX j) (point i) = point i
      rw [binaryRepresentation_apply,coe_actorX]
      exact x_fixes i
    · change binaryRepresentation (actorY j) (point i) = point i
      rw [binaryRepresentation_apply,coe_actorY]
      exact y_fixes i
  let := hs
  exact Group.IsPerfect.not_isSolvable K
    (Group.isSolvable_of_isSolvable_injective (inclusion_injective hle))

 theorem native_moved_stabilizer_not_solvable (v : BinarySpace) (hv : v ≠ 0)
    (hm : v ∈ (binaryRepresentation coreGeneratorB - LinearMap.id).range) :
    ¬ Group.IsSolvable (representationStabilizer binaryRepresentation v) := by
  obtain ⟨w,hw⟩ := hm
  have he : v = imageMatrix *ᵥ (factorMatrix *ᵥ w) := by
    calc
      v = binaryRepresentation coreGeneratorB w - w := hw.symm
      _ = matrixB *ᵥ w - w := by rw [binaryRepresentation_apply,coe_generatorB]
      _ = (matrixB - 1) *ᵥ w := by rw [Matrix.sub_mulVec,Matrix.one_mulVec]
      _ = _ := by rw [displacement_factor,Matrix.mulVec_mulVec]
  rw [he] at hv ⊢
  rcases image_cases (factorMatrix *ᵥ w) with h|⟨i,hi⟩
  · exact (hv h).elim
  · rw [hi]
    exact point_stabilizer_not_solvable i

 theorem moved_stabilizer_not_solvable (t : M22TripleCover) (ht : orderOf t = 2)
    (v : BinarySpace) (hv : v ≠ 0)
    (hm : v ∈ (binaryRepresentation t - LinearMap.id).range) :
    ¬ Group.IsSolvable (representationStabilizer binaryRepresentation v) := by
  obtain ⟨g,hg⟩ := isConj_iff.mp
    (NoFF.involutions_isConj coreGeneratorB t NoFF.coreGeneratorB_order ht)
  let ρ := binaryRepresentation
  let w := ρ g⁻¹ v
  have hw : w ≠ 0 := by
    intro he
    apply hv
    exact (ρ.apply_bijective g⁻¹).injective (he.trans (map_zero _).symm)
  have hmove : w ∈ (ρ coreGeneratorB - LinearMap.id).range := by
    obtain ⟨x,hx⟩ := hm
    refine ⟨ρ g⁻¹ x,?_⟩
    change ρ coreGeneratorB (ρ g⁻¹ x) - ρ g⁻¹ x = ρ g⁻¹ v
    rw [←hx,LinearMap.sub_apply,LinearMap.id_apply,map_sub]
    apply congrArg (fun y => y - ρ g⁻¹ x)
    have he : coreGeneratorB * g⁻¹ = g⁻¹ * t := by rw [←hg]; group
    rw [←Module.End.mul_apply,←map_mul,he,map_mul,Module.End.mul_apply]
  intro hs
  let := hs
  let P := representationStabilizer ρ w
  let Q := representationStabilizer ρ v
  have hback : ρ g w = v := by
    change ρ g (ρ g⁻¹ v) = v
    rw [←Module.End.mul_apply,←map_mul,mul_inv_cancel,map_one]
    rfl
  let f : P →* Q := ((MulAut.conj g).toMonoidHom.comp P.subtype).codRestrict Q (by
    intro x
    change ρ (g*x.val*g⁻¹) v = v
    simp only [map_mul,Module.End.mul_apply]
    change ρ g (ρ x.val w) = v
    exact (congrArg (ρ g) x.property).trans hback)
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    exact (MulAut.conj g).injective (congrArg Subtype.val he)
  exact native_moved_stabilizer_not_solvable w hw hmove
    (Group.isSolvable_of_isSolvable_injective hf)

end Sporadic.Mathieu.M22TripleCover.MovedStabilizer
