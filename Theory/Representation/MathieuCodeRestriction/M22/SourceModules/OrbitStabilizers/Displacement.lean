module

public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Action
/-!
# Full displacement under the M22 point stabilizers

Double transitivity of M22 makes a point stabilizer transitive on the other
21 moving coordinates. A fixed Golay word, after subtraction of a constant,
has support at most three; minimum distance forces it to vanish. The fixed
code space is therefore zero. Coordinate duality gives full cocode displacement
for both the inner and outer vector stabilizers. Perfectness of the inner
stabilizer suffices for the actual solvable-residual versions; the assembly
module discharges this premise using the compatible PSL(3,4) identification.

Source: Aschbacher--Smith, H.15.1(2) and 8.1.1, printed pp.398,712.
-/

public section
open Sporadic.Mathieu
open scoped BigOperators
namespace MathieuCode
noncomputable section
set_option maxRecDepth 10000

private theorem point_golay_fixed_constant (i : Fin 22) (v : golay)
    (hv : ∀ g : MulAction.stabilizer M22 i, golayRepresentation (m22Embedding g.val) v = v) :
    v ∈ codeLine := by
  obtain ⟨b, hb⟩ := exists_ne i
  let c := v.val (m22Coordinates b)
  have hm (j : Fin 22) (hj : j ≠ i) : v.val (m22Coordinates j) = c := by
    obtain ⟨g, hgi, hgj⟩ := (MulAction.is_two_pretransitive_iff.mp m22_isTwoPretransitive)
      hj.symm hb.symm
    have he := congrArg (fun w : golay => w.val (m22Coordinates b)) (hv ⟨g, hgi⟩)
    change v.val ((m22Embedding g).val.symm (m22Coordinates b)) = c at he
    have ha := m22Embedding_apply g j
    rw [hgj] at ha
    rw [← ha, Equiv.symm_apply_apply] at he
    exact he
  let w : Full := v.val - c • BinaryPermutation.allOne (Fin 24)
  have hw : w ∈ golay := golay.sub_mem v.property (golay.smul_mem c allOne_mem)
  have hwsmall : hammingNorm w ≤ 3 := by
    have hs : (Finset.univ.filter fun k => w k ≠ 0) ⊆ {0, 9, m22Coordinates i} := by
      intro k hk
      obtain h | h | ⟨j, rfl⟩ := pairResidual_coordinates_cover k
      · simp [h]
      · simp [h]
      · by_cases hj : j = i
        · simp [hj]
        · have hz : w (m22Coordinates j) = 0 := by
            simp [w, hm j hj, BinaryPermutation.allOne]
          exact False.elim ((Finset.mem_filter.mp hk).2 hz)
    exact (Finset.card_le_card hs).trans Finset.card_le_three

  have hz : w = 0 := by
    by_contra hn
    have hmin := native_golay_minimum hw hn
    omega
  change v.val ∈ BinaryPermutation.constants (Fin 24)
  exact Submodule.mem_span_singleton.mpr ⟨c, (sub_eq_zero.mp hz).symm⟩

/-- A point stabilizer fixes no vector in the actual ten-dimensional code. -/
theorem m22PointStabilizer_code_fixed_eq_bot (i : Fin 22) :
    Representation.BinaryOffender.fixedSpace m22CodeRepresentation (MulAction.stabilizer M22 i) = ⊥ := by
  apply le_antisymm _ bot_le
  rintro ⟨q, hqmem⟩ hq
  obtain ⟨v, rfl⟩ := codeLine.mkQ_surjective q
  change (⟨codeLine.mkQ v, hqmem⟩ : M22Code) = 0
  apply Subtype.ext
  apply (Submodule.Quotient.mk_eq_zero codeLine).mpr
  apply point_golay_fixed_constant i
  intro g
  have he := congrArg Subtype.val (hq g)
  change codeRepresentation (m22Embedding g.val) (codeLine.mkQ v) = codeLine.mkQ v at he
  exact golay_fixed_of_code_fixed (m22Embedding g.val) 0 (m22Embedding_fixed_zero g.val) v he

/-- Full displacement under the actual native point stabilizer. -/
theorem m22PointStabilizer_commutator_eq_top (i : Fin 22) :
    Representation.BinaryOffender.subspaceCommutator m22CocodeRepresentation ⊤
      (MulAction.stabilizer M22 i) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨v, rfl⟩ := m22CodeCocodeDuality.surjective f
  have hv : v ∈ Representation.BinaryOffender.fixedSpace m22CodeRepresentation (MulAction.stabilizer M22 i) := by
    intro g
    apply m22CodeCocodeDuality.injective
    apply LinearMap.ext
    intro w
    change m22CodeCocodeDuality (m22CodeRepresentation g.val v) w = m22CodeCocodeDuality v w
    rw [m22CodeCocodeDuality_equivariant_native]
    change m22CodeCocodeDuality v (m22CocodeRepresentation g.val⁻¹ w) = m22CodeCocodeDuality v w
    have hh := ((Submodule.mem_dualAnnihilator _).mp hf) _
      (Submodule.subset_span ⟨g.val⁻¹, (MulAction.stabilizer M22 i).inv_mem g.property,
        w, Submodule.mem_top, rfl⟩)
    simpa only [map_sub, sub_eq_zero] using hh
  rw [m22PointStabilizer_code_fixed_eq_bot, Submodule.mem_bot] at hv
  simp [hv]

theorem m22WeightTwoVector_commutator_eq_top (i : Fin 22) :
    Representation.BinaryOffender.subspaceCommutator m22CocodeRepresentation ⊤
      (m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i)) = ⊤ := by
  rw [m22WeightTwoVector_stabilizer]
  exact m22PointStabilizer_commutator_eq_top i

/-- The same displacement generators belong to the full outer stabilizer. -/
theorem m22WeightTwoVector_outer_commutator_eq_top (i : Fin 22) :
    Representation.BinaryOffender.subspaceCommutator m22OuterCocodeRepresentation ⊤
      (m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i)) = ⊤ := by
  apply top_unique
  conv_lhs => rw [← m22WeightTwoVector_commutator_eq_top i]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, hv, rfl⟩
  exact Submodule.subset_span ⟨m22ToPairStabilizer g, hg, v, hv, rfl⟩

/-- The residual conclusion, with the sole remaining group-structure input
made explicit until the native point-stabilizer identification is supplied. -/
theorem m22WeightTwoVector_residual_commutator_of_perfect (i : Fin 22)
    [Group.IsPerfect (MulAction.stabilizer M22 i)] :
    Representation.BinaryOffender.subspaceCommutator m22CocodeRepresentation ⊤
      ((Subgroup.solvableResidual
        (m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i))).map
        (m22CocodeStabilizer m22CocodeRepresentation (m22WeightTwoVector i)).subtype) = ⊤ := by
  rw [m22WeightTwoVector_stabilizer, Subgroup.solvableResidual_eq_top,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact m22PointStabilizer_commutator_eq_top i

/-- Perfectness of the inner stabilizer places its displacement generators
in the actual outer stabilizer's solvable residual. -/
theorem m22WeightTwoVector_outer_residual_commutator_of_perfect (i : Fin 22)
    [Group.IsPerfect (MulAction.stabilizer M22 i)] :
    Representation.BinaryOffender.subspaceCommutator m22OuterCocodeRepresentation ⊤
      ((Subgroup.solvableResidual
        (m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i))).map
        (m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i)).subtype) = ⊤ := by
  let P := (MulAction.stabilizer M22 i).map m22ToPairStabilizer
  let H := m22CocodeStabilizer m22OuterCocodeRepresentation (m22WeightTwoVector i)
  have hinj : Function.Injective m22ToPairStabilizer := by
    intro x y h
    exact m22Embedding_injective (congrArg Subtype.val h)
  let e := Subgroup.equivMapOfInjective (MulAction.stabilizer M22 i) m22ToPairStabilizer hinj
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hPH : P ≤ H := by
    rintro _ ⟨g, hg, rfl⟩
    change m22CocodeRepresentation g (m22WeightTwoVector i) = m22WeightTwoVector i
    exact (m22WeightTwoVector_fixed_iff g i).mpr hg
  have hres := Subgroup.le_map_solvableResidual_of_isPerfect P H hPH
  apply top_unique
  conv_lhs => rw [← m22PointStabilizer_commutator_eq_top i]
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, hv, rfl⟩
  exact Submodule.subset_span ⟨m22ToPairStabilizer g, hres ⟨g, hg, rfl⟩, v, hv, rfl⟩

end
end MathieuCode
