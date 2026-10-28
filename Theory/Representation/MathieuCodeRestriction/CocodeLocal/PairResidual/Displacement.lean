module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal
public import Theory.Representation.MathieuCodeRestriction.M22.Construction
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.FixedLift
public import Theory.Representation.MathieuCodeRestriction.Duality
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.DualCommutator
public import Theory.GroupTheory.SolvableResidual

/-!
# Full cocode displacement under the perfect pair subgroup

The embedded native M22 fixes coordinates 0 and 9 and is transitive on the
remaining 22 coordinates. A fixed code class lifts to a fixed Golay word
because coordinate 0 is fixed. Subtracting its common value on the moving
coordinates gives a Golay word of weight at most two, hence zero. Thus the
code fixed space vanishes, and the perfect code--cocode pairing proves full
cocode displacement. Simplicity and the composite order prove M22 perfect.
Conjugating this subgroup into every weight-two stabilizer places it inside
the stabilizer's actual solvable residual, mapped into the ambient actor.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, H.15.1(2),
printed p.398, and the perfect-residual use in 8.1.1, printed p.712.
-/

@[expose] public section

open Sporadic.Mathieu Representation.BinaryOffender
open scoped BigOperators
namespace MathieuCode
noncomputable section

/-- The native M22 moving coordinates are exactly the complement of 0 and 9. -/
lemma pairResidual_coordinates_cover (i : Fin 24) :
    i = 0 ∨ i = 9 ∨ ∃ j : Fin 22, m22Coordinates j = i := by
  revert i
  decide +kernel

/-- Every Golay word fixed by the embedded M22 is constant. -/
lemma pairResidual_golay_fixed_constant (v : golay)
    (hv : ∀ g : M22, golayRepresentation (m22Embedding g) v = v) :
    v ∈ codeLine := by
  let c := v.val (m22Coordinates 0)
  have hm (i : Fin 22) : v.val (m22Coordinates i) = c := by
    let := m22_isPretransitive
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M22 i (0 : Fin 22)
    have he := congrArg (fun w : golay => w.val (m22Coordinates 0)) (hv g)
    change v.val ((m22Embedding g).val.symm (m22Coordinates 0)) = c at he
    have ha := m22Embedding_apply g i
    rw [hg] at ha
    rw [← ha, Equiv.symm_apply_apply] at he
    exact he
  let w : Full := v.val - c • BinaryPermutation.allOne (Fin 24)
  have hw : w ∈ golay := golay.sub_mem v.property (golay.smul_mem c allOne_mem)
  have hwsmall : hammingNorm w ≤ 2 := by
    have hs : (Finset.univ.filter fun i => w i ≠ 0) ⊆ ({0, 9} : Finset (Fin 24)) := by
      intro i hi
      obtain h | h | ⟨j, rfl⟩ := pairResidual_coordinates_cover i
      · simp [h]
      · simp [h]
      · have hz : w (m22Coordinates j) = 0 := by
          simp [w, hm, BinaryPermutation.allOne]
        exact False.elim ((Finset.mem_filter.mp hi).2 hz)
    exact (Finset.card_le_card hs).trans (by decide)
  have hwzero : w = 0 := by
    by_contra h
    have hmin := native_golay_minimum hw h
    omega
  change v.val ∈ BinaryPermutation.constants (Fin 24)
  apply Submodule.mem_span_singleton.mpr
  exact ⟨c, (sub_eq_zero.mp hwzero).symm⟩

/-- The embedded M22 fixes no nonzero vector of the eleven-dimensional code. -/
lemma pairResidual_code_fixed_eq_bot :
    fixedSpace codeRepresentation m22Embedding.range = ⊥ := by
  apply le_antisymm _ bot_le
  intro q hq
  obtain ⟨v, rfl⟩ := codeLine.mkQ_surjective q
  change codeLine.mkQ v = 0
  apply (Submodule.Quotient.mk_eq_zero codeLine).mpr
  apply pairResidual_golay_fixed_constant
  intro g
  exact golay_fixed_of_code_fixed (m22Embedding g) 0 (m22Embedding_fixed_zero g) v
    (hq ⟨m22Embedding g, ⟨g, rfl⟩⟩)

/-- The embedded M22 generates the whole eleven-dimensional cocode by displacements. -/
lemma pairResidual_cocode_commutator_eq_top :
    subspaceCommutator cocodeRepresentation ⊤ m22Embedding.range = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro f hf
  obtain ⟨v, rfl⟩ := codeDuality.toLinearEquiv.surjective f
  have hv : v ∈ fixedSpace codeRepresentation m22Embedding.range := by
    intro g
    apply codeCocodePairing_injective
    apply LinearMap.ext
    intro w
    have he := codeCocodePairing_invariant g.val v (cocodeRepresentation g.val⁻¹ w)
    simp only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      Module.End.one_apply] at he
    change codeCocodePairing (codeRepresentation g.val v) w = codeCocodePairing v w
    rw [he]
    have hh := ((Submodule.mem_dualAnnihilator _).mp hf) _
      (Submodule.subset_span ⟨g.val⁻¹, m22Embedding.range.inv_mem g.property,
        w, Submodule.mem_top, rfl⟩)
    change codeCocodePairing v (cocodeRepresentation g.val⁻¹ w - w) = 0 at hh
    simpa only [map_sub, sub_eq_zero] using hh
  rw [pairResidual_code_fixed_eq_bot, Submodule.mem_bot] at hv
  simp [hv]

/-- Perfectness of the actual native group, from simplicity and its composite order. -/
lemma pairResidual_m22_perfect : Group.IsPerfect M22 := by
  let := m22_isSimpleGroup
  refine ⟨(IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator M22)
    inferInstance).resolve_left ?_⟩
  intro h
  let := (commutator_eq_bot_iff M22).mp h
  let : CommGroup M22 := { (inferInstance : Group M22) with mul_comm := IsMulCommutative.is_comm.comm }
  have hp := IsSimpleGroup.prime_card (α := M22)
  rw [m22_order] at hp
  norm_num at hp


private lemma commutator_mono_actor {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {H K : Subgroup G} (h : H ≤ K) :
    subspaceCommutator ρ ⊤ H ≤ subspaceCommutator ρ ⊤ K := by
  apply Submodule.span_le.mpr
  rintro _ ⟨g, hg, v, hv, rfl⟩
  exact Submodule.subset_span ⟨g, h hg, v, hv, rfl⟩

private lemma commutator_conjugate_eq_top {G V : Type*} [Group G] [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    {H K : Subgroup G} (a : G) (h : ∀ g ∈ H, a * g * a⁻¹ ∈ K)
    (hfull : subspaceCommutator ρ ⊤ H = ⊤) :
    subspaceCommutator ρ ⊤ K = ⊤ := by
  let C := subspaceCommutator ρ ⊤ K
  have hc : subspaceCommutator ρ ⊤ H ≤ C.comap (ρ a) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    have hm : ρ (a * g * a⁻¹) (ρ a v) - ρ a v ∈ C :=
      Submodule.subset_span ⟨_, h g hg, _, Submodule.mem_top, rfl⟩
    change ρ a (ρ g v - v) ∈ C
    simpa only [map_sub, map_mul, Module.End.mul_apply,
      ρ.inv_self_apply] using hm
  apply top_unique
  intro v _
  have hm := hc (hfull ▸ (Submodule.mem_top : ρ a⁻¹ v ∈ (⊤ : Submodule (ZMod 2) V)))
  change ρ a (ρ a⁻¹ v) ∈ C at hm
  simpa only [ρ.self_inv_apply] using hm

private lemma residual_full_of_orbit {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G Cocode) (f : M22 →* G)
    (hf : subspaceCommutator ρ ⊤ f.range = ⊤)
    (v : Cocode) (hfix : ∀ g : M22, ρ (f g) v = v)
    (a : G) :
    subspaceCommutator ρ ⊤
      ((Subgroup.solvableResidual (cocodeVectorStabilizer ρ (ρ a v))).map
        (cocodeVectorStabilizer ρ (ρ a v)).subtype) = ⊤ := by
  let := pairResidual_m22_perfect
  let f' : M22 →* G := (MulAut.conj a).toMonoidHom.comp f
  let := Group.IsPerfect.range f'
  have hle : f'.range ≤ cocodeVectorStabilizer ρ (ρ a v) := by
    rintro _ ⟨g, rfl⟩
    change ρ (a * f g * a⁻¹) (ρ a v) = ρ a v
    simp only [map_mul, Module.End.mul_apply, ρ.inv_self_apply, hfix]
  have hr := Subgroup.le_map_solvableResidual_of_isPerfect _ _ hle
  apply commutator_conjugate_eq_top ρ a _ hf
  rintro _ ⟨g, rfl⟩
  exact hr ⟨g, rfl⟩

lemma pairVector_residual_commutator (B : PointPair) :
    subspaceCommutator cocodeRepresentation ⊤
      ((Subgroup.solvableResidual
        (cocodeVectorStabilizer cocodeRepresentation (pairVector B))).map
        (cocodeVectorStabilizer cocodeRepresentation (pairVector B)).subtype) = ⊤ := by
  obtain ⟨a, ha⟩ := weightTwoOrbit_transitive (pointPair 9) B
  rw [← ha]
  apply residual_full_of_orbit cocodeRepresentation m22Embedding
    pairResidual_cocode_commutator_eq_top
  intro g
  change m23CocodeRepresentation (m22InM23 g) (m23PairVector 9) = m23PairVector 9
  rw [m23PairVector_fixed_iff]
  exact (m23EquivM22PointStabilizer g).property

lemma m23PairVector_residual_commutator (i : Fin 23) :
    subspaceCommutator m23CocodeRepresentation ⊤
      ((Subgroup.solvableResidual
        (cocodeVectorStabilizer m23CocodeRepresentation (m23PairVector i))).map
        (cocodeVectorStabilizer m23CocodeRepresentation (m23PairVector i)).subtype) = ⊤ := by
  have hfull : subspaceCommutator m23CocodeRepresentation ⊤ m22InM23.range = ⊤ := by
    apply top_unique
    apply pairResidual_cocode_commutator_eq_top.ge.trans
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨g, rfl⟩, v, hv, rfl⟩
    exact Submodule.subset_span ⟨m22InM23 g, ⟨g, rfl⟩, v, hv, rfl⟩
  obtain ⟨a, ha⟩ := m23WeightTwoOrbit_transitive 9 i
  rw [← ha]
  apply residual_full_of_orbit m23CocodeRepresentation m22InM23 hfull
  intro g
  rw [m23PairVector_fixed_iff]
  exact (m23EquivM22PointStabilizer g).property

lemma weightTwoOrbit_residual_commutator {v : Cocode} (hv : v ∈ weightTwoOrbit) :
    subspaceCommutator cocodeRepresentation ⊤
      ((Subgroup.solvableResidual (cocodeVectorStabilizer cocodeRepresentation v)).map
        (cocodeVectorStabilizer cocodeRepresentation v).subtype) = ⊤ := by
  obtain ⟨B, rfl⟩ := hv
  exact pairVector_residual_commutator B

lemma m23WeightTwoOrbit_residual_commutator {v : Cocode} (hv : v ∈ m23WeightTwoOrbit) :
    subspaceCommutator m23CocodeRepresentation ⊤
      ((Subgroup.solvableResidual (cocodeVectorStabilizer m23CocodeRepresentation v)).map
        (cocodeVectorStabilizer m23CocodeRepresentation v).subtype) = ⊤ := by
  obtain ⟨i, rfl⟩ := hv
  exact m23PairVector_residual_commutator i

lemma weightTwoOrbit_stabilizer_commutator {v : Cocode} (hv : v ∈ weightTwoOrbit) :
    subspaceCommutator cocodeRepresentation ⊤
      (cocodeVectorStabilizer cocodeRepresentation v) = ⊤ := by
  apply top_unique
  apply (weightTwoOrbit_residual_commutator hv).ge.trans
  exact commutator_mono_actor _ (Subgroup.map_subtype_le _)

lemma m23WeightTwoOrbit_stabilizer_commutator {v : Cocode} (hv : v ∈ m23WeightTwoOrbit) :
    subspaceCommutator m23CocodeRepresentation ⊤
      (cocodeVectorStabilizer m23CocodeRepresentation v) = ⊤ := by
  apply top_unique
  apply (m23WeightTwoOrbit_residual_commutator hv).ge.trans
  exact commutator_mono_actor _ (Subgroup.map_subtype_le _)

end
end MathieuCode
