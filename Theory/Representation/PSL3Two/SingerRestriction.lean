module

public import Theory.Representation.PSL3Two.SingerDisplacement
public import Theory.SpecificGroups.PSL3Two.Cardinality
import Mathlib.GroupTheory.Sylow

/-!
# Restriction to an order-seven subgroup in binary SL₃

The natural module is fixed-point-free and transitive away from zero.
On the trace-zero endomorphism model of the Steinberg module, two explicit
commuting matrices give a basis of the Singer fixed plane. The displacement
bound gives the reverse dimension inequality. Sylow conjugacy transports
these facts to every actual subgroup of order seven.

The additive fixed-plane equivalence is used with the literal coordinate
map in the Ru1 fixed-subgroup lift. No subspace decomposition or stabilizer
claim is included in these initial restriction results.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3, printed pp.433–434 (PDF pp.444–445).
-/

open Matrix Representation Representation.BinaryOffender
open scoped Matrix
@[expose] public section
namespace BinaryLinearThree.SingerRestriction
open Matrix.PSL3Two.OuterInvolutionSinger
abbrev Mat := Matrix (Fin 3) (Fin 3) (ZMod 2)
def fixedMatrix (a b : ZMod 2) : Mat :=
  !![b,a,b; a,a,a+b; b,a+b,a+b]
def fixedVector (a b : ZMod 2) : Steinberg :=
  ⟨(fixedMatrix a b).toLin', by
    change (LinearMap.trace (ZMod 2) Vector) (fixedMatrix a b).toLin' = 0
    rw [Matrix.trace_toLin'_eq]
    simp [fixedMatrix, Matrix.trace, Fin.sum_univ_three]
    ring_nf
    simp only [show (2 : ZMod 2) = 0 by decide, mul_zero, add_zero]⟩
private theorem fixedMatrix_commutes (a b : ZMod 2) :
    fixedMatrix a b * singer.val = singer.val * fixedMatrix a b := by
  ext i j
  fin_cases i <;> fin_cases j <;>
  simp [fixedMatrix, Matrix.PSL3Two.OuterInvolutionSinger.singer,
    Matrix.mul_apply, Fin.sum_univ_three]
  all_goals abel_nf
  all_goals simp only [two_smul]
  all_goals first | rfl | simp only [CharTwo.add_self_eq_zero]
private theorem singer_fixed_vector_one :
    S singer (fixedVector 1 0) = fixedVector 1 0 := by
  apply Subtype.ext
  change (Matrix.toLin' singer.val) ∘ₗ
      ((fixedMatrix 1 0).toLin' ∘ₗ Matrix.toLin' (singer⁻¹).val) =
    (fixedMatrix 1 0).toLin'
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  have hmat : singer.val * (fixedMatrix 1 0 * (singer⁻¹).val) = fixedMatrix 1 0 := by
    have hi : singer.val * (singer⁻¹).val = 1 :=
      congrArg Subtype.val (mul_inv_cancel singer)
    rw [← mul_assoc, ← fixedMatrix_commutes, mul_assoc, hi, mul_one]
  exact congrArg Matrix.toLin' hmat
private theorem singer_fixed_vector_two :
    S singer (fixedVector 0 1) = fixedVector 0 1 := by
  apply Subtype.ext
  change (Matrix.toLin' singer.val) ∘ₗ
      ((fixedMatrix 0 1).toLin' ∘ₗ Matrix.toLin' (singer⁻¹).val) =
    (fixedMatrix 0 1).toLin'
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  have hmat : singer.val * (fixedMatrix 0 1 * (singer⁻¹).val) = fixedMatrix 0 1 := by
    have hi : singer.val * (singer⁻¹).val = 1 :=
      congrArg Subtype.val (mul_inv_cancel singer)
    rw [← mul_assoc, ← fixedMatrix_commutes, mul_assoc, hi, mul_one]
  exact congrArg Matrix.toLin' hmat
noncomputable def singerFixedOne : Steinberg := fixedVector 1 0
noncomputable def singerFixedTwo : Steinberg := fixedVector 0 1
private noncomputable def fixedVectorOne : fixedSpace S (Subgroup.zpowers singer) :=
  ⟨fixedVector 1 0, by rw [mem_fixedSpace_zpowers_iff]; exact singer_fixed_vector_one⟩
private noncomputable def fixedVectorTwo : fixedSpace S (Subgroup.zpowers singer) :=
  ⟨fixedVector 0 1, by rw [mem_fixedSpace_zpowers_iff]; exact singer_fixed_vector_two⟩
private noncomputable def fixedEmbedding :
    (ZMod 2 × ZMod 2) →ₗ[ZMod 2] fixedSpace S (Subgroup.zpowers singer) where
  toFun p := p.1 • fixedVectorOne + p.2 • fixedVectorTwo
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, add_smul]
    module
  map_smul' c p := by
    change (c * p.1) • fixedVectorOne + (c * p.2) • fixedVectorTwo =
      c • (p.1 • fixedVectorOne + p.2 • fixedVectorTwo)
    rw [smul_add, smul_smul, smul_smul]
    try module
private theorem fixedEmbedding_injective : Function.Injective fixedEmbedding := by
  intro p q h
  have h' := congrArg (fun f : Steinberg =>
    (f.val (Pi.single 0 1)) 1) (congrArg Subtype.val h)
  have h'' := congrArg (fun f : Steinberg =>
    (f.val (Pi.single 0 1)) 2) (congrArg Subtype.val h)
  have hp : p.1 = q.1 := by simpa [fixedEmbedding, fixedVectorOne, fixedVectorTwo,
    fixedVector, fixedMatrix] using h'
  have hq : p.2 = q.2 := by simpa [fixedEmbedding, fixedVectorOne, fixedVectorTwo,
    fixedVector, fixedMatrix] using h''
  exact Prod.ext hp hq
theorem finrank_fixedSpace_singer : Module.finrank (ZMod 2) (fixedSpace S (Subgroup.zpowers singer)) = 2 := by
  have hle := BinaryLinearThree.SingerDisplacement.six_le_fixedCodim_singer_steinberg
  have hdim := fixedCodim_add_finrank S (Subgroup.zpowers singer)
  rw [finrank_steinberg] at hdim
  have hmono := LinearMap.finrank_le_finrank_of_injective fixedEmbedding_injective
  have hr : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) = 2 := by simp
  rw [hr] at hmono
  omega

/-- The Singer subgroup is fixed-point-free on the natural three-space. -/
theorem natural_fixedSpace_singer :
    fixedSpace W (Subgroup.zpowers singer) = ⊥ := by
  apply _root_.eq_bot_iff.mpr
  intro v hv
  have hf : W singer v = v :=
    (mem_fixedSpace_zpowers_iff W singer v).mp hv
  have hc : ∀ v : Vector, singer.val *ᵥ v = v → v = 0 := by decide
  exact hc v hf

/-- Any subgroup of order seven is conjugate to the concrete Singer subgroup. -/
theorem exists_conjugate_singer (H : Subgroup Group) (hH : Nat.card H = 7) :
    ∃ g : Group, (Subgroup.zpowers singer).map (MulAut.conj g).toMonoidHom = H := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hc : Nat.card (Subgroup.zpowers singer) = 7 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by decide : singer ^ 7 = 1) (by decide : singer ≠ 1)
  let syl (K : Subgroup Group) (hK : Nat.card K = 7) : Sylow 7 Group :=
    (IsPGroup.of_card (n := 1) (by simpa using hK)).toSylow (by
      have hi := K.card_mul_index
      rw [hK, Matrix.PSL3Two.card_SL] at hi
      have hind : K.index = 24 := by omega
      rw [hind]
      decide)
  let P : Sylow 7 Group := syl (Subgroup.zpowers singer) hc
  let Q : Sylow 7 Group := syl H hH
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Group P Q
  exact ⟨g, congrArg (fun T : Sylow 7 Group => (T : Subgroup Group)) hg⟩

/-- The natural module has no nonzero fixed vector for any order-seven
subgroup.  This is the Sylow transport of the literal Singer calculation. -/
theorem natural_fixedSpace_order_seven (H : Subgroup Group) (hH : Nat.card H = 7) :
    fixedSpace W H = ⊥ := by
  obtain ⟨g, he⟩ := exists_conjugate_singer H hH
  rw [← he]
  apply _root_.eq_bot_iff.mpr
  intro v hv
  let e := fixedSpaceConjEquiv W (Subgroup.zpowers singer) g
  let u : fixedSpace W (Subgroup.zpowers singer) := e.symm ⟨v, hv⟩
  have hu : (u : Vector) = 0 := by
    have hu' : (u : Vector) ∈ (⊥ : Submodule (ZMod 2) Vector) := by
      rw [← natural_fixedSpace_singer]
      exact u.property
    change (u : Vector) = 0 at hu'
    exact hu'
  have huv := congrArg Subtype.val (e.apply_symm_apply ⟨v, hv⟩)
  calc
    v = (e u : Vector) := huv.symm
    _ = 0 := by
      have hue : u = 0 := Subtype.ext hu
      rw [hue]
      exact congrArg Subtype.val (map_zero e)

/-- An explicit additive model for the Singer fixed plane.  The target uses
the two coordinates of a binary basis, so its underlying multiplicative
group is the standard `E₄` carrier used by the source adapter. -/
noncomputable def fixedPlaneEquiv :
    fixedSpace S (Subgroup.zpowers singer) ≃+ (ZMod 2 × ZMod 2) := by
  let b := Module.finBasisOfFinrankEq (ZMod 2)
    (fixedSpace S (Subgroup.zpowers singer)) finrank_fixedSpace_singer
  let e : (Fin 2 → ZMod 2) ≃+ (ZMod 2 × ZMod 2) :=
    { finTwoArrowEquiv (ZMod 2) with
      map_add' := by intro x y; rfl }
  exact b.equivFun.toAddEquiv.trans e

theorem fixedPlaneEquiv_surjective : Function.Surjective fixedPlaneEquiv :=
  fixedPlaneEquiv.surjective

/-- Every order-seven subgroup has the same two-dimensional Steinberg fixed
space as the concrete Singer subgroup. -/
theorem finrank_fixedSpace_order_seven (H : Subgroup Group) (hH : Nat.card H = 7) :
    Module.finrank (ZMod 2) (fixedSpace S H) = 2 := by
  obtain ⟨g, he⟩ := exists_conjugate_singer H hH
  rw [← he, ← (fixedSpaceConjEquiv S (Subgroup.zpowers singer) g).finrank_eq]
  exact finrank_fixedSpace_singer

/-- The seven powers of the Singer element run through the nonzero natural vectors. -/
theorem natural_transitive_singer (u v : Vector) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g ∈ Subgroup.zpowers singer, W g u = v := by
  have hc : ∀ u v : Vector, u ≠ 0 → v ≠ 0 →
      ∃ i : Fin 7, (singer.val ^ (i : ℕ)) *ᵥ u = v := by decide +kernel
  obtain ⟨i, hi⟩ := hc u v hu hv
  exact ⟨singer ^ (i : ℕ), (Subgroup.zpowers singer).pow_mem (Subgroup.mem_zpowers singer) _, hi⟩

/-- Every subgroup of order seven is transitive on the nonzero natural vectors. -/
theorem natural_transitive_order_seven (H : Subgroup Group) (hH : Nat.card H = 7)
    (u v : Vector) (hu : u ≠ 0) (hv : v ≠ 0) :
    ∃ g ∈ H, W g u = v := by
  obtain ⟨g, he⟩ := exists_conjugate_singer H hH
  have hu' : W g⁻¹ u ≠ 0 := by
    intro h
    exact hu ((W.apply_bijective g⁻¹).injective (h.trans (map_zero _).symm))
  have hv' : W g⁻¹ v ≠ 0 := by
    intro h
    exact hv ((W.apply_bijective g⁻¹).injective (h.trans (map_zero _).symm))
  obtain ⟨h, hh, heq⟩ := natural_transitive_singer _ _ hu' hv'
  refine ⟨(MulAut.conj g) h, he ▸ Subgroup.mem_map.mpr ⟨h, hh, rfl⟩, ?_⟩
  change W (g * h * g⁻¹) u = v
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, heq,
    Representation.self_inv_apply]

/-- An actual additive isomorphism from the order-seven fixed plane to F₂². -/
noncomputable def fixedPlaneEquivOfCard (H : Subgroup Group) (hH : Nat.card H = 7) :
    fixedSpace S H ≃+ (ZMod 2 × ZMod 2) := by
  let b := Module.finBasisOfFinrankEq (ZMod 2) (fixedSpace S H)
    (finrank_fixedSpace_order_seven H hH)
  let e : (Fin 2 → ZMod 2) ≃+ (ZMod 2 × ZMod 2) :=
    { finTwoArrowEquiv (ZMod 2) with map_add' := by intro x y; rfl }
  exact b.equivFun.toAddEquiv.trans e
end BinaryLinearThree.SingerRestriction
