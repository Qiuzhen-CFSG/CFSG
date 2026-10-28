module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.StrictCode.Checks
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF
public import Theory.Representation.BinaryOffender.SmallMovedProducts
public import Theory.Representation.BinaryOffender.CubicRatio
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
/-!
# Strict quadratic ratios for the native Mathieu code modules

Every quadratic elementary actor has order at most four. For an actor of rank
one, an involution moves at least four dimensions. For rank two, the checked
Sylow-pair certificates exhibit five independent cocode displacement vectors.
Literal code--cocode duality identifies that moved dimension with the code's
fixed codimension. Sylow conjugacy and the point embedding give the global M24
and M23 bounds.

Source: Aschbacher--Smith K.4.1 and K.4.2--3, printed pp.458--459; the strict
bound is used in the A5 terminal argument of Chapter 13.
-/
public section
open Sporadic.Mathieu Representation Representation.BinaryOffender
open Sporadic.Mathieu.M24ChapterHStabilizers.ElementaryFusion.SylowCoverage
open MathieuCode.CocodeOctad.Involutions
namespace MathieuCode.QuadraticActors.StrictCode
private lemma matrix_column_mem (A : Subgroup M24) (v : Fin 192)
    (hv : (native v).val ∈ A) (j : Fin 11) :
    (matrix v).col j ∈ (subspaceCommutator cocodeRepresentation ⊤ A).map coordinates := by
  refine ⟨_, Submodule.subset_span ⟨(native v).val, hv,
    sectionMap (Pi.single j 1), Submodule.mem_top, rfl⟩, ?_⟩
  have h := LinearMap.congr_fun (displacementMatrix_eq (native v).val) (Pi.single j 1)
  rw [displacementMatrix_native] at h
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using h.symm

private lemma selected_rank_le (A : Subgroup M24) (v w : Fin 192)
    (hv : (native v).val ∈ A) (hw : (native w).val ∈ A) :
    (selected v w).rank ≤ fixedCodim codeRepresentation A := by
  have hle : Submodule.span (ZMod 2) (Set.range (selected v w).col) ≤
      (subspaceCommutator cocodeRepresentation ⊤ A).map coordinates := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    by_cases hj : columnIndex v w j < 11
    · have he : (selected v w).col j =
          (matrix v).col ⟨columnIndex v w j % 11, Nat.mod_lt _ (by decide)⟩ := by
        ext i
        simp only [selected, Matrix.col_apply, if_pos hj]
      rw [he]
      exact matrix_column_mem A v hv _
    · have he : (selected v w).col j =
          (matrix w).col ⟨columnIndex v w j % 11, Nat.mod_lt _ (by decide)⟩ := by
        ext i
        simp only [selected, Matrix.col_apply, if_neg hj]
      rw [he]
      exact matrix_column_mem A w hw _
  have hf := Submodule.finrank_mono hle
  rw [← Matrix.rank_eq_finrank_span_cols] at hf
  have he := coordinateEquiv.finrank_map_eq (subspaceCommutator cocodeRepresentation ⊤ A)
  change Module.finrank (ZMod 2)
      ((subspaceCommutator cocodeRepresentation ⊤ A).map coordinates) = _ at he
  rw [he] at hf
  have hd := fixedCodim_map_equivariant codeRepresentation cocodeRepresentation.dual
    (MonoidHom.id M24) codeDuality.toLinearEquiv
    (fun g x => LinearMap.congr_fun (codeDuality.isIntertwining' g) x) A
  rw [Subgroup.map_id, fixedCodim_dual_eq_moved_finrank] at hd
  exact hf.trans_eq hd.symm

private lemma native_zero : (native 0).val = (1 : M24) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (native 0).val.val x = x
  rw [native_apply]
  have h : vertexPoint 0 = id := by decide +kernel
  exact congrFun h x

private lemma quadratic_code_to_cocode {A : Subgroup M24}
    (hq : IsQuadratic codeRepresentation A) : IsQuadratic cocodeRepresentation A := by
  have hd : IsQuadratic cocodeRepresentation.dual A :=
    quadratic_of_equivariant_surjection codeRepresentation cocodeRepresentation.dual
      codeDuality.toLinearMap codeDuality.toLinearEquiv.surjective
      (fun g v => LinearMap.congr_fun (codeDuality.isIntertwining' g) v) A hq
  have hcomm : Coinvariants.ker (Representation.dual (cocodeRepresentation.comp A.subtype)) ≤
      Representation.invariants (Representation.dual (cocodeRepresentation.comp A.subtype)) := by
    rw [commutator_le_invariants_iff]
    intro g t v
    exact hd g g.property t t.property v
  have h := (commutator_le_invariants_iff_dual (cocodeRepresentation.comp A.subtype)).mpr hcomm
  rw [commutator_le_invariants_iff] at h
  intro g hg t ht v
  exact h ⟨g,hg⟩ ⟨t,ht⟩ v

private lemma native_rank_two_bound (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hS : A ≤ Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate)
    (hq : IsQuadratic codeRepresentation A) (hr : rank A = 2) :
    5 ≤ fixedCodim codeRepresentation A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have ha2 : orderOf a = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
  obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra hn
    push Not at hn
    have hle : A ≤ Subgroup.zpowers a := by
      intro b hb
      by_cases hb1 : b = 1
      · simpa only [hb1] using (Subgroup.zpowers a).one_mem
      · rw [hn b hb hb1]
        exact Subgroup.mem_zpowers a
    have hcard := Subgroup.card_le_of_le hle
    rw [hA.card_eq_two_pow_rank, hr, Nat.card_zpowers, ha2] at hcard
    omega
  obtain ⟨v, hv⟩ := vertex_of_square
    (⟨a, hS ha⟩ : Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate)
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian a ha))
  obtain ⟨w, hw⟩ := vertex_of_square
    (⟨b, hS hb⟩ : Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate)
    (Subtype.ext (elemPow_eq_one_of_isElementaryAbelian b hb))
  have hv' : (native v).val = a := congrArg Subtype.val hv
  have hw' : (native w).val = b := congrArg Subtype.val hw
  have hv0 : v ≠ 0 := by intro he; apply ha1; rw [he, native_zero] at hv'; exact hv'.symm
  have hw0 : w ≠ 0 := by intro he; apply hb1; rw [he, native_zero] at hw'; exact hw'.symm
  have hvw : v ≠ w := by intro he; exact hba (hw'.symm.trans (he ▸ hv'))
  have hvA : (native v).val ∈ A := hv'.symm ▸ ha
  have hwA : (native w).val ∈ A := hw'.symm ▸ hb
  have hadj := native_quadratic_adjacent (quadratic_code_to_cocode hq) v w hvA hwA
  have hcert := certificate_check v w hv0 hw0 hvw hadj
  have hlow : 5 ≤ (selected v w).rank := by
    have h := Matrix.rank_mul_le_right (leftInverse v w) (selected v w)
    simpa only [hcert, Matrix.rank_one, Fintype.card_fin] using h
  exact hlow.trans (selected_rank_le A v w hvA hwA)

/-- A quadratic elementary actor of rank two moves at least five code dimensions. -/
theorem rank_two_bound (A : Subgroup M24) (hA : IsElementaryTwo A)
    (hq : IsQuadratic codeRepresentation A) (hr : rank A = 2) :
    5 ≤ fixedCodim codeRepresentation A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 S
    Sporadic.Mathieu.M24LocalGeometry.SextetCore.nativeSylow
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom =
      Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.candidate := congrArg Sylow.toSubgroup hg
  have hB := native_rank_two_bound (A.map (MulAut.conj g).toMonoidHom)
    (hA.map_conj g) (hg' ▸ Subgroup.map_mono hAS) (quadratic_conj _ hq g)
    (by rw [rank_map_conj, hr])
  rwa [fixedCodim_map_conj] at hB

/-- Every nontrivial quadratic elementary actor on the M24 code has ratio greater than two. -/
theorem code_quadraticRatio_gt_two :
    2 < quadraticRatio codeRepresentation := by
  by_contra! hle
  obtain ⟨A, hA, hq, hsmall⟩ := (quadraticRatio_le_iff codeRepresentation (by simp)).mp hle
  have hdim := (actionRatio_le_nat_iff codeRepresentation hA 2).mp hsmall
  let : IsElementaryAbelian 2 A := hA.2
  have hcard := m24_code_card_le_four A hq
  have hr : rank A ≤ 2 :=
    (Nat.log_mono_right hcard : Nat.log 2 (Nat.card A) ≤ Nat.log 2 4)
  by_cases hr2 : rank A = 2
  · have hb := rank_two_bound A hA hq hr2
    omega
  · have hr1 : rank A = 1 := by have := hA.rank_pos; omega
    obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ho : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hd := m24_cocode_involution_gt_two a ho
    rw [← code_cocode_fixedCodim_zpowers] at hd
    have hf := Submodule.finrank_mono
      (fixedSpace_antitone codeRepresentation (Subgroup.zpowers_le.mpr ha))
    have hdimA := fixedCodim_add_finrank codeRepresentation A
    have hdima := fixedCodim_add_finrank codeRepresentation (Subgroup.zpowers a)
    omega

/-- The literal M23 code restriction has strict quadratic ratio greater than two. -/
theorem m23Code_quadraticRatio_gt_two :
    2 < quadraticRatio m23CodeRepresentation :=
  code_quadraticRatio_gt_two.trans_le
    (quadraticRatio_le_of_injective_equivariant m23CodeRepresentation codeRepresentation
      pointEmbedding pointEmbedding_injective (LinearEquiv.refl _ _) (fun _ _ => rfl))
end MathieuCode.QuadraticActors.StrictCode
