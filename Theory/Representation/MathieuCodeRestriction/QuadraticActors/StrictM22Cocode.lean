module
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.StrictM22Cocode.Checks
public import Theory.Representation.MathieuCodeRestriction.QuadraticActors.NoFF
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.BinaryOffender.CubicRatio
/-!
# The strict quadratic bound for the genuine M22 cocode

A quadratic elementary actor has order at most four. For a four-group,
the checked Sylow-pair certificates give five independent columns in the
two displacement maps on the literal quotient by the marked pair line.
The common kernel contains the actor's fixed space, so rank-nullity gives
fixed codimension at least five. Involutions have codimension at least three.
Sylow conjugacy gives the bound for every inner or outer actor.

The Chapter 13 Mathieu recognition consumer uses this to discard the cocode
and retain the actual code intertwiner, with no universal B.4.5 callback.
Source: Aschbacher–Smith, K.4.4, printed p.459; 13.8.21(2), printed p.956.
-/
public section
open Sporadic.Mathieu Representation Representation.BinaryOffender
open MathieuCode.CocodeOctad.Involutions
namespace MathieuCode.QuadraticActors.StrictM22Cocode
noncomputable section

private def quotientCoordinates : M22Cocode →ₗ[ZMod 2] Coordinates :=
  m22PairLine.liftQ
    (coordinates - (LinearMap.proj 0 ∘ₗ coordinates).smulRight pairCoordinate) (by
      intro x hx
      apply LinearMap.mem_ker.mpr
      ext i
      exact pair_line_coordinate x hx i)

private lemma quotient_displacement (a : m22PairStabilizer) (x : Cocode) (i : Fin 11) :
    quotientCoordinates (m22OuterCocodeRepresentation a (m22PairLine.mkQ x) -
      m22PairLine.mkQ x) i =
      coordinates (cocodeRepresentation a.val x - x) i -
        coordinates (cocodeRepresentation a.val x - x) 0 * pairCoordinate i := by
  rw [m22OuterCocodeRepresentation_mk, ← map_sub]
  rfl

private def pairMap (a b : m22PairStabilizer) : M22Cocode →ₗ[ZMod 2] (Fin 22 → ZMod 2) :=
  LinearMap.pi fun i => (LinearMap.proj ⟨i.val % 11, Nat.mod_lt _ (by decide)⟩).comp
    (quotientCoordinates.comp
      (m22OuterCocodeRepresentation (if i.val < 11 then a else b) - LinearMap.id))

private lemma matrix_entry (v : Fin 72) (i j : Fin 11) :
    outerMatrix v i j =
      coordinates (cocodeRepresentation (outerNative v) (sectionMap (Pi.single j 1)) -
        sectionMap (Pi.single j 1)) i := by
  have h := LinearMap.congr_fun (displacementMatrix_eq (outerNative v)) (Pi.single j 1)
  rw [displacementMatrix_outerNative] at h
  have hh := congrFun h i
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul, Matrix.col_apply,
    LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using hh

private lemma pair_column (a b : m22PairStabilizer) (v w : Fin 72)
    (hv : outerNative v = a.val) (hw : outerNative w = b.val) (j : Fin 11) :
    (pairMatrix v w).col j =
      pairMap a b (m22PairLine.mkQ (sectionMap (Pi.single j 1))) := by
  ext i
  simp only [Matrix.col_apply, pairMatrix]
  change _ = quotientCoordinates
    (m22OuterCocodeRepresentation (if i.val < 11 then a else b)
      (m22PairLine.mkQ (sectionMap (Pi.single j 1))) -
        m22PairLine.mkQ (sectionMap (Pi.single j 1))) _
  rw [quotient_displacement]
  split_ifs <;> simp only [matrix_entry, hv, hw]

private lemma selected_rank_le (A : Subgroup m22PairStabilizer)
    (a b : m22PairStabilizer) (ha : a ∈ A) (hb : b ∈ A) (v w : Fin 72)
    (hv : outerNative v = a.val) (hw : outerNative w = b.val) :
    (selected v w).rank ≤ fixedCodim m22OuterCocodeRepresentation A := by
  have hle : Submodule.span (ZMod 2) (Set.range (selected v w).col) ≤
      LinearMap.range (pairMap a b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact ⟨_, (pair_column a b v w hv hw (columnIndex v w j)).symm⟩
  have hf := Submodule.finrank_mono hle
  rw [← Matrix.rank_eq_finrank_span_cols] at hf
  have hk : fixedSpace m22OuterCocodeRepresentation A ≤ LinearMap.ker (pairMap a b) := by
    intro x hx
    apply LinearMap.mem_ker.mpr
    ext i
    change quotientCoordinates
      (m22OuterCocodeRepresentation (if i.val < 11 then a else b) x - x) _ = 0
    have ha' : m22OuterCocodeRepresentation a x = x := hx ⟨a,ha⟩
    have hb' : m22OuterCocodeRepresentation b x = x := hx ⟨b,hb⟩
    split_ifs <;> simp only [ha', hb', sub_self, map_zero, Pi.zero_apply]
  have hkdim := Submodule.finrank_mono hk
  have hr := (pairMap a b).finrank_range_add_finrank_ker
  have hd := fixedCodim_add_finrank m22OuterCocodeRepresentation A
  omega

private lemma outer_zero : outerNative 0 = (1 : M24) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (outerNative 0).val x = x
  rw [outerNative_apply]
  have h : outerPoint 0 = id := by decide +kernel
  exact congrFun h x

private lemma native_rank_two_bound (A : Subgroup m22PairStabilizer)
    (hA : IsElementaryTwo A)
    (hS : A ≤ M22ChapterH.CompatibleSylow.outerGroup)
    (hq : IsQuadratic m22OuterCocodeRepresentation A) (hr : rank A = 2) :
    5 ≤ fixedCodim m22OuterCocodeRepresentation A := by
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
  obtain ⟨v, hv⟩ := outer_vertex_of_square a (hS ha)
    (elemPow_eq_one_of_isElementaryAbelian a ha)
  obtain ⟨w, hw⟩ := outer_vertex_of_square b (hS hb)
    (elemPow_eq_one_of_isElementaryAbelian b hb)
  have hv0 : v ≠ 0 := by
    intro he
    apply ha1
    apply Subtype.ext
    rw [he, outer_zero] at hv
    exact hv.symm
  have hw0 : w ≠ 0 := by
    intro he
    apply hb1
    apply Subtype.ext
    rw [he, outer_zero] at hw
    exact hw.symm
  have hvw : v ≠ w := by
    intro he
    exact hba (Subtype.ext (hw.symm.trans (he ▸ hv)))
  have hadj := outer_quadratic_adjacent hq ⟨a,ha⟩ ⟨b,hb⟩ v w hv hw
  have hcert := certificate_check v w hv0 hw0 hvw hadj
  have hlow : 5 ≤ (selected v w).rank := by
    have h := Matrix.rank_mul_le_right (leftInverse v w) (selected v w)
    simpa only [hcert, Matrix.rank_one, Fintype.card_fin] using h
  exact hlow.trans (selected_rank_le A a b ha hb v w hv hw)

/-- A quadratic four-group fixes at most five dimensions in the literal M22 cocode. -/
theorem rank_two_bound (A : Subgroup m22PairStabilizer) (hA : IsElementaryTwo A)
    (hq : IsQuadratic m22OuterCocodeRepresentation A) (hr : rank A = 2) :
    5 ≤ fixedCodim m22OuterCocodeRepresentation A := by
  let : IsElementaryAbelian 2 A := hA.2
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq m22PairStabilizer S
    M22ChapterH.CompatibleSylow.outer
  have hg' : S.toSubgroup.map (MulAut.conj g).toMonoidHom =
      M22ChapterH.CompatibleSylow.outerGroup := congrArg Sylow.toSubgroup hg
  have hB := native_rank_two_bound (A.map (MulAut.conj g).toMonoidHom)
    (hA.map_conj g) (hg' ▸ Subgroup.map_mono hAS) (quadratic_conj _ hq g)
    (by rw [rank_map_conj, hr])
  rwa [fixedCodim_map_conj] at hB

/-- The native M22 cocode has strict quadratic ratio greater than two,
including the setwise pair stabilizer's outer actors. -/
theorem m22OuterCocode_quadraticRatio_gt_two :
    2 < quadraticRatio m22OuterCocodeRepresentation := by
  by_contra! hle
  obtain ⟨A, hA, hq, hsmall⟩ :=
    (quadraticRatio_le_iff m22OuterCocodeRepresentation (by simp)).mp hle
  have hdim := (actionRatio_le_nat_iff m22OuterCocodeRepresentation hA 2).mp hsmall
  let : IsElementaryAbelian 2 A := hA.2
  have hcard := m22Outer_cocode_card_le_four A hq
  have hr : rank A ≤ 2 :=
    (Nat.log_mono_right hcard : Nat.log 2 (Nat.card A) ≤ Nat.log 2 4)
  by_cases hr2 : rank A = 2
  · have hb := rank_two_bound A hA hq hr2
    omega
  · have hr1 : rank A = 1 := by have := hA.rank_pos; omega
    obtain ⟨a, ha, ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
    have ho : orderOf a = 2 := orderOf_eq_prime
      (elemPow_eq_one_of_isElementaryAbelian a ha) ha1
    have hd := (m22Outer_involution_displacement_ge_three a ho).2
    have hf := Submodule.finrank_mono
      (fixedSpace_antitone m22OuterCocodeRepresentation (Subgroup.zpowers_le.mpr ha))
    have hdimA := fixedCodim_add_finrank m22OuterCocodeRepresentation A
    have hdima := fixedCodim_add_finrank m22OuterCocodeRepresentation (Subgroup.zpowers a)
    omega
end
end MathieuCode.QuadraticActors.StrictM22Cocode
