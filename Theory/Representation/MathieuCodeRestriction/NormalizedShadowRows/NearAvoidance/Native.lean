module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.NearAvoidance.Data
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.OuterSpan.Native
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.OrbitStabilizers.Action
public import Theory.Representation.BinaryOffender.QuadraticRatioTransport
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Involutions

/-!
# Weight-two avoidance in fixed spaces of the native M22 cocode

Two distinct commuting involutions either move at least six dimensions,
or move at least five and fix an actual distinguished weight-two vector.
The checked minors imply that a five-space fixed by both must contain such
a vector. Sylow conjugacy gives the avoidance bound for every noncyclic
elementary actor of the full pair stabilizer. A near-offender is noncyclic,
since every involution moves at least three dimensions.

Source: Aschbacher--Smith H.15.2(3) and 8.1.2, pp.398--399,713.
-/
public noncomputable section
open Subgroup Representation Representation.BinaryOffender Matrix
open Sporadic.Mathieu MathieuCode MathieuCode.QuadraticActors
open MathieuCode.CocodeOctad.Involutions
open scoped IsMulCommutative
namespace MathieuCode.NormalizedShadowRows.NearAvoidance

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
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    Matrix.col_apply, LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply] using hh

private lemma pair_column (a b : m22PairStabilizer) (v w : Fin 72)
    (hv : outerNative v = a.val) (hw : outerNative w = b.val) (j : Fin 11) :
    (StrictM22Cocode.pairMatrix v w).col j =
      pairMap a b (m22PairLine.mkQ (sectionMap (Pi.single j 1))) := by
  ext i
  simp only [Matrix.col_apply, StrictM22Cocode.pairMatrix]
  change _ = quotientCoordinates
    (m22OuterCocodeRepresentation (if i.val < 11 then a else b)
      (m22PairLine.mkQ (sectionMap (Pi.single j 1))) -
        m22PairLine.mkQ (sectionMap (Pi.single j 1))) _
  rw [quotient_displacement]
  split_ifs <;> simp only [matrix_entry, hv, hw]

private lemma rank_bound (a b : m22PairStabilizer) (v w : Fin 72)
    (hv : outerNative v = a.val) (hw : outerNative w = b.val)
    (hv0 : v ≠ 0) (hvw : v < w) (hadj : OuterSpan.adjacent v w = true) :
    dimension v w ≤ Module.finrank (ZMod 2) (LinearMap.range (pairMap a b)) := by
  have hle : Submodule.span (ZMod 2) (Set.range (StrictM22Cocode.pairMatrix v w).col) ≤
      LinearMap.range (pairMap a b) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact ⟨_,(pair_column a b v w hv hw j).symm⟩
  have hm := Submodule.finrank_mono hle
  rw [←Matrix.rank_eq_finrank_span_cols] at hm
  have hs := Matrix.rank_submatrix_le (StrictM22Cocode.pairMatrix v w) (row v w) (col v w)
  have hi := Matrix.rank_mul_le_right (leftInverse v w) (minor v w)
  rw [(certified_pairs v w hv0 hvw hadj).1,Matrix.rank_one,Fintype.card_fin] at hi
  exact hi.trans (hs.trans hm)

private lemma mem_pair_kernel (a b : m22PairStabilizer) (x : M22Cocode)
    (ha : m22OuterCocodeRepresentation a x = x)
    (hb : m22OuterCocodeRepresentation b x = x) : x ∈ LinearMap.ker (pairMap a b) := by
  apply LinearMap.mem_ker.mpr
  ext i
  change quotientCoordinates
    (m22OuterCocodeRepresentation (if i.val < 11 then a else b) x - x) _ = 0
  split_ifs <;> simp only [ha,hb,sub_self,map_zero,Pi.zero_apply]

private theorem moving_coverage : ∀ c : Fin 24, c ≠ 0 → c ≠ 9 →
    ∃ i : Fin 22, m22Coordinates i = c := by decide +kernel

private lemma pair_avoiding_bound (a b : m22PairStabilizer) (v w : Fin 72)
    (hv : outerNative v = a.val) (hw : outerNative w = b.val)
    (hv0 : v ≠ 0) (hvw : v < w) (hadj : OuterSpan.adjacent v w = true)
    (I : Submodule (ZMod 2) M22Cocode)
    (ha : ∀ x ∈ I, m22OuterCocodeRepresentation a x = x)
    (hb : ∀ x ∈ I, m22OuterCocodeRepresentation b x = x)
    (havoid : Disjoint (I : Set M22Cocode) m22WeightTwoFamily) :
    Module.finrank (ZMod 2) I ≤ 4 := by
  have hI : I ≤ LinearMap.ker (pairMap a b) := fun x hx =>
    mem_pair_kernel a b x (ha x hx) (hb x hx)
  have hl := rank_bound a b v w hv hw hv0 hvw hadj
  have hk := (pairMap a b).finrank_range_add_finrank_ker
  rw [finrank_m22Cocode] at hk
  have hi := Submodule.finrank_mono hI
  by_contra! hlarge
  by_cases hp : point v w = 0
  · have hd : dimension v w = 6 := if_pos hp
    omega
  · have hd : dimension v w = 5 := if_neg hp
    have he : I = LinearMap.ker (pairMap a b) :=
      Submodule.eq_of_le_of_finrank_le hI (by omega)
    obtain ⟨hne,hvfix,hwfix⟩ := (certified_pairs v w hv0 hvw hadj).2 hp
    obtain ⟨i,hi⟩ := moving_coverage (point v w) hp hne
    have hfix (c : m22PairStabilizer) (t : Fin 72) (ht : outerNative t = c.val)
        (htf : outerPoint t (point v w) = point v w) :
        m22OuterCocodeRepresentation c (m22WeightTwoVector i) = m22WeightTwoVector i := by
      apply (m22WeightTwoVector_outer_fixed_iff c i).mpr
      change c.val.val (m22Coordinates i) = m22Coordinates i
      rw [hi,←ht,outerNative_apply,htf]
    have hx : m22WeightTwoVector i ∈ I := by
      rw [he]
      exact mem_pair_kernel a b _ (hfix a v hv hvfix) (hfix b w hw hwfix)
    exact Set.disjoint_left.mp havoid hx ⟨i,rfl⟩

private lemma outer_zero : outerNative 0 = (1 : M24) := by
  apply Subtype.ext
  apply Equiv.ext
  intro x
  rw [outerNative_apply]
  exact congrFun (by decide +kernel : outerPoint 0 = id) x

/-- A noncyclic elementary actor in the native Sylow has the full weight-two
avoidance bound on its literal cocode fixed space. -/
theorem sylow_avoiding_bound (A : Subgroup m22PairStabilizer) [IsElementaryAbelian 2 A]
    (hS : A ≤ M22ChapterH.CompatibleSylow.outerGroup) (hc : 2 < Nat.card A)
    (I : Submodule (ZMod 2) M22Cocode) (hI : I ≤ fixedSpace m22OuterCocodeRepresentation A)
    (ha : Disjoint (I : Set M22Cocode) m22WeightTwoFamily) :
    Module.finrank (ZMod 2) I ≤ 4 := by
  have hne : A ≠ ⊥ := by intro he; simp [he] at hc
  obtain ⟨a,haA,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hne
  have hao : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a haA) ha1
  obtain ⟨b,hbA,hb1,hba⟩ : ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
    by_contra hn
    push Not at hn
    have hle : A ≤ zpowers a := by
      intro b hb
      by_cases hb1 : b = 1
      · simpa only [hb1] using (zpowers a).one_mem
      · rw [hn b hb hb1]; exact mem_zpowers a
    have hh := card_le_of_le hle
    rw [Nat.card_zpowers,hao] at hh
    omega
  obtain ⟨v,hv⟩ := outer_vertex_of_square a (hS haA) (elemPow_eq_one_of_isElementaryAbelian a haA)
  obtain ⟨w,hw⟩ := outer_vertex_of_square b (hS hbA) (elemPow_eq_one_of_isElementaryAbelian b hbA)
  have hv0 : v ≠ 0 := by
    intro he; apply ha1; apply Subtype.ext; rw [he,outer_zero] at hv; exact hv.symm
  have hw0 : w ≠ 0 := by
    intro he; apply hb1; apply Subtype.ext; rw [he,outer_zero] at hw; exact hw.symm
  have hvw : v ≠ w := by
    intro he
    exact hba (Subtype.ext (hw.symm.trans (he ▸ hv)))
  have hcomm : Commute a b := congrArg Subtype.val (mul_comm (⟨a,haA⟩ : A) ⟨b,hbA⟩)
  rcases lt_or_gt_of_ne hvw with hlt | hlt
  · exact pair_avoiding_bound a b v w hv hw hv0 hlt
      (OuterSpan.native_adjacent v w hv hw hcomm) I
      (fun x hx => hI hx ⟨a,haA⟩) (fun x hx => hI hx ⟨b,hbA⟩) ha
  · exact pair_avoiding_bound b a w v hw hv hw0 hlt
      (OuterSpan.native_adjacent w v hw hv hcomm.symm) I
      (fun x hx => hI hx ⟨b,hbA⟩) (fun x hx => hI hx ⟨a,haA⟩) ha

/-- The avoidance bound holds for every noncyclic elementary subgroup of the
full original native pair stabilizer, including outer actors. -/
theorem noncyclic_avoiding_bound (A : Subgroup m22PairStabilizer) [IsElementaryAbelian 2 A]
    (hc : 2 < Nat.card A) (I : Submodule (ZMod 2) M22Cocode)
    (hI : I ≤ fixedSpace m22OuterCocodeRepresentation A)
    (ha : Disjoint (I : Set M22Cocode) m22WeightTwoFamily) :
    Module.finrank (ZMod 2) I ≤ 4 := by
  obtain ⟨S,hAS⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq m22PairStabilizer S M22ChapterH.CompatibleSylow.outer
  let f := (MulAut.conj g).toMonoidHom
  let E := LinearMap.GeneralLinearGroup.toLinearEquiv (m22OuterCocodeRepresentation.asGroupHom g)
  let B := A.map f
  let J := I.map E.toLinearMap
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f
  have hBS : B ≤ M22ChapterH.CompatibleSylow.outerGroup := by
    have hh := map_mono (f := f) hAS
    change B ≤ (g • S : Sylow 2 m22PairStabilizer) at hh
    rwa [hg] at hh
  have hBC : 2 < Nat.card B := by rwa [card_map_of_injective (MulAut.conj g).injective]
  have hJ : J ≤ fixedSpace m22OuterCocodeRepresentation B := by
    rintro x ⟨y,hy,rfl⟩ ⟨b,hb⟩
    obtain ⟨a,ha,rfl⟩ := hb
    change m22OuterCocodeRepresentation (g*a*g⁻¹)
      (m22OuterCocodeRepresentation g y) = m22OuterCocodeRepresentation g y
    rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right,map_mul,Module.End.mul_apply]
    exact congrArg (m22OuterCocodeRepresentation g) (hI hy ⟨a,ha⟩)
  have haJ : Disjoint (J : Set M22Cocode) m22WeightTwoFamily := by
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,rfl⟩ hx
    apply Set.disjoint_left.mp ha hy
    obtain ⟨i,hi⟩ := hx
    change m22WeightTwoVector i = E y at hi
    rw [m22WeightTwoFamily_outer_orbit i]
    refine ⟨g⁻¹,?_⟩
    rw [hi]
    change m22OuterCocodeRepresentation g⁻¹ (m22OuterCocodeRepresentation g y) = y
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,Module.End.one_apply]
  have hb := sylow_avoiding_bound B hBS hBC J hJ haJ
  rwa [LinearEquiv.finrank_map_eq] at hb

/-- The precise native H.15.2(3) input consumed by original 8.1.2. -/
theorem nearOffender_avoiding_bound (A : Subgroup m22PairStabilizer)
    (hA : IsElementaryTwo A) (hn : fixedCodim m22OuterCocodeRepresentation A ≤ rank A + 1)
    (I : Submodule (ZMod 2) M22Cocode) (hI : I ≤ fixedSpace m22OuterCocodeRepresentation A)
    (ha : Disjoint (I : Set M22Cocode) m22WeightTwoFamily) :
    Module.finrank (ZMod 2) I ≤ 4 := by
  let := hA.2
  obtain ⟨a,haA,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA.1
  have hao : orderOf a = 2 := orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian a haA) ha1
  have hd := (m22Outer_involution_displacement_ge_three a hao).2
  have hm := Submodule.finrank_mono
    (fixedSpace_antitone m22OuterCocodeRepresentation (zpowers_le.mpr haA))
  have hdA := fixedCodim_add_finrank m22OuterCocodeRepresentation A
  have hda := fixedCodim_add_finrank m22OuterCocodeRepresentation (zpowers a)
  have hr : 2 ≤ rank A := by omega
  apply noncyclic_avoiding_bound A _ I hI ha
  rw [hA.card_eq_two_pow_rank]
  exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) hr)
end MathieuCode.NormalizedShadowRows.NearAvoidance
