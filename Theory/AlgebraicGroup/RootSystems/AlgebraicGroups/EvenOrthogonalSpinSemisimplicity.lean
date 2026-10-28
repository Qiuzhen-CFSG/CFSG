module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalOmegaSemisimple
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenOrthogonalSpinCarrier
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.EvenSpinIsogeny
public import Theory.AlgebraicGroup.Semisimple.IsogenySource
public import Theory.AlgebraicGroup.Morphism.Connected
public import Theory.AlgebraicGroup.ClosedSubgroup.Connected
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Algebra.Group.Commute.Basic
import Mathlib.Tactic

/-!
# Semisimplicity of the split even Spin carrier

For a hyperbolic split quadratic form of rank at least four, this module proves
connectedness of the explicit left-regular Spin carrier and then lifts direct
Omega semisimplicity through the characteristic-free Spin-to-Omega isogeny.
The connectedness certificate is proved without type-D classification: the
isogeny image is connected, kernel points are scalar elements with square one,
and three pairwise orthogonal norm-minus-one vectors produce the scalar `-1`
as an explicit Spin commutator.  The argument therefore also covers
characteristic two, where the two scalar roots coincide.
-/

namespace Theory.AlgebraicGroup

open _root_.Theory.AlgebraicGroup.CliffordAlgebra
open scoped commutatorElement

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.style.haveILetI false

universe u
variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

private noncomputable def testVector
    (s : SplitQuadraticForm Q) (a : Fin s.rank) : V :=
  s.isometry.symm (Pi.single a 1, -Pi.single a 1)

private lemma testVector_norm
    (s : SplitQuadraticForm Q) (a : Fin s.rank) :
    Q (testVector s a) = -1 := by
  classical
  rw [testVector, ← s.isometry.map_app]
  simp
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [Pi.single_apply, hba]
  · simp

private lemma testVector_ortho
    (s : SplitQuadraticForm Q) {a b : Fin s.rank} (hab : a ≠ b) :
    QuadraticMap.IsOrtho Q (testVector s a) (testVector s b) := by
  rw [QuadraticMap.IsOrtho]
  simp only [testVector]
  let A : (Fin s.rank → k) × (Fin s.rank → k) :=
    (Pi.single a 1, -Pi.single a 1)
  let B : (Fin s.rank → k) × (Fin s.rank → k) :=
    (Pi.single b 1, -Pi.single b 1)
  have hsum : s.isometry.symm A + s.isometry.symm B =
      s.isometry.symm (A + B) :=
    (s.isometry.symm.toLinearEquiv.map_add A B).symm
  have hq (Z : (Fin s.rank → k) × (Fin s.rank → k)) :
      Q (s.isometry.symm Z) = hyperbolicForm s.rank Z := by
    rw [← s.isometry.map_app]
    simp
  change Q (s.isometry.symm A + s.isometry.symm B) =
    Q (s.isometry.symm A) + Q (s.isometry.symm B)
  rw [hsum, hq, hq, hq]
  classical
  simp [hyperbolicForm_apply, A, B, Finset.sum_add_distrib,
    mul_add, add_mul, Pi.single_apply, hab, Ne.symm hab]

private noncomputable def testUnit
    (s : SplitQuadraticForm Q) (a : Fin s.rank) : (CliffordAlgebra Q)ˣ where
  val := CliffordAlgebra.ι Q (testVector s a)
  inv := -CliffordAlgebra.ι Q (testVector s a)
  val_inv := by simp [CliffordAlgebra.ι_sq_scalar, testVector_norm]
  inv_val := by simp [CliffordAlgebra.ι_sq_scalar, testVector_norm]

private lemma testUnit_val
    (s : SplitQuadraticForm Q) (a : Fin s.rank) :
    (testUnit s a : CliffordAlgebra Q) = CliffordAlgebra.ι Q (testVector s a) := rfl

private lemma testUnit_mem_spin
    (s : SplitQuadraticForm Q) (a b : Fin s.rank) :
    ((testUnit s a) * (testUnit s b) : CliffordAlgebra Q) ∈ spinGroup Q := by
  rw [spinGroup.mem_iff]
  refine ⟨?_, ?_⟩
  · rw [pinGroup.mem_iff]
    refine ⟨?_, ?_⟩
    · refine ⟨testUnit s a * testUnit s b, ?_, rfl⟩
      exact mul_mem
        (Subgroup.subset_closure ⟨testVector s a, testUnit_val s a⟩)
        (Subgroup.subset_closure ⟨testVector s b, testUnit_val s b⟩)
    · exact mul_mem
        (by constructor <;> simp [testUnit, testVector_norm])
        (by constructor <;> simp [testUnit, testVector_norm])
  · exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero Q
      (testVector s a) (testVector s b)

private lemma testUnit_sq
    (s : SplitQuadraticForm Q) (a : Fin s.rank) :
    (testUnit s a : CliffordAlgebra Q) * testUnit s a = -1 := by
  simp [testUnit, CliffordAlgebra.ι_sq_scalar, testVector_norm]

private lemma testUnit_anti
    (s : SplitQuadraticForm Q) {a b : Fin s.rank} (hab : a ≠ b) :
    (testUnit s a : CliffordAlgebra Q) * testUnit s b =
      -((testUnit s b : CliffordAlgebra Q) * testUnit s a) := by
  simp only [testUnit_val, neg_mul]
  rw [CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (testVector_ortho s hab)]

private noncomputable def pairSpin
    (s : SplitQuadraticForm Q) (a b : Fin s.rank) : spinGroup Q :=
  ⟨(testUnit s a * testUnit s b : CliffordAlgebra Q), testUnit_mem_spin s a b⟩

private lemma pairSpin_val
    (s : SplitQuadraticForm Q) (a b : Fin s.rank) :
    (pairSpin s a b : CliffordAlgebra Q) =
      (testUnit s a : CliffordAlgebra Q) * testUnit s b := rfl

private lemma pairSpin_sq
    (s : SplitQuadraticForm Q) {a b : Fin s.rank} (hab : a ≠ b) :
    (pairSpin s a b : CliffordAlgebra Q) * pairSpin s a b = -1 := by
  rw [pairSpin_val]
  have hba : (testUnit s b : CliffordAlgebra Q) * testUnit s a =
      -((testUnit s a : CliffordAlgebra Q) * testUnit s b) := by
    have h := congrArg Neg.neg (testUnit_anti s hab)
    simpa only [neg_neg] using h.symm
  calc
    (testUnit s a : CliffordAlgebra Q) * testUnit s b *
        (testUnit s a * testUnit s b) =
      (testUnit s a) * (testUnit s b * testUnit s a) * testUnit s b := by
        simp [mul_assoc]
    _ = (testUnit s a) * (-(testUnit s a * testUnit s b)) * testUnit s b := by
      rw [hba]
    _ = -1 := by
      calc
        (testUnit s a : CliffordAlgebra Q) *
            (-(testUnit s a * testUnit s b)) * testUnit s b =
          -((testUnit s a * testUnit s a) *
            (testUnit s b * testUnit s b)) := by noncomm_ring
        _ = -1 := by simp [testUnit_sq]

private lemma spin_inv_val_of_sq_neg (x : spinGroup Q)
    (hx : (x : CliffordAlgebra Q) * x = -1) :
    ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) = -(x : CliffordAlgebra Q) := by
  have hu := (spinGroup.toUnits x).val_inv
  have hxi : (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) =
      -(x : CliffordAlgebra Q) := by
    change (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) = _
    have hmul :
        (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) *
            (x : CliffordAlgebra Q) = 1 :=
      (spinGroup.toUnits x).inv_val
    calc
      (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) =
          (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) * 1 := by simp
      _ = (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) *
          (-((x : CliffordAlgebra Q) * x)) := by rw [hx]; simp
      _ = -((↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) * x) *
          (x : CliffordAlgebra Q) := by noncomm_ring
      _ = -(x : CliffordAlgebra Q) := by rw [hmul]; simp
  change ((spinGroup.toUnits x⁻¹ : CliffordAlgebra Q)) = _
  rw [spinGroup.toUnits.map_inv]
  exact hxi

private lemma pairSpin_commutator_three
    (s : SplitQuadraticForm Q) {a b c : Fin s.rank}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ⁅pairSpin s a b, pairSpin s b c⁆ = pairSpin s a a := by
  let x := pairSpin s a b
  let y := pairSpin s b c
  have hba : (testUnit s b : CliffordAlgebra Q) * testUnit s a =
      -((testUnit s a : CliffordAlgebra Q) * testUnit s b) := by
    have h := congrArg Neg.neg (testUnit_anti s hab)
    simpa only [neg_neg] using h.symm
  have hca : (testUnit s c : CliffordAlgebra Q) * testUnit s a =
      -((testUnit s a : CliffordAlgebra Q) * testUnit s c) := by
    have h := congrArg Neg.neg (testUnit_anti s hac)
    simpa only [neg_neg] using h.symm
  have hcb : (testUnit s c : CliffordAlgebra Q) * testUnit s b =
      -((testUnit s b : CliffordAlgebra Q) * testUnit s c) := by
    have h := congrArg Neg.neg (testUnit_anti s hbc)
    simpa only [neg_neg] using h.symm
  have hx2 : (x : CliffordAlgebra Q) * x = -1 := by
    exact pairSpin_sq s hab
  have hy2 : (y : CliffordAlgebra Q) * y = -1 := by
    exact pairSpin_sq s hbc
  have hxy : (x : CliffordAlgebra Q) * y =
      -((y : CliffordAlgebra Q) * x) := by
    change ((testUnit s a : CliffordAlgebra Q) * testUnit s b) *
      (testUnit s b * testUnit s c) =
      -((testUnit s b * testUnit s c) *
        (testUnit s a * testUnit s b))
    have hleft :
        ((testUnit s a : CliffordAlgebra Q) * testUnit s b) *
            (testUnit s b * testUnit s c) =
          -((testUnit s a : CliffordAlgebra Q) * testUnit s c) := by
      calc
        ((testUnit s a : CliffordAlgebra Q) * testUnit s b) *
            (testUnit s b * testUnit s c) =
          (testUnit s a) * ((testUnit s b * testUnit s b) * testUnit s c) := by
            simp [mul_assoc]
        _ = -((testUnit s a : CliffordAlgebra Q) * testUnit s c) := by
          rw [testUnit_sq]
          simp
    have hright :
        ((testUnit s b : CliffordAlgebra Q) * testUnit s c) *
            (testUnit s a * testUnit s b) =
          (testUnit s a : CliffordAlgebra Q) * testUnit s c := by
      calc
        ((testUnit s b : CliffordAlgebra Q) * testUnit s c) *
            (testUnit s a * testUnit s b) =
          (testUnit s b) * ((testUnit s c * testUnit s a) * testUnit s b) := by
            simp [mul_assoc]
        _ = (testUnit s b) * (-(testUnit s a * testUnit s c) * testUnit s b) := by
          rw [hca]
        _ = -((testUnit s b * testUnit s a) *
            (testUnit s c * testUnit s b)) := by noncomm_ring
        _ = -((-((testUnit s a : CliffordAlgebra Q) * testUnit s b)) *
            (-((testUnit s b : CliffordAlgebra Q) * testUnit s c))) := by
          rw [hba, hcb]
        _ = (testUnit s a : CliffordAlgebra Q) * testUnit s c := by
          simp [neg_mul, mul_neg, hleft]
    rw [hleft, hright]
  apply Subtype.ext
  change (x : CliffordAlgebra Q) * (y : CliffordAlgebra Q) *
      ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) *
      ((y⁻¹ : spinGroup Q) : CliffordAlgebra Q) =
    (pairSpin s a a : CliffordAlgebra Q)
  rw [spin_inv_val_of_sq_neg x hx2, spin_inv_val_of_sq_neg y hy2]
  change (x : CliffordAlgebra Q) * y * (-(x : CliffordAlgebra Q)) *
      (-(y : CliffordAlgebra Q)) =
    (pairSpin s a a : CliffordAlgebra Q)
  rw [pairSpin_val]
  have hyx : (y : CliffordAlgebra Q) * x =
      -((x : CliffordAlgebra Q) * y) := by
    have h := congrArg Neg.neg hxy
    simpa only [neg_neg] using h.symm
  calc
    (x : CliffordAlgebra Q) * y * (-x) * (-y) =
        -((x : CliffordAlgebra Q) * x) * ((y : CliffordAlgebra Q) * y) := by
      calc
        (x : CliffordAlgebra Q) * y * (-x) * (-y) =
            (x : CliffordAlgebra Q) * y * x * y := by noncomm_ring
        _ = (x : CliffordAlgebra Q) * (y * x) * y := by simp [mul_assoc]
        _ = (x : CliffordAlgebra Q) * (-(x * y)) * y := by rw [hyx]
        _ = -((x : CliffordAlgebra Q) * x) * (y * y) := by noncomm_ring
    _ = -1 := by rw [hx2, hy2]; simp
    _ = (testUnit s a : CliffordAlgebra Q) * testUnit s a := by
      rw [testUnit_sq]

private theorem cover_identity_surj (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    let S := splitSpinClosedSubgroup s
    let I := evenSpinActionImageClosedSubgroup Q s
    letI := S.carrierAlgebraicGroup
    letI := I.carrierAlgebraicGroup
    ∀ y : Variety.Point I.carrierVariety, ∃ x : Variety.Point S.carrierVariety,
      x ∈ identityComponentSubgroup S.carrierVariety ∧
        (evenSpinActionImageCover Q s).onPoints x = y := by
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let φ := evenSpinActionImageCover Q s
  change ∀ y : Variety.Point I.carrierVariety, ∃ x : Variety.Point S.carrierVariety,
      x ∈ identityComponentSubgroup S.carrierVariety ∧ φ.onPoints x = y
  let R : ClosedSubgroup I.carrierVariety := ClosedSubgroup.top
  have hR : IsConnected (R : Set (Variety.Point I.carrierVariety)) := by
    change IsConnected (Set.univ : Set (Variety.Point I.carrierVariety))
    exact evenSpinActionImageClosedSubgroup_isConnected s hrank
  have hRvar : Variety.IsConnected R.carrierVariety := by
    let e := Variety.closedSubvarietyPointHomeomorph R.isZariskiClosed
    let : ConnectedSpace {x : Variety.Point I.carrierVariety // x ∈ (R : Set (Variety.Point I.carrierVariety))} :=
      Subtype.connectedSpace hR
    let : ConnectedSpace (Variety.Point R.carrierVariety) := e.connectedSpace_iff.mpr inferInstance
    exact connectedSpace_iff_univ.mp inferInstance
  have hsurj : Function.Surjective φ.onPoints := evenSpinActionImageCover_surjective Q s
  intro y
  let yR : Variety.Point R.carrierVariety := R.pointEquiv.symm ⟨y, by trivial⟩
  letI : AlgebraicGroup R.carrierVariety := R.carrierAlgebraicGroup
  let P := φ.closedSubgroupPreimage R
  letI : AlgebraicGroup P.carrierVariety := P.carrierAlgebraicGroup
  let P0 := identityComponentClosedSubgroup P.carrierVariety
  letI : AlgebraicGroup P0.carrierVariety := P0.carrierAlgebraicGroup
  have hPsurj := φ.preimageRestriction_identityComponent_surjective hsurj R hRvar
  obtain ⟨z, hz⟩ := hPsurj yR
  let xP : Variety.Point P.carrierVariety := P0.inclusion.onPoints z
  let x : Variety.Point S.carrierVariety := P.inclusion.onPoints xP
  let K : ClosedSubgroup S.carrierVariety :=
    (P.inclusion.comp P0.inclusion).imageClosedSubgroup
  have hKconn : IsConnected (K : Set (Variety.Point S.carrierVariety)) := by
    exact (P.inclusion.comp P0.inclusion).imageClosedSubgroup_isConnected
      (identityComponentClosedSubgroup_carrier_isConnected P.carrierVariety)
  have hxK : x ∈ K.toSubgroup := by
    change x ∈ (P.inclusion.comp P0.inclusion).image
    exact ⟨z, rfl⟩
  have hxPtop : K ≤ (ClosedSubgroup.top : ClosedSubgroup S.carrierVariety).identityComponentAmbient := by
    apply connected_closedSubgroup_le_identityComponentAmbient K
      (ClosedSubgroup.top : ClosedSubgroup S.carrierVariety) hKconn
    exact fun _ _ => trivial
  have hxcomp : x ∈ identityComponentSubgroup S.carrierVariety := by
    have hx := hxPtop hxK
    let T : ClosedSubgroup S.carrierVariety := ClosedSubgroup.top
    letI : AlgebraicGroup T.carrierVariety := T.carrierAlgebraicGroup
    obtain ⟨y0, hy0, hyx⟩ :=
      (ClosedSubgroup.mem_identityComponentAmbient_iff T x).mp hx
    rw [← hyx]
    change T.inclusion.onPoints y0 ∈ identityComponent S.carrierVariety
    exact closedSubgroup_inclusion_identityComponent_subset T ⟨y0, hy0, rfl⟩
  refine ⟨x, hxcomp, ?_⟩
  change φ.onPoints (P.inclusion.onPoints xP) = y
  have hz' := congrArg R.inclusion.onPoints hz
  change φ.onPoints (P.inclusion.onPoints (P0.inclusion.onPoints z)) =
    R.inclusion.onPoints yR at hz'
  have hyR : R.inclusion.onPoints yR = y := by
    change (R.pointEquiv yR).val = y
    dsimp only [yR]
    rw [R.pointEquiv.apply_symm_apply]
  exact hz'.trans hyR

private theorem cover_kernel_scalar
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (z : (evenSpinActionImageCover Q s).kernel) :
    ∃ a : k,
      (splitSpinClosedSubgroupPoints s z.1 : CliffordAlgebra Q) =
        algebraMap k (CliffordAlgebra Q) a ∧ a * a = 1 := by
  let x := splitSpinClosedSubgroupPoints s z.1
  have hz0 : (evenSpinActionImageCover Q s).onPoints z.1 = 1 :=
    MonoidHom.mem_ker.mp z.2
  have hpoints := evenSpinActionImageCover_spin_points Q s hrank x
  have hxpoint : (splitSpinClosedSubgroupPoints s).symm x = z.1 := by
    exact (splitSpinClosedSubgroupPoints s).symm_apply_apply z.1
  rw [hxpoint, hz0, map_one] at hpoints
  have hact : cliffordSpinActionOfSplit Q s x = 1 := by
    apply Subtype.ext
    exact congrArg Subtype.val hpoints.symm
  have hscalar : ∃ a : k, (x : CliffordAlgebra Q) =
      algebraMap k (CliffordAlgebra Q) a := by
    apply CliffordAlgebra.eq_algebraMap_of_mem_even_of_commute_ι s
      (x : CliffordAlgebra Q) (spinGroup.mem_even x.property)
    intro v
    have hs := cliffordSpinActionOfSplit_spec_inv Q s x v
    rw [hact] at hs
    have hconj : CliffordAlgebra.ι Q v =
        (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q v * (x⁻¹ : spinGroup Q) := by
      simpa using hs
    have hmul := congrArg
      (fun y : CliffordAlgebra Q => y * (x : CliffordAlgebra Q)) hconj
    have hmul' : CliffordAlgebra.ι Q v * (x : CliffordAlgebra Q) =
        (x : CliffordAlgebra Q) *
          (CliffordAlgebra.ι Q v * ((x⁻¹ : spinGroup Q) * x)) := by
      simpa only [mul_assoc] using hmul
    have hinv : ((x⁻¹ : spinGroup Q) : CliffordAlgebra Q) * x = 1 := by
      change (↑((spinGroup.toUnits x)⁻¹) : CliffordAlgebra Q) *
        (x : CliffordAlgebra Q) = 1
      exact (spinGroup.toUnits x).inv_val
    rw [hinv, mul_one] at hmul'
    exact hmul'.symm
  obtain ⟨a, ha⟩ := hscalar
  have ha2 : a * a = 1 := by
    let e := CliffordAlgebra.changeFormEquiv s.bilinear_toQuadraticMap
    let _ : Nontrivial (CliffordAlgebra Q) := e.symm.injective.nontrivial
    apply (FaithfulSMul.algebraMap_injective k (CliffordAlgebra Q))
    have hnorm := spinGroup.star_mul_self_of_mem x.property
    rw [ha] at hnorm
    simpa [CliffordAlgebra.star_algebraMap] using hnorm
  exact ⟨a, ha, ha2⟩

private theorem cover_kernel_central
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (z : (evenSpinActionImageCover Q s).kernel)
    (w : Variety.Point (splitSpinClosedSubgroup s).carrierVariety) :
    z.1 * w = w * z.1 := by
  let x := splitSpinClosedSubgroupPoints s z.1
  let y := splitSpinClosedSubgroupPoints s w
  obtain ⟨a, ha, _⟩ := cover_kernel_scalar s hrank z
  apply (splitSpinClosedSubgroupPoints s).injective
  rw [map_mul, map_mul]
  have hxy : x * y = y * x := by
    apply spinGroup.toUnits_injective
    apply Units.ext
    change (splitSpinClosedSubgroupPoints s z.1 : CliffordAlgebra Q) *
      (splitSpinClosedSubgroupPoints s w : CliffordAlgebra Q) =
      (splitSpinClosedSubgroupPoints s w : CliffordAlgebra Q) *
        (splitSpinClosedSubgroupPoints s z.1 : CliffordAlgebra Q)
    rw [ha]
    exact (Algebra.commutes a
      (splitSpinClosedSubgroupPoints s w : CliffordAlgebra Q))
  simpa [x, y] using hxy

private theorem source_commutator_mem_identity
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank)
    (g h : Variety.Point (splitSpinClosedSubgroup s).carrierVariety) :
    ⁅g, h⁆ ∈ identityComponentSubgroup
      (splitSpinClosedSubgroup s).carrierVariety := by
  let S := splitSpinClosedSubgroup s
  let I := evenSpinActionImageClosedSubgroup Q s
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  letI : AlgebraicGroup I.carrierVariety := I.carrierAlgebraicGroup
  let φ := evenSpinActionImageCover Q s
  obtain ⟨g0, hg0, hφg⟩ := cover_identity_surj s hrank (φ.onPoints g)
  obtain ⟨h0, hh0, hφh⟩ := cover_identity_surj s hrank (φ.onPoints h)
  let zg : φ.kernel := ⟨g * g0⁻¹, by
    apply MonoidHom.mem_ker.mpr
    simp [φ, hφg]⟩
  let zh : φ.kernel := ⟨h * h0⁻¹, by
    apply MonoidHom.mem_ker.mpr
    simp [φ, hφh]⟩
  have hgrel : zg.1 * g0 = g := by
    simp [zg]
  have hhrel : zh.1 * h0 = h := by
    simp [zh]
  have hzg : ∀ t : Variety.Point S.carrierVariety, zg.1 * t = t * zg.1 := by
    intro t
    exact cover_kernel_central s hrank zg t
  have hzh : ∀ t : Variety.Point S.carrierVariety, zh.1 * t = t * zh.1 := by
    intro t
    exact cover_kernel_central s hrank zh t
  have hcomm : ⁅g, h⁆ = ⁅g0, h0⁆ := by
    have hleft : ∀ (c a b : Variety.Point S.carrierVariety),
        c * a = a * c → c * b = b * c → ⁅c * a, b⁆ = ⁅a, b⁆ := by
      intro c a b hca hcb
      have hcaC : Commute c a := (commute_iff_eq c a).mpr hca
      have hcbC : Commute c b := (commute_iff_eq c b).mpr hcb
      have hcai : Commute c a⁻¹ := hcaC.inv_right
      have hcbi : Commute c b⁻¹ := hcbC.inv_right
      have hc_ab : Commute c (a * b) := hcaC.mul_right hcbC
      have hc_k : Commute c ⁅a, b⁆ := by
        rw [commutatorElement_def]
        exact ((hc_ab.mul_right hcai).mul_right hcbi)
      rw [commutatorElement_mul_left_eq_conj_mul]
      rw [hcbC.commutator_eq]
      simp only [mul_one]
      rw [hc_k.eq]
      simp
    have hright : ∀ (c a b : Variety.Point S.carrierVariety),
        c * a = a * c → c * b = b * c → ⁅a, c * b⁆ = ⁅a, b⁆ := by
      intro c a b hca hcb
      have hcaC : Commute c a := (commute_iff_eq c a).mpr hca
      have hcbC : Commute c b := (commute_iff_eq c b).mpr hcb
      have hacC : Commute a c := hcaC.symm
      have hcai : Commute c a⁻¹ := hcaC.inv_right
      have hcbi : Commute c b⁻¹ := hcbC.inv_right
      have hc_ab : Commute c (a * b) := hcaC.mul_right hcbC
      have hc_k : Commute c ⁅a, b⁆ := by
        rw [commutatorElement_def]
        exact ((hc_ab.mul_right hcai).mul_right hcbi)
      rw [commutatorElement_mul_right_eq_mul_conj]
      rw [hacC.commutator_eq]
      simp only [one_mul]
      rw [hc_k.eq]
      simp
    calc
      ⁅g, h⁆ = ⁅zg.1 * g0, zh.1 * h0⁆ := by rw [hgrel, hhrel]
      _ = ⁅g0, zh.1 * h0⁆ := hleft zg.1 g0 (zh.1 * h0) (hzg g0)
        (hzg (zh.1 * h0))
      _ = ⁅g0, h0⁆ := hright zh.1 g0 h0 (hzh g0) (hzh h0)
  rw [hcomm, commutatorElement_def]
  let H0 : Subgroup (Variety.Point S.carrierVariety) :=
    identityComponentSubgroup S.carrierVariety
  have hg0' : g0 ∈ H0 := hg0
  have hh0' : h0 ∈ H0 := hh0
  have hp : g0 * h0 ∈ H0 := H0.mul_mem hg0' hh0'
  have hpi : g0 * h0 * g0⁻¹ ∈ H0 := H0.mul_mem hp (H0.inv_mem hg0')
  exact H0.mul_mem hpi (H0.inv_mem hh0')

private theorem splitSpinClosedSubgroup_isConnected_core
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    _root_.IsConnected (Set.univ : Set
      (Variety.Point (splitSpinClosedSubgroup s).carrierVariety)) := by
  let S := splitSpinClosedSubgroup s
  letI : AlgebraicGroup S.carrierVariety := S.carrierAlgebraicGroup
  let a : Fin s.rank := ⟨0, by omega⟩
  let b : Fin s.rank := ⟨1, by omega⟩
  let c : Fin s.rank := ⟨2, by omega⟩
  have hab : a ≠ b := by simp [a, b]
  have hac : a ≠ c := by simp [a, c]
  have hbc : b ≠ c := by simp [b, c]
  let p : spinGroup Q → Variety.Point S.carrierVariety :=
    (splitSpinClosedSubgroupPoints s).symm
  let xa := p (pairSpin s a b)
  let xb := p (pairSpin s b c)
  let zn := p (pairSpin s a a)
  have hzn_comm : ⁅xa, xb⁆ = zn := by
    apply (splitSpinClosedSubgroupPoints s).injective
    rw [map_commutatorElement]
    simpa [xa, xb, zn, p] using pairSpin_commutator_three s hab hac hbc
  have hzn : zn ∈ identityComponentSubgroup S.carrierVariety := by
    rw [← hzn_comm]
    exact source_commutator_mem_identity s hrank xa xb
  have hzn_val : (splitSpinClosedSubgroupPoints s zn : CliffordAlgebra Q) = -1 := by
    simp [zn, p, pairSpin_val, testUnit_sq]
  have hId : identityComponent S.carrierVariety = Set.univ := by
    apply Set.eq_univ_of_forall
    intro g
    obtain ⟨g0, hg0, hφg⟩ :=
      cover_identity_surj s hrank ((evenSpinActionImageCover Q s).onPoints g)
    let φ := evenSpinActionImageCover Q s
    let z : φ.kernel := ⟨g * g0⁻¹, by
      apply MonoidHom.mem_ker.mpr
      simp [φ, hφg]⟩
    obtain ⟨r, hr, hr2⟩ := cover_kernel_scalar s hrank z
    have hrpm : (r - 1) * (r + 1) = 0 := by
      calc
        (r - 1) * (r + 1) = r * r - 1 := by ring
        _ = 0 := by rw [hr2]; simp
    rcases mul_eq_zero.mp hrpm with hrm | hrp
    · have hrone : r = 1 := sub_eq_zero.mp hrm
      have hz1 : z.1 = 1 := by
        apply (splitSpinClosedSubgroupPoints s).injective
        apply spinGroup.toUnits_injective
        apply Units.ext
        change (splitSpinClosedSubgroupPoints s z.1 : CliffordAlgebra Q) =
          (splitSpinClosedSubgroupPoints s 1 : CliffordAlgebra Q)
        rw [hr, hrone, map_one]
        simp
      have hz0 : z.1 ∈ identityComponentSubgroup S.carrierVariety := by
        rw [hz1]
        exact (identityComponentSubgroup S.carrierVariety).one_mem
      have hzg : z.1 * g0 = g := by simp [z]
      rw [← hzg]
      exact (identityComponentSubgroup S.carrierVariety).mul_mem hz0 hg0
    · have hrneg : r = -1 := eq_neg_of_add_eq_zero_left hrp
      have hzn_eq : z.1 = zn := by
        apply (splitSpinClosedSubgroupPoints s).injective
        apply spinGroup.toUnits_injective
        apply Units.ext
        change (splitSpinClosedSubgroupPoints s z.1 : CliffordAlgebra Q) =
          (splitSpinClosedSubgroupPoints s zn : CliffordAlgebra Q)
        rw [hr, hrneg, hzn_val]
        simp
      have hz0 : z.1 ∈ identityComponentSubgroup S.carrierVariety := by
        rw [hzn_eq]
        exact hzn
      have hzg : z.1 * g0 = g := by simp [z]
      rw [← hzg]
      exact (identityComponentSubgroup S.carrierVariety).mul_mem hz0 hg0
  exact (identityComponent_eq_univ_iff_isConnected S.carrierVariety).mp hId

/-- The split even Spin carrier is connected in hyperbolic rank at least four.
This is obtained directly from the connected Omega image and the explicit
scalar kernel calculation, including characteristic two. -/
public theorem splitSpinClosedSubgroup_isConnected
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    _root_.IsConnected (Set.univ : Set
      (Variety.Point (splitSpinClosedSubgroup s).carrierVariety)) :=
  splitSpinClosedSubgroup_isConnected_core s hrank

/-- Semisimplicity of the packaged split even Spin carrier in every
characteristic, obtained by lifting semisimplicity across its Spin-to-Omega
isogeny. -/
public theorem splitEvenOrthogonalSpinCarrier_isSemisimple
    (s : SplitQuadraticForm Q) (hrank : 4 ≤ s.rank) :
    IsSemisimpleAlgebraicGroup
      (splitEvenOrthogonalSpinCarrier s).spin.carrierVariety := by
  letI : AlgebraicGroup (splitSpinClosedSubgroup s).carrierVariety :=
    (splitSpinClosedSubgroup s).carrierAlgebraicGroup
  have hsource : IsSemisimpleAlgebraicGroup
      (splitSpinClosedSubgroup s).carrierVariety :=
    isogeny_source_semisimple (evenSpinActionImageCover Q s)
    (evenSpinActionImageCover_isIsogeny Q s)
    (splitSpinClosedSubgroup_isConnected s hrank)
    (evenSpinActionImageClosedSubgroup_isSemisimple s hrank)
  rw [splitEvenOrthogonalSpinCarrier_spin]
  exact hsource

end Theory.AlgebraicGroup
